const http = require("http");
const fs = require("fs");
const path = require("path");
const { WebSocketServer } = require("ws");

const PORT = process.env.PORT || 8080;

/* ----------------------------- Defaults ------------------------------ */
const TICK_MS          = 33;
const COUNTDOWN_MS     = 5000;
const POSTGAME_MS      = 9000;

const BASE_SPEED       = 5.0;
const BOOST_SPEED      = 11.0;
const TURN_RATE        = 0.22;
const START_MASS        = 14;
const BOOST_MIN_MASS   = 9;
const BOOST_DRAIN      = 0.09;
const POINT_STEP       = 4.2;
const FOOD_TARGET      = 200;
const FOOD_MASS        = 1;
const SNAKE_BASE_R     = 7;
const BORDER_DRAIN     = 0.35;  // mass lost per tick while in the storm

const COLORS = [
  "#37e6c9", "#ff5da2", "#ffd23f", "#7c5cff",
  "#4ad66d", "#ff7849", "#43c6ff", "#ff4d6d",
];

const rand  = (a, b) => a + Math.random() * (b - a);
const dist2 = (ax, ay, bx, by) => { const dx=ax-bx, dy=ay-by; return dx*dx+dy*dy; };
function angleDelta(a, b) {
  let d = (b - a) % (Math.PI * 2);
  if (d > Math.PI) d -= Math.PI * 2;
  if (d < -Math.PI) d += Math.PI * 2;
  return d;
}

/* ====================================================================
 *  ROOM
 * ==================================================================== */
class Room {
  constructor(code) {
    this.code = code;
    this.players = new Map();
    this.food = [];
    this.state = "lobby";
    this.nextId = 1;
    this.winnerName = null;
    this.phaseUntil = 0;

    // Host-configurable settings (defaults)
    this.settings = {
      mapSize: 2200,       // world radius
      borderSpeed: 1.0,    // multiplier: 0.5=slow, 1=normal, 2=fast
      maxPlayers: 20,
      graceMs: 8000,
      shrinkMs: 90000,
      snakeSpeed: 1.0,     // multiplier for base speed
      boostSpeed: 1.0,     // multiplier for boost speed
      foodRate: 1.0,       // multiplier for food target count
    };

    // Border state
    this.borderR = this.settings.mapSize;
    this.borderCenterX = 0;
    this.borderCenterY = 0;
    this.borderPhase = "waiting"; // waiting | shrinking | moving | final
    this.roundStartAt = 0;
    this.moveStartAt = 0;
    this.moveAngle = 0;
    this.starterCount = 0;

    this.scatterFood(FOOD_TARGET);
    this.powerups = [];
    this.powerupTimer = 0;
    this.isPublic = false;
  }

  /* ---- player lifecycle ---- */
  addPlayer(ws, name, color, pattern) {
    if (this.players.size >= this.settings.maxPlayers) {
      ws.send(JSON.stringify({ t: "error", msg: "Room full" }));
      return null;
    }
    const id = this.nextId++;
    const isHost = this.isPublic ? false : this.players.size === 0;
    // Validate color: must be a valid hex color
    const validColor = /^#[0-9a-fA-F]{6}$/.test(color) ? color : COLORS[(id - 1) % COLORS.length];
    const validPattern = ["solid","striped","gradient"].includes(pattern) ? pattern : "solid";
    const p = {
      id, ws, name: (name || "snake").slice(0, 14), isHost,
      color: validColor, pattern: validPattern,
      alive: false, points: [], heading: 0, targetAngle: 0,
      boost: false, mass: START_MASS, _stepAcc: 0, _curSpeed: BASE_SPEED, _stormTicks: 0,
    };
    this.players.set(id, p);
    this.send(p, { t: "welcome", id, room: this.code, isHost, settings: this.settings, isPublic: this.isPublic });
    this.broadcastLobby();

    // Auto-start public rooms when 2+ players join (10 second countdown)
    if (this.isPublic && this.state === "lobby" && this.players.size >= 2) {
      if (!this._autoStartTimer) {
        this._autoStartTimer = setTimeout(() => {
          this._autoStartTimer = null;
          if (this.state === "lobby" && this.players.size >= 2) this.startCountdown();
        }, 10000);
        this.broadcast({ t: "autostart", seconds: 10 });
      }
    }
    return p;
  }

  removePlayer(id) {
    const p = this.players.get(id);
    if (!p) return;
    this.players.delete(id);
    if (p.isHost) {
      const next = this.players.values().next().value;
      if (next) next.isHost = true;
    }
    if (this.state === "playing") this.checkWin();
    this.broadcastLobby();
  }

  updateSettings(s) {
    if (typeof s.mapSize === "number") this.settings.mapSize = Math.max(800, Math.min(5000, s.mapSize));
    if (typeof s.borderSpeed === "number") this.settings.borderSpeed = Math.max(0.25, Math.min(4, s.borderSpeed));
    if (typeof s.maxPlayers === "number") this.settings.maxPlayers = Math.max(2, Math.min(50, s.maxPlayers));
    if (typeof s.graceMs === "number") this.settings.graceMs = Math.max(0, Math.min(60000, s.graceMs));
    if (typeof s.shrinkMs === "number") this.settings.shrinkMs = Math.max(10000, Math.min(300000, s.shrinkMs));
    if (typeof s.snakeSpeed === "number") this.settings.snakeSpeed = Math.max(0.5, Math.min(3, s.snakeSpeed));
    if (typeof s.boostSpeed === "number") this.settings.boostSpeed = Math.max(0.5, Math.min(4, s.boostSpeed));
    if (typeof s.foodRate === "number") this.settings.foodRate = Math.max(0.25, Math.min(5, s.foodRate));
    this.broadcastLobby();
  }

  /* ---- snake spawning (avoids other snakes) ---- */
  spawnSnake(p) {
    let hx, hy, safe;
    for (let attempt = 0; attempt < 30; attempt++) {
      const r = rand(120, this.borderR * 0.55);
      const a = rand(0, Math.PI * 2);
      hx = Math.cos(a) * r;
      hy = Math.sin(a) * r;
      safe = true;
      for (const q of this.players.values()) {
        if (q === p || !q.alive || q.points.length === 0) continue;
        const qh = q.points[0];
        if (dist2(hx, hy, qh.x, qh.y) < 10000) { safe = false; break; }
      }
      if (safe) break;
    }
    p.heading = Math.atan2(-hy, -hx);
    p.targetAngle = p.heading;
    p.mass = START_MASS;
    p.boost = false;
    p.alive = true;
    p._stepAcc = 0;
    p._curSpeed = BASE_SPEED;
    p._stormTicks = 0;
    p._boostTicks = 0;
    p.powerups = [];        // array of {type, until}
    p.points = [];
    for (let i = 0; i < 12; i++) {
      p.points.push({
        x: hx - Math.cos(p.heading) * i * POINT_STEP,
        y: hy - Math.sin(p.heading) * i * POINT_STEP,
      });
    }
  }

  hasPowerup(p, type) { return p.powerups.some(pu => pu.type === type); }

  snakeRadius(p) {
    let r = SNAKE_BASE_R + Math.min(p.mass * 0.05, 13);
    if (this.hasPowerup(p, "jumbo")) r *= 1.8;
    return r;
  }
  targetLen(p) {
    // Length caps at mass 80 — after that you just get fatter
    const effectiveMass = Math.min(p.mass, 80);
    return 70 + effectiveMass * 4.0;
  }

  /* ---- food ---- */
  scatterFood(n) {
    for (let i = 0; i < n; i++) this.food.push(this.randFoodPos());
  }
  randFoodPos() {
    const r = Math.sqrt(Math.random()) * (this.settings.mapSize * 0.97);
    const a = rand(0, Math.PI * 2);
    return { x: Math.cos(a) * r, y: Math.sin(a) * r };
  }
  randFoodInBorder() {
    const safeR = Math.max(20, this.borderR * 0.92);
    const r = Math.sqrt(Math.random()) * safeR;
    const a = rand(0, Math.PI * 2);
    return { x: this.borderCenterX + Math.cos(a) * r, y: this.borderCenterY + Math.sin(a) * r };
  }

  /* ---- round flow ---- */
  startCountdown() {
    if (this.state !== "lobby" && this.state !== "postgame") return;
    if (this.players.size < 2) return;

    // Public rooms: auto-configure settings based on player count
    if (this.isPublic) {
      const n = this.players.size;
      if (n <= 4) this.settings.mapSize = 1400;
      else if (n <= 8) this.settings.mapSize = 2000;
      else if (n <= 15) this.settings.mapSize = 2800;
      else this.settings.mapSize = 3500;
      this.settings.snakeSpeed = 1.0;
      this.settings.boostSpeed = 1.5; // strong
      this.settings.borderSpeed = 1.0;
      this.settings.foodRate = 1.0;
    }

    this.state = "countdown";
    this.borderR = this.settings.mapSize;
    this.borderCenterX = 0;
    this.borderCenterY = 0;
    this.borderPhase = "waiting";
    this.winnerName = null;
    this.food = [];
    this.scatterFood(FOOD_TARGET);
    for (const p of this.players.values()) this.spawnSnake(p);
    this.phaseUntil = Date.now() + COUNTDOWN_MS;
    this.broadcast({ t: "roundstart", countdownMs: COUNTDOWN_MS, settings: this.settings });
    this.broadcastLobby();
  }

  beginPlay() {
    this.state = "playing";
    this.roundStartAt = Date.now();
    this.starterCount = [...this.players.values()].filter(p => p.alive).length;
  }

  checkWin() {
    const alive = [...this.players.values()].filter(p => p.alive);
    if (alive.length <= 1 && this.starterCount >= 1) {
      this.state = "postgame";
      this.winnerName = alive.length === 1 ? alive[0].name : null;
      this.phaseUntil = Date.now() + POSTGAME_MS;
      this.broadcast({
        t: "roundover",
        winner: this.winnerName,
        winnerId: alive.length === 1 ? alive[0].id : null,
      });
      this.broadcastLobby();
    }
  }

  killSnake(p, reason) {
    if (!p.alive) return;
    p.alive = false;
    const drops = Math.min(60, Math.floor(p.mass));
    for (let i = 0; i < drops; i++) {
      const pt = p.points[Math.floor(rand(0, p.points.length))];
      if (pt) this.food.push({ x: pt.x + rand(-8, 8), y: pt.y + rand(-8, 8) });
    }
    p.points = [];
    this.send(p, { t: "died", reason });
    if (this.state === "playing") this.checkWin();
  }

  /* ---- the simulation tick ---- */
  step() {
    const now = Date.now();

    if (this.state === "countdown" && now >= this.phaseUntil) this.beginPlay();
    if (this.state === "postgame" && now >= this.phaseUntil) {
      if (this.isPublic) {
        // Public rooms: kick everyone back and close the room
        this.broadcast({ t: "roundover", winner: null, winnerId: null, ended: true });
        for (const p of this.players.values()) {
          if (p.ws.readyState === 1) p.ws.close(1000, "Game over");
        }
        this.players.clear();
        this.state = "lobby"; // will get cleaned up by room GC
      } else {
        this.state = "lobby";
        this.broadcastLobby();
      }
    }
    if (this.state !== "playing") return;

    const elapsed = now - this.roundStartAt;
    const spd = this.settings.borderSpeed;
    const graceMs = this.settings.graceMs / spd;
    const shrinkMs = this.settings.shrinkMs / spd;
    const minR = 120;
    const moveMs = 30000 / spd;   // how long it moves around
    const finalMs = 20000 / spd;  // how long final shrink takes

    /* 1. Border phases */
    if (this.borderPhase === "waiting") {
      if (elapsed > graceMs) this.borderPhase = "shrinking";
    }

    if (this.borderPhase === "shrinking") {
      const shrinkElapsed = elapsed - graceMs;
      const k = Math.min(1, shrinkElapsed / shrinkMs);
      this.borderR = this.settings.mapSize - (this.settings.mapSize - minR) * k;
      if (k >= 1) {
        this.borderPhase = "moving";
        this.moveStartAt = now;
        this.moveAngle = rand(0, Math.PI * 2);
      }
    }

    if (this.borderPhase === "moving") {
      const moveElapsed = now - this.moveStartAt;
      // Circle moves around the map center in a slow arc
      const moveSpeed = 1.2 * spd;
      this.moveAngle += 0.008 * spd;
      this.borderCenterX += Math.cos(this.moveAngle) * moveSpeed;
      this.borderCenterY += Math.sin(this.moveAngle) * moveSpeed;
      // Keep center within bounds
      const maxDrift = this.settings.mapSize * 0.4;
      const cd = Math.hypot(this.borderCenterX, this.borderCenterY);
      if (cd > maxDrift) {
        this.borderCenterX *= maxDrift / cd;
        this.borderCenterY *= maxDrift / cd;
        this.moveAngle += Math.PI * 0.3; // redirect
      }
      this.borderR = minR;
      if (moveElapsed > moveMs) {
        this.borderPhase = "final";
        this.moveStartAt = now;
      }
    }

    if (this.borderPhase === "final") {
      const finalElapsed = now - this.moveStartAt;
      const k = Math.min(1, finalElapsed / finalMs);
      this.borderR = minR * (1 - k);
      if (this.borderR < 5) this.borderR = 5;
    }

    /* 1b. Spawn power-ups periodically */
    this.powerupTimer++;
    if (this.powerupTimer >= 300 && this.powerups.length < 5) { // every ~10 seconds
      this.powerupTimer = 0;
      const types = ["jumbo", "magnet", "boostme", "invincible"];
      const type = types[Math.floor(Math.random() * types.length)];
      const pos = this.randFoodInBorder();
      this.powerups.push({ x: pos.x, y: pos.y, type });
    }

    /* 2. Move every alive snake. */
    for (const p of this.players.values()) {
      if (!p.alive) continue;

      // Expire power-ups
      p.powerups = p.powerups.filter(pu => now < pu.until);

      const d = angleDelta(p.heading, p.targetAngle);
      // Bigger snakes turn slower — ranges from 0.22 (small) to 0.08 (huge)
      const turnRate = Math.max(0.08, TURN_RATE - p.mass * 0.0012);
      p.heading += Math.max(-turnRate, Math.min(turnRate, d));

      let targetSpeed = BASE_SPEED * this.settings.snakeSpeed;
      if (p.boost && p.mass > BOOST_MIN_MASS) {
        targetSpeed = BOOST_SPEED * this.settings.boostSpeed;
        p._boostTicks++;
        const compound = 1 + p._boostTicks * 0.003; // slow compounding drain
        if (this.hasPowerup(p, "boostme")) {
          // No mass loss while boostme is active
        } else {
          p.mass -= BOOST_DRAIN * compound;
        }
        if (Math.random() < 0.16 && !this.hasPowerup(p, "boostme")) {
          const tail = p.points[p.points.length - 1];
          if (tail) this.food.push({ x: tail.x, y: tail.y });
        }
      } else {
        p._boostTicks = Math.max(0, p._boostTicks - 2); // recover when not boosting
      }

      // Smooth speed ramping (lerp toward target)
      p._curSpeed += (targetSpeed - p._curSpeed) * 0.25;
      const speed = p._curSpeed;

      const head = p.points[0];
      const nx = head.x + Math.cos(p.heading) * speed;
      const ny = head.y + Math.sin(p.heading) * speed;

      p._stepAcc += speed;
      if (p._stepAcc >= POINT_STEP) {
        p._stepAcc = 0;
        p.points.unshift({ x: nx, y: ny });
      } else {
        p.points[0] = { x: nx, y: ny };
      }

      let len = 0, want = this.targetLen(p);
      for (let i = 1; i < p.points.length; i++) {
        len += Math.hypot(p.points[i].x - p.points[i-1].x, p.points[i].y - p.points[i-1].y);
        if (len > want) { p.points.length = i + 1; break; }
      }
    }

    /* 3. Eating + Magnet + Power-up pickup */
    for (const p of this.players.values()) {
      if (!p.alive) continue;
      const h = p.points[0];
      const eatR = this.snakeRadius(p) + 16;
      const er2 = eatR * eatR;

      // Magnet: pull nearby food toward head
      if (this.hasPowerup(p, "magnet")) {
        const magnetR2 = 22500; // ~150px radius
        for (const f of this.food) {
          const d2 = dist2(h.x, h.y, f.x, f.y);
          if (d2 < magnetR2 && d2 > 1) {
            const d = Math.sqrt(d2);
            f.x += (h.x - f.x) / d * 4;
            f.y += (h.y - f.y) / d * 4;
          }
        }
      }

      for (let i = this.food.length - 1; i >= 0; i--) {
        const f = this.food[i];
        if (dist2(h.x, h.y, f.x, f.y) < er2) {
          p.mass += FOOD_MASS;
          this.food[i] = this.food[this.food.length - 1];
          this.food.pop();
        }
      }

      // Power-up pickup (compound — can have multiple)
      for (let i = this.powerups.length - 1; i >= 0; i--) {
        const pu = this.powerups[i];
        if (dist2(h.x, h.y, pu.x, pu.y) < 900) { // ~30px radius
          const duration = pu.type === "invincible" ? 10000 : 15000;
          p.powerups.push({ type: pu.type, until: now + duration });
          if (pu.type === "jumbo") p.mass *= 4;
          this.powerups.splice(i, 1);
          this.send(p, { t: "powerup", type: pu.type });
        }
      }
    }

    // Remove food outside the border — 40% chance to respawn inside
    const br2 = this.borderR * this.borderR;
    for (let i = this.food.length - 1; i >= 0; i--) {
      const f = this.food[i];
      if (dist2(f.x, f.y, this.borderCenterX, this.borderCenterY) > br2) {
        this.food[i] = this.food[this.food.length - 1];
        this.food.pop();
        if (Math.random() < 0.4) this.food.push(this.randFoodInBorder());
      }
    }
    // Remove power-ups outside the border — 35% chance to respawn inside
    for (let i = this.powerups.length - 1; i >= 0; i--) {
      const pu = this.powerups[i];
      if (dist2(pu.x, pu.y, this.borderCenterX, this.borderCenterY) > br2) {
        this.powerups.splice(i, 1);
        if (Math.random() < 0.35) {
          const types = ["jumbo", "magnet", "boostme", "invincible"];
          const type = types[Math.floor(Math.random() * types.length)];
          const pos = this.randFoodInBorder();
          this.powerups.push({ x: pos.x, y: pos.y, type });
        }
      }
    }
    const foodTarget = Math.round(FOOD_TARGET * this.settings.foodRate);
    while (this.food.length < foodTarget) this.food.push(this.randFoodInBorder());

    /* 4. Collisions */
    for (const p of this.players.values()) {
      if (!p.alive) continue;
      const h = p.points[0];

      // 4a. Border: DRAIN mass — accelerates the longer you stay outside
      const distFromCenter = Math.hypot(h.x - this.borderCenterX, h.y - this.borderCenterY);
      if (distFromCenter > this.borderR) {
        p._stormTicks++;
        if (!this.hasPowerup(p, "invincible")) {
          const rampUp = 1 + p._stormTicks * 0.08;
          p.mass -= BORDER_DRAIN * rampUp;
          if (Math.random() < 0.15) {
            const tail = p.points[p.points.length - 1];
            if (tail) this.food.push({ x: tail.x, y: tail.y });
          }
          if (p.mass <= 1) {
            this.killSnake(p, "border");
            continue;
          }
        }
      } else {
        p._stormTicks = 0;
      }

      // 4b. Snake-vs-snake
      const hr = this.snakeRadius(p);
      for (const q of this.players.values()) {
        if (q === p || !q.alive) continue;
        const br = this.snakeRadius(q);
        const lethal = (hr + br) * 0.82;
        const l2 = lethal * lethal;
        for (let i = 0; i < q.points.length; i += 2) {
          if (dist2(h.x, h.y, q.points[i].x, q.points[i].y) < l2) {
            if (this.hasPowerup(p, "invincible")) {
              // Bounce away from the collision point
              const cx = q.points[i].x, cy = q.points[i].y;
              const dx = h.x - cx, dy = h.y - cy;
              const d = Math.sqrt(dx * dx + dy * dy) || 1;
              const pushDist = lethal * 1.3;
              h.x = cx + (dx / d) * pushDist;
              h.y = cy + (dy / d) * pushDist;
              p.points[0] = { x: h.x, y: h.y };
              p.heading = Math.atan2(dy, dx);
              p.targetAngle = p.heading;
            } else {
              this.killSnake(p, "collision");
            }
            break;
          }
        }
        if (!p.alive) break;
      }
    }

    /* 5. Broadcast state */
    this.broadcastState();
  }

  /* ---- networking ---- */
  send(p, obj) { if (p.ws.readyState === 1) p.ws.send(JSON.stringify(obj)); }
  broadcast(obj) {
    const s = JSON.stringify(obj);
    for (const p of this.players.values()) if (p.ws.readyState === 1) p.ws.send(s);
  }

  broadcastLobby() {
    const players = [...this.players.values()].map(p => ({
      id: p.id, name: p.name, isHost: p.isHost, alive: p.alive, color: p.color,
    }));
    this.broadcast({
      t: "lobby", state: this.state, players,
      winner: this.winnerName,
      settings: this.settings,
      isPublic: this.isPublic,
    });
  }

  broadcastState() {
    if (!this._tickCount) this._tickCount = 0;
    this._tickCount++;

    const snakes = [];
    for (const p of this.players.values()) {
      if (!p.alive) continue;
      const pts = [];
      // Send every 3rd point instead of every 2nd — cuts bandwidth 33%
      for (let i = 0; i < p.points.length; i += 3) {
        pts.push(Math.round(p.points[i].x), Math.round(p.points[i].y));
      }
      snakes.push({
        id: p.id, n: p.name, c: p.color, pat: p.pattern,
        r: Math.round(this.snakeRadius(p)),
        m: Math.round(p.mass), p: pts,
        b: p.boost && p.mass > BOOST_MIN_MASS ? 1 : 0,
        pu: p.powerups.map(x => x.type),
      });
    }

    // Only send food every 3rd tick (food doesn't move fast)
    let food;
    if (this._tickCount % 3 === 0 || !this._lastFood) {
      food = [];
      for (const f of this.food) food.push(Math.round(f.x), Math.round(f.y));
      this._lastFood = food;
    } else {
      food = this._lastFood;
    }

    const pups = [];
    for (const pu of this.powerups) pups.push(Math.round(pu.x), Math.round(pu.y), pu.type);

    const payload = JSON.stringify({
      t: "state",
      br: Math.round(this.borderR),
      bcx: Math.round(this.borderCenterX),
      bcy: Math.round(this.borderCenterY),
      bp: this.borderPhase,
      wr: this.settings.mapSize,
      pups,
      alive: snakes.length,
      total: this.players.size,
      s: snakes,
      f: food,
    });

    for (const p of this.players.values()) {
      if (p.ws.readyState === 1) {
        p.ws.send(payload);
        p.ws.send(JSON.stringify({ t: "you", id: p.id, alive: p.alive }));
      }
    }
  }
}

/* ====================================================================
 *  HTTP + WebSocket server
 * ==================================================================== */
const rooms = new Map();
function getRoom(code) {
  code = (code || "MAIN").toUpperCase().replace(/[^A-Z0-9]/g, "").slice(0, 8) || "MAIN";
  if (!rooms.has(code)) rooms.set(code, new Room(code));
  return rooms.get(code);
}

function findQuickPlayRoom() {
  // Find an existing public room in lobby state with space
  for (const [code, room] of rooms) {
    if (room.isPublic && room.state === "lobby" && room.players.size < room.settings.maxPlayers) {
      return room;
    }
  }
  // No open public room — create a new one with a random code
  const code = "PUB" + Math.random().toString(36).substring(2, 5).toUpperCase();
  const room = new Room(code);
  room.isPublic = true;
  rooms.set(code, room);
  return room;
}

const server = http.createServer((req, res) => {
  // Security headers
  const secHeaders = {
    "X-Content-Type-Options": "nosniff",
    "X-Frame-Options": "DENY",
    "X-XSS-Protection": "1; mode=block",
    "Referrer-Policy": "no-referrer",
    "Content-Security-Policy": "default-src 'self' 'unsafe-inline' https://fonts.googleapis.com https://fonts.gstatic.com; connect-src 'self' ws: wss:",
  };

  // Only allow GET
  if (req.method !== "GET") {
    res.writeHead(405, secHeaders); return res.end("method not allowed");
  }

  let file = req.url === "/" ? "/index.html" : req.url.split("?")[0];

  // Block path traversal
  const normalized = path.normalize(file).replace(/\\/g, "/");
  if (normalized.includes("..")) {
    res.writeHead(403, secHeaders); return res.end("forbidden");
  }

  const full = path.join(__dirname, "public", normalized);
  if (!full.startsWith(path.join(__dirname, "public"))) {
    res.writeHead(403, secHeaders); return res.end("forbidden");
  }

  fs.readFile(full, (err, data) => {
    if (err) { res.writeHead(404, secHeaders); return res.end("not found"); }
    const ext = path.extname(full);
    const type = ext === ".html" ? "text/html"
      : ext === ".js" ? "text/javascript"
      : ext === ".css" ? "text/css" : "text/plain";
    res.writeHead(200, { ...secHeaders, "Content-Type": type });
    res.end(data);
  });
});

// ===== SECURITY: Rate limiting per IP =====
const ipConnections = new Map(); // ip -> { count, lastClean }
const MAX_CONNS_PER_IP = 6;
const MSG_RATE_LIMIT = 30; // max messages per second per connection

const wss = new WebSocketServer({
  server,
  perMessageDeflate: {
    zlibDeflateOptions: { level: 1 }, // fast compression
    threshold: 128, // only compress messages > 128 bytes
  },
});
wss.on("connection", (ws, req) => {
  // Rate limit connections per IP
  const ip = req.headers["x-forwarded-for"]?.split(",")[0]?.trim() || req.socket.remoteAddress || "unknown";
  const conns = ipConnections.get(ip) || { count: 0 };
  conns.count++;
  ipConnections.set(ip, conns);
  if (conns.count > MAX_CONNS_PER_IP) {
    ws.close(1008, "Too many connections");
    return;
  }

  let room = null, me = null;
  let msgCount = 0;
  let msgResetTime = Date.now();

  ws.on("message", (raw) => {
    // Rate limit messages
    const now = Date.now();
    if (now - msgResetTime > 1000) { msgCount = 0; msgResetTime = now; }
    msgCount++;
    if (msgCount > MSG_RATE_LIMIT) return;

    // Size limit (prevent memory bombs)
    if (raw.length > 512) return;

    let msg;
    try { msg = JSON.parse(raw); } catch { return; }

    // Type must be a string
    if (typeof msg.t !== "string") return;

    if (msg.t === "join") {
      if (room) return;
      const name = String(msg.name || "").replace(/[<>&"']/g, "").slice(0, 14);
      const mode = msg.mode || "private";
      if (mode === "quickplay") {
        room = findQuickPlayRoom();
      } else {
        const roomCode = String(msg.room || "").replace(/[^A-Za-z0-9]/g, "").slice(0, 8).toUpperCase() || "MAIN";
        room = getRoom(roomCode);
      }
      me = room.addPlayer(ws, name, msg.color, msg.pattern);
      return;
    }
    if (!room || !me) return;

    switch (msg.t) {
      case "input":
        if (typeof msg.angle === "number" && isFinite(msg.angle)) me.targetAngle = msg.angle;
        me.boost = !!msg.boost;
        break;
      case "start":
        if (me.isHost) room.startCountdown();
        break;
      case "settings":
        if (me.isHost) room.updateSettings(msg);
        break;
      case "endgame":
        if (me.isHost || room.state === "postgame") {
          room.state = "lobby";
          room.winnerName = null;
          room.broadcast({ t: "roundover", winner: null, winnerId: null, ended: true });
          room.broadcastLobby();
        }
        break;
    }
  });

  ws.on("close", () => {
    const c = ipConnections.get(ip);
    if (c) { c.count--; if (c.count <= 0) ipConnections.delete(ip); }
    if (room && me) room.removePlayer(me.id);
  });
  ws.on("error", () => {});
});

setInterval(() => {
  for (const [code, room] of rooms) {
    room.step();
    if (room.players.size === 0 && room.state === "lobby") rooms.delete(code);
  }
}, TICK_MS);

server.listen(PORT, () => {
  console.log(`WormyRoyal.io running on http://localhost:${PORT}`);
  console.log(`Open that URL, or expose it with a tunnel so friends can join.`);
});
