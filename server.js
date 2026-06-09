const http = require("http");
const fs = require("fs");
const path = require("path");
const { WebSocketServer } = require("ws");

const PORT = process.env.PORT || 8080;

/* ----------------------------- Defaults ------------------------------ */
const TICK_MS          = 8;               // 125Hz physics — slither.io's exact tick rate
const COUNTDOWN_MS     = 5000;
const POSTGAME_MS      = 9000;

// ===== SLITHER.IO PHYSICS CONSTANTS (READ FROM ACTUAL SOURCE) =====
// Pulled live from slither.io/s/game.js:
//   spangdv = 4.8
//   nsp1 = 4.25, nsp2 = 0.5, nsp3 = 12
//   mamu = 0.033, mamu2 = 0.028
//   cst = 0.43  (chain catch-up — used every tick in body relaxation)
// Slither has two turn constants: mamu=0.033 (used for the local player's
// cosmetic angle easing) and mamu2=0.028 (the authoritative rate at which
// a snake's heading chases its wanted angle). The server-side body turn is
// mamu2 — using 0.033 made turning ~18% twitchier than real slither.
const TURN_PER_TICK    = 0.028;           // slither's mamu2
const BASE_SPEED       = 1.2;             // px per 8ms tick at sc=1 = 150 px/s
const NSP1             = 4.25;            // slither's nsp1 (speed base)
const NSP2             = 0.5;             // slither's nsp2 (speed per sc)
// Slither boost: nsp3=12 = absolute boost speed in slither units.
// Boost ratio nsp3 / (nsp1+nsp2) = 12 / 4.75 = 2.526× base
// In our units: BOOST adds enough delta to reach 2.5× total.
const BOOST_DELTA      = 1.83;            // px/tick added during boost (gives ~2.5× total)
// Slither.io spawns with 27 body segments (reference/slither-game.js
// line 191242: `for (var i = 27; i >= 1; i--)`). At sc=1.236 the snake
// already looks like a proper noodle, not a stub.
const START_SCT        = 27;
const BOOST_MIN_SCT    = 5;
const WSEP_BASE        = 6;               // slither's wsep = 6 * sc
const BODY_R_BASE      = 5;
const FOOD_TARGET      = 200;
const FOOD_VAL         = 1;               // fam value per food (slither has variable, ours fixed)

// === Slither's exact diminishing-returns growth curve ===
// Source: reference/slither-game.js line 42798 setMscps()
// fmlts[i] = (1 - i/mscps)^2.25  for i in 0..mscps
// Growth threshold for sct -> sct+1 is 1 / fmlts[sct].
// At sct=0, fmlts=1.0 → threshold=1 (fast early growth).
// At sct=200 (with mscps=300), fmlts=0.094 → threshold=10.6 food per segment.
// At sct=290, threshold ≈ 850 food per segment — growth nearly stops.
const MSCPS = 300;
const FMLTS = new Float64Array(MSCPS + 2048);
for (let i = 0; i < FMLTS.length; i++) {
  if (i >= MSCPS) FMLTS[i] = FMLTS[MSCPS - 1];
  else FMLTS[i] = Math.pow(1 - i / MSCPS, 2.25);
}
function growthThreshold(sct) {
  // 1 / fmlts[sct], with safety clamp
  const idx = Math.max(0, Math.min(FMLTS.length - 1, sct));
  const f = FMLTS[idx];
  return f > 0.0001 ? 1 / f : 10000;
}
const BORDER_DRAIN     = 0.144;           // body parts lost per tick in storm (custom)
// Broadcast on every 2nd physics tick = ~60 Hz network update rate over
// the 125 Hz physics. Halves snapshot-to-snapshot jitter on the client.
// Doubles outbound bandwidth (was 30 Hz). For a 10-player game this is
// going from ~60 KB/s to ~120 KB/s — well within any modern connection.
const BROADCAST_EVERY  = 2;

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
      winsNeeded: 3,       // tournament target — first to N round wins
    };

    // Tournament state — persists across rounds within a single private room.
    // Reset on tournament victory; cleared when room is destroyed.
    this.tournamentWins = new Map();   // playerId → number of round wins
    this.tournamentCrownId = null;     // last tournament champion's id (shows crown next session)
    this.tournamentChampionName = null;

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
    this.isTestMode = false;  // solo practice mode
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
    const validPattern = ["solid","striped","gradient","rings","rainbow"].includes(pattern) ? pattern : "solid";
    const p = {
      id, ws, name: (name || "snake").slice(0, 14), isHost,
      color: validColor, pattern: validPattern,
      alive: false, points: [], heading: 0, targetAngle: 0,
      // sct  = body part count (slither: number of segments)
      // fam  = fractional fullness 0..1 (slither: fullness on dying tail).
      //        On food: fam += food_val. When fam >= 1: sct++, fam -= 1.
      //        On boost drain / border: fam -= drain. When fam < 0:
      //        sct--, fam += 1. (Matches slither's algorithm exactly.)
      // _dyingPts: list of recently-trimmed tail points fading out
      //           ({x, y, fadeStart} — render with alpha proportional to remaining time)
      boost: false, sct: START_SCT, fam: 0, _curSpeed: BASE_SPEED, _stormTicks: 0,
      _dyingPts: [],
    };
    this.players.set(id, p);
    this.send(p, { t: "welcome", id, room: this.code, isHost, settings: this.settings, isPublic: this.isPublic, isTestMode: this.isTestMode });
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
    // Number.isFinite (not typeof) — a NaN here poisons border math and
    // spawn positions into NaN, which renders as an empty world.
    if (Number.isFinite(s.mapSize)) this.settings.mapSize = Math.max(800, Math.min(5000, s.mapSize));
    if (Number.isFinite(s.borderSpeed)) this.settings.borderSpeed = Math.max(0.25, Math.min(4, s.borderSpeed));
    if (Number.isFinite(s.maxPlayers)) this.settings.maxPlayers = Math.max(2, Math.min(50, s.maxPlayers));
    if (Number.isFinite(s.graceMs)) this.settings.graceMs = Math.max(0, Math.min(60000, s.graceMs));
    if (Number.isFinite(s.shrinkMs)) this.settings.shrinkMs = Math.max(10000, Math.min(300000, s.shrinkMs));
    if (Number.isFinite(s.snakeSpeed)) this.settings.snakeSpeed = Math.max(0.5, Math.min(3, s.snakeSpeed));
    if (Number.isFinite(s.boostSpeed)) this.settings.boostSpeed = Math.max(0.5, Math.min(4, s.boostSpeed));
    if (Number.isFinite(s.foodRate)) this.settings.foodRate = Math.max(0.25, Math.min(5, s.foodRate));
    if (Number.isFinite(s.winsNeeded)) this.settings.winsNeeded = Math.max(1, Math.min(20, s.winsNeeded));
    this.broadcastLobby();
  }

  /* ---- snake spawning (hunger-games style: on the border edge) ---- */
  spawnSnake(p) {
    // Place every snake on a ring near the border, evenly distributed
    // away from any other live snakes (like Hunger Games tributes around
    // the Cornucopia). Heads point inward so nobody walks into the wall
    // off the spawn.
    const SPAWN_RADIUS = this.borderR * 0.92;
    const SLOT_COUNT = 32;
    let bestSlot = 0;
    let bestMinDist = -1;
    // Random rotation of the slot grid so every round looks different.
    const rotOff = Math.random() * (Math.PI * 2);
    for (let s = 0; s < SLOT_COUNT; s++) {
      const angle = rotOff + s * (Math.PI * 2 / SLOT_COUNT);
      const cx = this.borderCenterX + Math.cos(angle) * SPAWN_RADIUS;
      const cy = this.borderCenterY + Math.sin(angle) * SPAWN_RADIUS;
      let minDist = Infinity;
      for (const q of this.players.values()) {
        if (q === p || !q.alive || q.points.length === 0) continue;
        const qh = q.points[0];
        const d = dist2(qh.x, qh.y, cx, cy);
        if (d < minDist) minDist = d;
      }
      if (minDist > bestMinDist) {
        bestMinDist = minDist;
        bestSlot = s;
      }
    }
    const angle = rotOff + bestSlot * (Math.PI * 2 / SLOT_COUNT);
    const hx = this.borderCenterX + Math.cos(angle) * SPAWN_RADIUS;
    const hy = this.borderCenterY + Math.sin(angle) * SPAWN_RADIUS;
    // Heading: face the centre of the arena
    p.heading = Math.atan2(this.borderCenterY - hy, this.borderCenterX - hx);
    p.targetAngle = p.heading;
    p.sct = START_SCT;
    p.fam = 0;
    p._dyingPts = [];
    p._stepAcc = 0;
    p.boost = false;
    p.alive = true;
    p._curSpeed = BASE_SPEED;
    p._stormTicks = 0;

    p.powerups = [];        // array of {type, until}
    p.points = [];
    // Initial body: START_SCT points laid backward from head at wsep
    // (slither's chain relaxation will smooth them as the snake moves)
    const wsep = this.getWsep(p);
    for (let i = 0; i < START_SCT; i++) {
      p.points.push({
        x: hx - Math.cos(p.heading) * i * wsep,
        y: hy - Math.sin(p.heading) * i * wsep,
      });
    }
  }

  hasPowerup(p, type) { return p.powerups.some(pu => pu.type === type); }

  // === SLITHER.IO CORE FORMULAS ===
  // sc = thickness factor, ranges 1 (tiny) to 6 (max)
  getSC(p) {
    return Math.min(6, 1 + (p.sct - 2) / 106);
  }
  // scang = turn rate scaler — slither's exact quadratic falloff.
  // Big snakes turn slowly (15% rate at sc=6); that IS the slither feel.
  // If huge snakes ever need a mercy buff, lower the exponent toward 1.7
  // (one line, here) — but 2.0 is what slither actually runs.
  getScang(sc) {
    return 0.13 + 0.87 * Math.pow((7 - sc) / 6, 2);
  }
  // wsep = segment spacing in pixels (scales with thickness)
  getWsep(p) {
    return WSEP_BASE * this.getSC(p);
  }
  // body radius (visual + collision) — slither.io: lsz = 29 * sc, radius = lsz/2.
  // Source: reference/slither-game.js line 116673  (var lsz = 29 * ssc)
  snakeRadius(p) {
    let r = 14.5 * this.getSC(p);
    if (this.hasPowerup(p, "jumbo")) r *= 1.6;
    return r;
  }
  // speed per tick, slither's exact ssp formula
  getSpeed(p) {
    const sc = this.getSC(p);
    // Slither: ssp = nsp1 + nsp2*sc per 8ms (nsp1=4.25, nsp2=0.5)
    // Normalized to sc=1 baseline (= NSP1 + NSP2 = 4.75)
    return BASE_SPEED * (NSP1 + NSP2 * sc) / (NSP1 + NSP2);
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
    // Test mode allows solo play; everything else needs 2+
    if (!this.isTestMode && this.players.size < 2) return;

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
    // Test mode never ends — solo player can roam freely.
    if (this.isTestMode) return;
    const alive = [...this.players.values()].filter(p => p.alive);
    if (alive.length <= 1 && this.starterCount >= 1) {
      this.state = "postgame";
      this.winnerName = alive.length === 1 ? alive[0].name : null;
      const winnerId = alive.length === 1 ? alive[0].id : null;
      this.phaseUntil = Date.now() + POSTGAME_MS;

      // === Tournament tracking ===
      let wins = 0;
      let tournamentChampion = null;
      if (winnerId != null) {
        wins = (this.tournamentWins.get(winnerId) || 0) + 1;
        this.tournamentWins.set(winnerId, wins);
        if (wins >= this.settings.winsNeeded) {
          // Tournament champion!
          tournamentChampion = this.winnerName;
          this.tournamentCrownId = winnerId;
          this.tournamentChampionName = this.winnerName;
          this.tournamentWins.clear(); // fresh tournament starts next round
        }
      }

      this.broadcast({
        t: "roundover",
        winner: this.winnerName,
        winnerId,
        roundWins: wins,
        winsNeeded: this.settings.winsNeeded,
        tournamentChampion, // non-null only when somebody just won the whole thing
      });
      this.broadcastLobby();
    }
  }

  killSnake(p, reason) {
    if (!p.alive) return;
    p.alive = false;
    // Slither.io: dead snakes drop ~70% of their body as food orbs
    // along the body trail.
    const drops = Math.min(400, Math.floor(p.sct * 0.7));
    const bodyLen = p.points.length;
    for (let i = 0; i < drops && bodyLen > 0; i++) {
      const idx = Math.floor((i / drops) * bodyLen) % bodyLen;
      const pt = p.points[idx];
      if (pt) this.food.push({ x: pt.x + rand(-12, 12), y: pt.y + rand(-12, 12) });
    }
    p.points = [];
    this.send(p, { t: "died", reason });
    if (this.state === "playing") this.checkWin();
    // Test mode: auto-respawn after a short delay (no game over)
    if (this.isTestMode && this.state === "playing") {
      setTimeout(() => {
        if (this.isTestMode && this.players.has(p.id) && this.state === "playing") {
          this.spawnSnake(p);
        }
      }, 1500);
    }
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
    const finalMs = 40000 / spd;  // how long final shrink takes (doubled — slower endgame)

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
      // Circle drifts around the map center on a slow arc. Was moveSpeed=1.2
      // (=150 px/sec) which felt too aggressive in the endgame; players
      // couldn't react. Halved the linear drift and the angular turn rate.
      const moveSpeed = 0.5 * spd;
      this.moveAngle += 0.003 * spd;
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
    if (this.powerupTimer >= 1250 && this.powerups.length < 5) { // every ~10 sec (125Hz × 10)
      this.powerupTimer = 0;
      const types = ["jumbo", "magnet", "boostme", "invincible"];
      const type = types[Math.floor(Math.random() * types.length)];
      const pos = this.randFoodInBorder();
      this.powerups.push({ x: pos.x, y: pos.y, type });
    }

    /* 2. Move every alive snake — SLITHER.IO physics. */
    for (const p of this.players.values()) {
      if (!p.alive) continue;

      // Expire power-ups
      p.powerups = p.powerups.filter(pu => now < pu.until);

      // ===== TURN RATE (slither.io exact formula) =====
      //   sc    = thickness factor from body part count
      //   scang = 0.13 + 0.87 * ((7-sc)/6)^2   quadratic falloff
      //   omega = MAMU * scang  (rad per tick)
      const sc = this.getSC(p);
      const scang = this.getScang(sc);
      const turnRate = TURN_PER_TICK * scang * this.settings.snakeSpeed;
      const d = angleDelta(p.heading, p.targetAngle);
      const turnApplied = Math.max(-turnRate, Math.min(turnRate, d));
      p.heading += turnApplied;

      // ===== SPEED (slither.io: ssp = 5.39 + 0.4*sc) =====
      let targetSpeed = this.getSpeed(p) * this.settings.snakeSpeed;
      // BoostMe powerup: small passive speed bump (+15%) for the whole
      // duration, on top of removing boost-drain.
      const hasBoostMe = this.hasPowerup(p, "boostme");
      if (hasBoostMe) targetSpeed *= 1.15;
      const isBoosting = p.boost && p.sct > BOOST_MIN_SCT;
      if (isBoosting) {
        targetSpeed += BOOST_DELTA * this.settings.boostSpeed;
        // Slither: boost drain reduces fam (~1% of current size/sec).
        // At 125Hz: 0.008 of one segment per tick.
        if (!hasBoostMe) {
          p.fam -= 0.008;
          // Boost drops food trail
          if (Math.random() < 0.045) {
            const tail = p.points[p.points.length - 1];
            if (tail) this.food.push({ x: tail.x, y: tail.y });
          }
        }
      }
      // Speed ramps LINEARLY toward target — slither accelerates at a
      // fixed ±0.3 of its speed units per 8ms frame, not an exponential
      // snap. In our px/tick units: 0.3 × (BASE_SPEED / (NSP1+NSP2)) ≈
      // 0.076. Boost spool-up takes ~190ms (24 ticks), and easing off
      // boost glides down over the same window. The old 0.35 exponential
      // lerp hit target in ~80ms — boost felt like a gear-snap instead
      // of slither's smooth surge.
      const SPEED_RAMP = 0.076;
      if (p._curSpeed < targetSpeed) {
        p._curSpeed = Math.min(targetSpeed, p._curSpeed + SPEED_RAMP);
      } else if (p._curSpeed > targetSpeed) {
        p._curSpeed = Math.max(targetSpeed, p._curSpeed - SPEED_RAMP);
      }
      const speed = p._curSpeed;

      // ===== HEAD + BODY: SLITHER.IO actual architecture =====
      // From reading slither.io/s/game.js source:
      //   1. Head moves smoothly EVERY tick (o.xx += cos(ang)*csp)
      //   2. New pts entry pushed ONLY when head has traveled msl distance
      //   3. Chain relaxation runs ONCE PER PUSH (not every tick)
      // This keeps body at proper msl/wsep spacing AND smooths the chain
      // without compressing it to a tiny ball every tick.
      const head = p.points[0];
      const nx = head.x + Math.cos(p.heading) * speed;
      const ny = head.y + Math.sin(p.heading) * speed;
      // Head moves smoothly (just update the first point)
      p.points[0] = { x: nx, y: ny };

      // Track distance traveled since last pts push
      if (!p._stepAcc) p._stepAcc = 0;
      p._stepAcc += speed;
      const wsep = this.getWsep(p);

      // When head has moved a full msl/wsep, push a new pts entry.
      // This is the ONLY time we expand the body or run chain relaxation.
      if (p._stepAcc >= wsep) {
        p._stepAcc -= wsep;

        // Unshift the current head position as a new body point.
        // Now p.points[0] = head (will keep moving), p.points[1] = frozen.
        p.points.unshift({ x: nx, y: ny });

        // ===== GROW/SHRINK via fam (only when pushing) =====
        // Slither's exact non-linear threshold: 1/fmlts[sct].
        // Fast at low sct, very slow approaching mscps=300.
        const growT = growthThreshold(p.sct);
        if (p.fam >= growT) {
          p.sct++;
          p.fam -= growT;
        } else if (p.fam < 0 && p.sct > 2) {
          const shrinkT = growthThreshold(p.sct - 1);
          p.sct--;
          p.fam += shrinkT;
        }

        // ===== CHAIN RELAXATION — slither's exact cst=0.43 =====
        // Each point chases its predecessor once per push, with the
        // 4-point ramp at the head. This compresses raw point spacing —
        // that's expected and slither-correct. Body LENGTH is no longer
        // tied to point count (see length-based trim below), so the
        // compression no longer makes snakes stubby. In-place mutation,
        // no per-point allocation.
        const CST = 0.43;
        let n = 0;
        for (let m = 3; m < p.points.length; m++) {
          n++;
          const mv = n <= 4 ? CST * n / 4 : CST;
          const ahead = p.points[m - 1];
          const curr = p.points[m];
          curr.x += (ahead.x - curr.x) * mv;
          curr.y += (ahead.y - curr.y) * mv;
        }

        // ===== LENGTH-BASED TAIL TRIM (replaces count-based) =====
        // Slither's visual body length = sct * wsep of ARC LENGTH along
        // the path — not "sct points". Since relaxation compresses point
        // spacing below wsep, we keep however many points it takes for
        // the polyline to span the target length, and trim the excess.
        // (Renderers walk this path by arc length, so collision and
        // visuals both see a full-length body.)
        const targetLen = p.sct * wsep;
        let acc = 0;
        let cut = p.points.length;
        for (let i = 1; i < p.points.length; i++) {
          const a = p.points[i - 1], b = p.points[i];
          acc += Math.hypot(b.x - a.x, b.y - a.y);
          if (acc >= targetLen) { cut = i + 1; break; }
        }
        if (cut < p.points.length) p.points.length = cut;
        // Hard cap — runaway safety (a 300-sct snake needs ~700 pts)
        if (p.points.length > 1500) p.points.length = 1500;
      }

      // Cleanup faded dying points (every tick, not just on push)
      const FADE_MS = 400;
      while (p._dyingPts.length > 0 && now - p._dyingPts[0].fadeStart > FADE_MS) {
        p._dyingPts.shift();
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
          p.fam += FOOD_VAL;  // slither: fam accumulator
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
          if (pu.type === "jumbo") p.fam += 50; // adds ~50 segments via fam
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

      // 4a. Border: DRAIN segments — accelerates the longer you stay outside
      const distFromCenter = Math.hypot(h.x - this.borderCenterX, h.y - this.borderCenterY);
      if (distFromCenter > this.borderR) {
        p._stormTicks++;
        if (!this.hasPowerup(p, "invincible")) {
          const rampUp = 1 + p._stormTicks * 0.02; // scaled for 125Hz
          p.fam -= BORDER_DRAIN * rampUp;
          if (Math.random() < 0.15) {
            const tail = p.points[p.points.length - 1];
            if (tail) this.food.push({ x: tail.x, y: tail.y });
          }
          if (p.sct <= 2) {
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

    /* 5. Broadcast state — only every BROADCAST_EVERY tick (30Hz over 60Hz physics) */
    if (!this._physicsTickN) this._physicsTickN = 0;
    this._physicsTickN++;
    if (this._physicsTickN % BROADCAST_EVERY === 0) {
      this.broadcastState();
    }
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
      wins: this.tournamentWins.get(p.id) || 0,
      hasCrown: p.id === this.tournamentCrownId,
    }));
    this.broadcast({
      t: "lobby", state: this.state, players,
      winner: this.winnerName,
      settings: this.settings,
      isPublic: this.isPublic,
      isTestMode: this.isTestMode,
      tournamentChampion: this.tournamentChampionName,
      winsNeeded: this.settings.winsNeeded,
    });
  }

  broadcastState() {
    if (!this._tickCount) this._tickCount = 0;
    this._tickCount++;

    const snakes = [];
    for (const p of this.players.values()) {
      if (!p.alive) continue;
      const pts = [];
      // Adaptive subsampling: small snakes send every point (smooth viz),
      // big snakes subsample to save bandwidth.
      // Always include the head and tail points exactly.
      const total = p.points.length;
      const step = total < 30 ? 1 : (total < 80 ? 2 : 3);
      for (let i = 0; i < total; i += step) {
        pts.push(Math.round(p.points[i].x), Math.round(p.points[i].y));
      }
      // Ensure tail is always sent
      if ((total - 1) % step !== 0 && total > 1) {
        const lastIdx = total - 1;
        pts.push(Math.round(p.points[lastIdx].x), Math.round(p.points[lastIdx].y));
      }
      snakes.push({
        id: p.id, n: p.name, c: p.color, pat: p.pattern,
        r: Math.round(this.snakeRadius(p)),
        m: p.sct, p: pts,
        b: p.boost && p.sct > BOOST_MIN_SCT ? 1 : 0,
        pu: p.powerups.map(x => x.type),
        // Crown flag — previous tournament champion in this room
        cw: p.id === this.tournamentCrownId ? 1 : 0,
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
const MSG_RATE_LIMIT = 80; // max messages/sec/connection (client sends 60Hz input + occasional control)

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
    try {
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
      } else if (mode === "test") {
        // Create a fresh private test room — solo play, no waiting, never ends
        const code = "TEST" + Math.random().toString(36).substring(2, 5).toUpperCase();
        room = new Room(code);
        room.isTestMode = true;
        // Sensible defaults for solo roaming
        room.settings.mapSize = 1800;
        room.settings.snakeSpeed = 1.0;
        room.settings.boostSpeed = 1.5;
        room.settings.borderSpeed = 0.25;  // very slow border in test
        room.settings.foodRate = 1.5;      // extra food for testing growth
        room.settings.maxPlayers = 1;
        rooms.set(code, room);
      } else {
        const roomCode = String(msg.room || "").replace(/[^A-Za-z0-9]/g, "").slice(0, 8).toUpperCase() || "MAIN";
        room = getRoom(roomCode);
      }
      me = room.addPlayer(ws, name, msg.color, msg.pattern);
      // Test mode: immediately start (no countdown wait for 2nd player)
      if (room && room.isTestMode && me) {
        // Small delay so welcome message processes first
        setTimeout(() => {
          if (room.state === "lobby") room.startCountdown();
        }, 100);
      }
      return;
    }
    if (!room || !me) return;

    switch (msg.t) {
      case "input":
        if (typeof msg.angle === "number" && isFinite(msg.angle)) me.targetAngle = msg.angle;
        me.boost = !!msg.boost;
        break;
      case "testSize":
        // Only allowed in test mode — adjust snake size for practice
        if (room.isTestMode && me.alive && typeof msg.delta === "number" && isFinite(msg.delta)) {
          const d = Math.max(-500, Math.min(500, Math.round(msg.delta)));
          // Directly adjust sct in test mode (fam accumulator bypassed)
          me.sct = Math.max(2, Math.min(5000, me.sct + d));
        }
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
    } catch (e) {
      // A malformed message (or a bug it tickles) must not crash the
      // process — that kills every room's sockets at once.
      console.error("[ws message] handler crashed:", e && e.stack || e);
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
    // One room throwing must not kill the process (and every other
    // room's sockets with it). Log loudly and keep ticking.
    try {
      room.step();
    } catch (e) {
      console.error(`[room ${code}] step() crashed:`, e && e.stack || e);
    }
    if (room.players.size === 0 && room.state === "lobby") rooms.delete(code);
  }
}, TICK_MS);

// Last-resort visibility: if the process is dying in production, pm2's
// error log gets a stack trace instead of a silent restart loop.
process.on("uncaughtException", (err) => {
  console.error("[FATAL] uncaughtException:", err && err.stack || err);
});
process.on("unhandledRejection", (err) => {
  console.error("[FATAL] unhandledRejection:", err && err.stack || err);
});

server.listen(PORT, () => {
  console.log(`WormyRoyal.io running on http://localhost:${PORT}`);
  console.log(`Open that URL, or expose it with a tunnel so friends can join.`);
});
