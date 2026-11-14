const http = require('http');
const WebSocket = require('ws');
const crypto = require('crypto');

const PORT = process.env.PORT || 3001;
const TICK_RATE = 30;
const TICK_MS = 1000 / TICK_RATE;

/* ============================================================
   КОНСТАНТЫ ИГРЫ (синхронизированы с клиентом)
   ============================================================ */
const FLOOR = 60;
const PLAYER_HEIGHT = 1.6;
const CROUCH_HEIGHT = 1.1;
const GRAVITY = -22;
const JUMP_VELOCITY = 8.0;
const PLAYER_SPEED = 8;
const PLAYER_CROUCH_SPEED = 4;
const PLAYER_RADIUS = 0.4;

const WEAPON_STATS = {
  rifle:   { magSize: 30, reloadTime: 3000, damageBody: 20, damageHead: 80, fireRate: 110, range: 120 },
  shotgun: { magSize: 8,  reloadTime: 3000, damageBody: 40, damageHead: 140, fireRate: 800, range: 40 },
  sniper:  { magSize: 5,  reloadTime: 3000, damageBody: 400, damageHead: 500, fireRate: 1500, range: 200 },
  knife:   { magSize: 1,  reloadTime: 0,    damageBody: 9999, damageHead: 9999, fireRate: 600, range: 2.0 }
};

const KNIFE_ANGLE = Math.PI / 6;

/* ============================================================
   КАРТА (коллайдеры)
   ============================================================ */
const walls = [
  { x: 0, z: -FLOOR, w: FLOOR*2, d: 1, h: 6 },
  { x: 0, z:  FLOOR, w: FLOOR*2, d: 1, h: 6 },
  { x: -FLOOR, z: 0, w: 1, d: FLOOR*2, h: 6 },
  { x: FLOOR, z: 0, w: 1, d: FLOOR*2, h: 6 },
  { x: -20, z: -10, w: 1, d: 30, h: 4.5 },
  { x:  20, z:  10, w: 1, d: 30, h: 4.5 },
  { x:  0,  z: -28, w: 35, d: 1, h: 4.5 },
  { x:  0,  z:  32, w: 35, d: 1, h: 4.5 },
  { x: -35, z: -30, w: 15, d: 1, h: 4 },
  { x:  35, z:  30, w: 15, d: 1, h: 4 },
  { x:  10, z:  10, w: 3, d: 3, h: 1.8 },
  { x: -15, z:  15, w: 3, d: 3, h: 2.0 },
  { x:  15, z: -20, w: 4, d: 4, h: 2.2 },
  { x: -30, z:  0, w: 2, d: 5, h: 1.8 },
  { x:  30, z:  0, w: 2, d: 5, h: 1.8 },
  { x:  25, z: -35, w: 4, d: 4, h: 2.5 },
  { x: -25, z:  35, w: 4, d: 4, h: 2.5 },
  { x: -15, z: -15, w: 1.5, d: 1.5, h: 4.5 },
  { x:  15, z:  15, w: 1.5, d: 1.5, h: 4.5 },
  { x:  5,  z: -5, w: 1.2, d: 1.2, h: 1.5 },
  { x: -5,  z:  5, w: 1.2, d: 1.2, h: 1.5 },
];

const colliders = walls.map(w => ({
  minX: w.x - w.w/2, maxX: w.x + w.w/2,
  minY: 0, maxY: w.h,
  minZ: w.z - w.d/2, maxZ: w.z + w.d/2,
}));

function canExistAt(nx, nz, y, radius, height = PLAYER_HEIGHT) {
  if (Math.abs(nx) > FLOOR-1 || Math.abs(nz) > FLOOR-1) return false;
  const minX = nx - radius, maxX = nx + radius;
  const minY = y + 0.02, maxY = y + height;
  const minZ = nz - radius, maxZ = nz + radius;
  for (const c of colliders) {
    if (maxX > c.minX && minX < c.maxX &&
        maxY > c.minY && minY < c.maxY &&
        maxZ > c.minZ && minZ < c.maxZ) return false;
  }
  return true;
}

function groundHeightAt(nx, nz, fromY, radius) {
  let best = 0;
  const r = radius * 0.8;
  for (const c of colliders) {
    if (nx + r < c.minX || nx - r > c.maxX) continue;
    if (nz + r < c.minZ || nz - r > c.maxZ) continue;
    const top = c.maxY;
    if (top <= fromY + 0.05 && top > best) best = top;
  }
  return best;
}

function stepPhysics(state, moveInput, dt, crouching) {
  const yaw = state.yaw;
  const fx = -Math.sin(yaw), fz = -Math.cos(yaw);
  const rx = Math.cos(yaw), rz = -Math.sin(yaw);
  let mvX = rx * moveInput.moveX + fx * (-moveInput.moveY);
  let mvZ = rz * moveInput.moveX + fz * (-moveInput.moveY);
  const mlen = Math.hypot(mvX, mvZ);
  if (mlen > 1) { mvX /= mlen; mvZ /= mlen; }
  const speed = crouching ? PLAYER_CROUCH_SPEED : PLAYER_SPEED;
  const step = speed * dt;
  const nx = state.x + mvX * step;
  const nz = state.z + mvZ * step;
  const curHeight = crouching ? CROUCH_HEIGHT : PLAYER_HEIGHT;
  if (canExistAt(nx, state.z, state.y, PLAYER_RADIUS, curHeight)) state.x = nx;
  if (canExistAt(state.x, nz, state.y, PLAYER_RADIUS, curHeight)) state.z = nz;

  state.vy += GRAVITY * dt;
  let ny = state.y + state.vy * dt;
  const groundY = groundHeightAt(state.x, state.z, state.y, PLAYER_RADIUS);
  if (ny <= groundY) {
    ny = groundY; state.vy = 0; state.onGround = true;
  } else {
    state.onGround = false;
  }
  state.y = ny;
}

function hasLineOfSight(fromX, fromZ, fromY, toX, toZ, toY) {
  const dx = toX - fromX, dy = toY - fromY, dz = toZ - fromZ;
  const dist = Math.hypot(dx, dy, dz);
  if (dist < 0.001) return true;
  const ndx = dx/dist, ndy = dy/dist, ndz = dz/dist;
  for (const c of colliders) {
    let tmin = 0, tmax = dist;
    // X
    if (Math.abs(ndx) < 1e-8) { if (fromX < c.minX || fromX > c.maxX) continue; }
    else {
      let t1 = (c.minX - fromX) / ndx, t2 = (c.maxX - fromX) / ndx;
      if (t1 > t2) [t1, t2] = [t2, t1];
      tmin = Math.max(tmin, t1); tmax = Math.min(tmax, t2);
      if (tmin > tmax) continue;
    }
    // Y
    if (Math.abs(ndy) < 1e-8) { if (fromY < c.minY || fromY > c.maxY) continue; }
    else {
      let t1 = (c.minY - fromY) / ndy, t2 = (c.maxY - fromY) / ndy;
      if (t1 > t2) [t1, t2] = [t2, t1];
      tmin = Math.max(tmin, t1); tmax = Math.min(tmax, t2);
      if (tmin > tmax) continue;
    }
    // Z
    if (Math.abs(ndz) < 1e-8) { if (fromZ < c.minZ || fromZ > c.maxZ) continue; }
    else {
      let t1 = (c.minZ - fromZ) / ndz, t2 = (c.maxZ - fromZ) / ndz;
      if (t1 > t2) [t1, t2] = [t2, t1];
      tmin = Math.max(tmin, t1); tmax = Math.min(tmax, t2);
      if (tmin > tmax) continue;
    }
    if (tmin >= 0 && tmin < dist - 0.2) return false;
  }
  return true;
}

/* ============================================================
   КОМНАТЫ
   ============================================================ */
const rooms = new Map();

function genRoomCode() {
  const chars = 'abcdefghjkmnpqrstuvwxyz23456789';
  let s = '';
  for (let i = 0; i < 4; i++) s += chars[Math.floor(Math.random() * chars.length)];
  return s;
}

function createPlayerState(spawnX, spawnZ, yaw) {
  return {
    x: spawnX, y: 0, z: spawnZ,
    vy: 0, yaw: yaw, pitch: 0,
    hp: 100, alive: true, onGround: true,
    weapon: 'rifle',
    ammo: { rifle: 30, shotgun: 8, sniper: 5, knife: 1 },
    grenades: 1,
    isReloading: false, reloadEndTime: 0,
    isCrouching: false,
    lastShotTime: 0,
    score: 0,
    deaths: 0,
    kills: 0,
    input: { moveX: 0, moveY: 0, fire: false, jump: false, crouch: false, weapon: 'rifle' },
  };
}

function createRoom(code, hostWs, hostName, mode, targetKills) {
  const room = {
    code,
    host: {
      ws: hostWs,
      name: hostName,
      state: createPlayerState(0, 25, Math.PI),
    },
    guest: null,
    mode,
    targetKills,
    started: false,
    winner: null,
    tickInterval: null,
    tick: 0,
  };
  rooms.set(code, room);
  return room;
}

function broadcast(room, msg) {
  const str = JSON.stringify(msg);
  if (room.host && room.host.ws.readyState === WebSocket.OPEN) room.host.ws.send(str);
  if (room.guest && room.guest.ws.readyState === WebSocket.OPEN) room.guest.ws.send(str);
}

function sendTo(player, msg) {
  if (player && player.ws.readyState === WebSocket.OPEN) {
    player.ws.send(JSON.stringify(msg));
  }
}

function startGame(room) {
  if (!room.host || !room.guest) return;
  room.started = true;
  room.tick = 0;
  room.winner = null;

  // Сброс состояний
  Object.assign(room.host.state, createPlayerState(0, 25, Math.PI));
  Object.assign(room.guest.state, createPlayerState(0, -25, 0));

  broadcast(room, {
    t: 'start',
    hostName: room.host.name,
    guestName: room.guest.name,
    targetKills: room.targetKills,
    mode: room.mode,
  });

  room.tickInterval = setInterval(() => {
    try {
      tickRoom(room);
    } catch (e) {
      console.error('tick error', e);
    }
  }, TICK_MS);
}

function endGame(room, winnerName) {
  if (room.tickInterval) { clearInterval(room.tickInterval); room.tickInterval = null; }
  room.started = false;
  room.winner = winnerName;
  broadcast(room, { t: 'end', winner: winnerName });
}

function respawnPlayer(room, playerState, spawnX, spawnZ, yaw) {
  playerState.x = spawnX; playerState.y = 0; playerState.z = spawnZ;
  playerState.vy = 0; playerState.yaw = yaw; playerState.pitch = 0;
  playerState.hp = 100;
  playerState.alive = true;
  playerState.onGround = true;
  playerState.ammo = { rifle: 30, shotgun: 8, sniper: 5, knife: 1 };
  playerState.grenades = 1;
  playerState.isReloading = false;
  playerState.isCrouching = false;
}

/* ============================================================
   ТИК КОМНАТЫ
   ============================================================ */
function tickRoom(room) {
  if (!room.started || room.winner) return;
  room.tick++;
  const dt = TICK_MS / 1000;

  const hostState = room.host.state;
  const guestState = room.guest ? room.guest.state : null;
  if (!guestState) return;

  // Обновляем физику для живых
  if (hostState.alive) {
    const inp = hostState.input;
    stepPhysics(hostState, inp, dt, inp.crouch);
    if (inp.jump && hostState.onGround) {
      hostState.vy = JUMP_VELOCITY;
      hostState.onGround = false;
    }
    // Перезарядка
    if (hostState.isReloading && Date.now() >= hostState.reloadEndTime) {
      hostState.isReloading = false;
      hostState.ammo[hostState.weapon] = WEAPON_STATS[hostState.weapon].magSize;
    }
  }
  if (guestState.alive) {
    const inp = guestState.input;
    stepPhysics(guestState, inp, dt, inp.crouch);
    if (inp.jump && guestState.onGround) {
      guestState.vy = JUMP_VELOCITY;
      guestState.onGround = false;
    }
    if (guestState.isReloading && Date.now() >= guestState.reloadEndTime) {
      guestState.isReloading = false;
      guestState.ammo[guestState.weapon] = WEAPON_STATS[guestState.weapon].magSize;
    }
  }

  // Проверка стрельбы
  checkShooting(room, hostState, guestState, 'host');
  checkShooting(room, guestState, hostState, 'guest');

  // Снапшот для обоих
  sendTo(room.host, {
    t: 'state',
    you: serializeState(hostState),
    enemy: serializeState(guestState),
    score: { host: hostState.score, guest: guestState.score },
    tick: room.tick,
  });
  sendTo(room.guest, {
    t: 'state',
    you: serializeState(guestState),
    enemy: serializeState(hostState),
    score: { host: hostState.score, guest: guestState.score },
    tick: room.tick,
  });
}

function serializeState(s) {
  return {
    x: Math.round(s.x * 100) / 100,
    y: Math.round(s.y * 100) / 100,
    z: Math.round(s.z * 100) / 100,
    yaw: Math.round(s.yaw * 1000) / 1000,
    pitch: Math.round(s.pitch * 1000) / 1000,
    hp: s.hp,
    alive: s.alive,
    weapon: s.weapon,
    ammo: s.ammo[s.weapon],
    isCrouching: s.isCrouching,
    isReloading: s.isReloading,
  };
}

function checkShooting(room, shooter, target, shooterId) {
  if (!shooter.alive || !shooter.input.fire) return;
  if (shooter.isReloading) return;

  const w = shooter.weapon;
  const stats = WEAPON_STATS[w];
  const now = Date.now();
  if (now - shooter.lastShotTime < stats.fireRate) return;

  // Проверка патронов
  if (w !== 'knife' && shooter.ammo[w] <= 0) {
    // Авто-перезарядка
    if (!shooter.isReloading) {
      shooter.isReloading = true;
      shooter.reloadEndTime = now + stats.reloadTime;
    }
    return;
  }

  // Для ножа — проверка дистанции и угла
  if (w === 'knife') {
    const dx = target.x - shooter.x;
    const dz = target.z - shooter.z;
    const dist = Math.hypot(dx, dz);
    if (dist > stats.range + 1.0) return;

    const forward = getForward(shooter.yaw, shooter.pitch);
    const toTargetFlat = { x: dx, z: dz };
    const tlen = Math.hypot(toTargetFlat.x, toTargetFlat.z);
    if (tlen > 0.01) {
      toTargetFlat.x /= tlen; toTargetFlat.z /= tlen;
      const fwdFlatLen = Math.hypot(forward.x, forward.z);
      const fwdFlat = { x: forward.x / fwdFlatLen, z: forward.z / fwdFlatLen };
      const dot = toTargetFlat.x * fwdFlat.x + toTargetFlat.z * fwdFlat.z;
      const angle = Math.acos(Math.max(-1, Math.min(1, dot)));
      if (angle > KNIFE_ANGLE && dist >= 1.5) return;
    }
    if (!target.alive) return;

    shooter.lastShotTime = now;
    // Ваншот
    target.hp = 0;
    target.alive = false;
    shooter.score++;
    shooter.kills++;
    target.deaths++;

    const msg = {
      t: 'kill',
      killer: shooterId,
      victim: shooterId === 'host' ? 'guest' : 'host',
      weapon: 'knife',
      head: false,
    };
    broadcast(room, msg);

    if (shooter.score >= room.targetKills) {
      endGame(room, shooterId === 'host' ? room.host.name : room.guest.name);
      return;
    }
    // Респавн жертвы через 3с
    setTimeout(() => {
      if (room.winner) return;
      if (shooterId === 'host') respawnPlayer(room, target, 0, -25, 0);
      else respawnPlayer(room, target, 0, 25, Math.PI);
    }, 3000);
    return;
  }

  // Для огнестрела — raycast по позиции цели
  shooter.lastShotTime = now;
  shooter.ammo[w]--;

  // Оружие стреляет из груди стрелка
  const originY = shooter.y + (shooter.isCrouching ? CROUCH_HEIGHT : PLAYER_HEIGHT) - 0.2;
  const origin = { x: shooter.x, y: originY, z: shooter.z };
  const forward = getForward(shooter.yaw, shooter.pitch);

  // Raycast по коллайдерам и цели
  const targetHits = [
    { y: target.y + 0.4, part: 'body' },  // торс
    { y: target.y + 1.9, part: 'head' },  // голова
  ];

  let bestHit = null;
  let bestDist = Infinity;

  for (const th of targetHits) {
    if (!target.alive) continue;
    const tx = target.x, ty = th.y, tz = target.z;
    const dx = tx - origin.x, dy = ty - origin.y, dz = tz - origin.z;
    const dist = Math.hypot(dx, dy, dz);

    // Проверка "попал ли луч в точку" — если точка находится в пределах ~0.5м от линии
    const dot = dx * forward.x + dy * forward.y + dz * forward.z;
    if (dot < 0) continue;
    const perpX = dx - forward.x * dot;
    const perpY = dy - forward.y * dot;
    const perpZ = dz - forward.z * dot;
    const perpDist = Math.hypot(perpX, perpY, perpZ);

    const hitRadius = th.part === 'head' ? 0.4 : 0.6;
    if (perpDist < hitRadius && dot < stats.range) {
      // Проверка LOS
      if (!hasLineOfSight(origin.x, origin.z, origin.y, tx, tz, ty)) continue;
      if (dot < bestDist) {
        bestDist = dot;
        bestHit = th;
      }
    }
  }

  if (!bestHit) return;

  const isHead = bestHit.part === 'head';
  const dmg = isHead ? stats.damageHead : stats.damageBody;

  target.hp -= dmg;
  if (target.hp <= 0) {
    target.hp = 0;
    target.alive = false;
    shooter.score++;
    shooter.kills++;
    target.deaths++;
    broadcast(room, {
      t: 'kill',
      killer: shooterId,
      victim: shooterId === 'host' ? 'guest' : 'host',
      weapon: w,
      head: isHead,
    });
    if (shooter.score >= room.targetKills) {
      endGame(room, shooterId === 'host' ? room.host.name : room.guest.name);
      return;
    }
    setTimeout(() => {
      if (room.winner) return;
      if (shooterId === 'host') respawnPlayer(room, target, 0, -25, 0);
      else respawnPlayer(room, target, 0, 25, Math.PI);
    }, 3000);
  }

  broadcast(room, {
    t: 'hit',
    victim: shooterId === 'host' ? 'guest' : 'host',
    dmg: dmg,
    head: isHead,
  });
}

function getForward(yaw, pitch) {
  const cp = Math.cos(pitch);
  return {
    x: -Math.sin(yaw) * cp,
    y: Math.sin(pitch),
    z: -Math.cos(yaw) * cp,
  };
}

/* ============================================================
   WEBSOCKET СЕРВЕР
   ============================================================ */
const server = http.createServer((req, res) => {
  // Health check для Render
  res.writeHead(200, { 'Content-Type': 'text/plain' });
  res.end('Zaharka Shooter Server OK');
});

const wss = new WebSocket.Server({ server });

wss.on('connection', (ws) => {
  ws.player = { room: null, id: null };
  console.log('Client connected');

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }
    handleMessage(ws, msg);
  });

  ws.on('close', () => {
    const room = ws.player.room;
    if (!room) return;
    const id = ws.player.id;
    if (id === 'host') {
      // Хост отвалился — комната закрывается
      broadcast(room, { t: 'hostLeft' });
      if (room.tickInterval) clearInterval(room.tickInterval);
      rooms.delete(room.code);
    } else if (id === 'guest') {
      // Гость отвалился — хост может ждать нового или завершить
      broadcast(room, { t: 'guestLeft' });
      room.guest = null;
      if (room.tickInterval) { clearInterval(room.tickInterval); room.tickInterval = null; }
      room.started = false;
    }
    console.log('Client disconnected');
  });
});

function handleMessage(ws, msg) {
  switch (msg.t) {
    case 'create': {
      const mode = msg.mode || 13;
      const targetKills = mode === 'blood' ? 1 : parseInt(mode);
      let code;
      do { code = genRoomCode(); } while (rooms.has(code));
      const room = createRoom(code, ws, msg.name || 'Хост', mode, targetKills);
      ws.player.room = room;
      ws.player.id = 'host';
      sendTo(room.host, { t: 'created', code, name: room.host.name });
      break;
    }
    case 'join': {
      const code = String(msg.code || '').toLowerCase();
      const room = rooms.get(code);
      if (!room) { sendTo(ws ? { ws } : null, { t: 'error', msg: 'Комната не найдена' }); 
        // Отправляем напрямую
        if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ t: 'error', msg: 'Комната не найдена' }));
        return;
      }
      if (room.guest) { if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ t: 'error', msg: 'Комната занята' })); return; }
      room.guest = {
        ws,
        name: msg.name || 'Гость',
        state: createPlayerState(0, -25, 0),
      };
      ws.player.room = room;
      ws.player.id = 'guest';
      sendTo(room.guest, { t: 'joined', code, hostName: room.host.name, guestName: room.guest.name });
      sendTo(room.host, { t: 'guestJoined', name: room.guest.name });
      startGame(room);
      break;
    }
    case 'input': {
      const room = ws.player.room;
      if (!room) return;
      const playerState = ws.player.id === 'host' ? room.host.state : room.guest?.state;
      if (!playerState) return;
      const inp = msg.input || {};
      playerState.input.moveX = clamp(inp.moveX ?? 0, -1, 1);
      playerState.input.moveY = clamp(inp.moveY ?? 0, -1, 1);
      playerState.input.fire = !!inp.fire;
      playerState.input.jump = !!inp.jump;
      playerState.input.crouch = !!inp.crouch;
      playerState.yaw = inp.yaw ?? playerState.yaw;
      playerState.pitch = clamp(inp.pitch ?? playerState.pitch, -Math.PI/2 + 0.1, Math.PI/2 - 0.1);
      playerState.isCrouching = !!inp.crouch;
      if (inp.weapon && ['rifle','shotgun','sniper','knife'].includes(inp.weapon)) {
        if (playerState.weapon !== inp.weapon) {
          playerState.weapon = inp.weapon;
          playerState.isReloading = false;
        }
      }
      if (inp.reload && !playerState.isReloading && playerState.weapon !== 'knife') {
        const w = playerState.weapon;
        const stats = WEAPON_STATS[w];
        if (playerState.ammo[w] < stats.magSize) {
          playerState.isReloading = true;
          playerState.reloadEndTime = Date.now() + stats.reloadTime;
        }
      }
      break;
    }
    case 'leave': {
      const room = ws.player.room;
      if (!room) return;
      // Пометить как forfeit (поражение)
      const id = ws.player.id;
      if (id === 'host' && room.guest) {
        room.host.state.score = 0; // Обнулять не нужно
        endGame(room, room.guest.name);
        broadcast(room, { t: 'forfeit', by: 'host' });
      } else if (id === 'guest' && room.host) {
        endGame(room, room.host.name);
        broadcast(room, { t: 'forfeit', by: 'guest' });
      }
      break;
    }
    case 'ping': {
      if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ t: 'pong', ts: msg.ts }));
      break;
    }
  }
}

function clamp(v, min, max) { return Math.max(min, Math.min(max, v)); }

server.listen(PORT, () => {
  console.log(`Zaharka Shooter server listening on port ${PORT}`);
});
