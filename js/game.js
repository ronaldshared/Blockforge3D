"use strict";
const C = document.querySelector('#game');
const G = C.getContext('webgl', { antialias: false });
if (!G) { document.body.innerHTML = '<h1>WebGL no disponible</h1>'; throw Error('WebGL'); }
const $ = s => document.querySelector(s);

const W = 192, H = 60, D = 192, CS = 16, CV = 3;
const T = new Uint8Array(W * H * D);
const WL = new Uint8Array(W * H * D);
const I = (x, y, z) => x + W * (z + D * y);
const inside = (x, y, z) => x >= 0 && z >= 0 && y >= 0 && x < W && z < D && y < H;
const get = (x, y, z) => inside(x, y, z) ? T[I(x, y, z)] : 0;
const set = (x, y, z, v) => {
  if (inside(x, y, z)) {
    T[I(x, y, z)] = v;
    if (v !== 11) WL[I(x, y, z)] = 0;
    else if (v === 11 && WL[I(x, y, z)] === 0) WL[I(x, y, z)] = 8;
    mapDirty = true;
  }
};

// Paleta de colores de bloques
const B = [
  0, [0.3, 0.7, 0.3], [0.5, 0.3, 0.15], [0.5, 0.5, 0.5], [0.4, 0.25, 0.1], [0.1, 0.6, 0.1], 
  [0.8, 0.8, 0.5], [0.2, 0.6, 1.0], [0.6, 0.2, 0.8], [0.7, 0.5, 0.2], [1.0, 0.8, 0.2], [0.2, 0.6, 1.0], 
  [0.2, 0.2, 0.2], [0.8, 0.9, 1.0], [0.7, 0.3, 0.3], [0.6, 0.6, 0.6], [0.2, 0.8, 0.2], [0.9, 0.1, 0.1], 
  [0.9, 0.8, 0.1], [1.0, 1.0, 1.0], [0.7, 0.2, 0.2], [0.8, 0.75, 0.3], [0.3, 0.2, 0.1]
];
const N = ['Aire', 'Hierba', 'Tierra', 'Piedra', 'Madera', 'Hojas', 'Arena', 'Cristal', 'Gema', 'Tablón', 'Lámpara', 'Agua', 'Base', 'Vidrio', 'Ladrillo', 'P. Lisa', 'Pasto A.', 'Flor R.', 'Flor A.', 'Nube', 'Hojas R.', 'Heno', 'Cultivo'];

// Íconos mejorados (emojis)
const IC = ['', '🟩', '🟫', '🪨', '🪵', '🌳', '🟨', '💠', '🔮', '🪚', '💡', '💧', '⬛', '🪟', '🧱', '⬜', '🌿', '🌹', '🌻', '☁️', '🍁', '🌾', '🌱'];
const ANIMAL_NAMES = ['Oveja', 'Cerdito', 'Vaca', 'Gallina', 'Caballo', 'Perrito', 'Cheta', 'Tigre', 'Elefante', 'Jirafa', 'Conejo'];

let seed = 1, time = .25, run = false, pause = true, fps = 0, sel = 0;
let animals = [], chunks = new Map(), dirty = new Set();
let action = 0, captured = null, hudVisible = true;
let _rayDirty = true, _lastRay = null;
let _tipText = '', _tipUntil = 0;
let waterQueue = new Set();
let mapDirty = true;
let particles = [];

const mapCanvas = $('#minimap');
const mapCtx = mapCanvas ? mapCanvas.getContext('2d') : null;

function showTip(text, ms) { _tipText = text; _tipUntil = performance.now() + (ms || 1200); }

const src = { remove: { mouse: 0, key: 0, touch: 0 }, place: { mouse: 0, key: 0, touch: 0 } };
const wantRemove = () => src.remove.mouse || src.remove.key || src.remove.touch;
const wantPlace = () => src.place.mouse || src.place.key || src.place.touch;

const touch = { moveX: 0, moveY: 0, jump: 0, down: 0, sprint: 0, moveId: null, lookId: null, lookX: 0, lookY: 0 };
const coarse = matchMedia('(pointer:coarse)').matches;
const hot = [1, 2, 3, 4, 6, 11, 13, 16, 17];
const P = { x: 96, y: 20, z: 96, yaw: 0, pitch: 0, vy: 0, r: .28, h: 1.75, ground: 0, fly: 0, spawn: [96, 20, 96] };

function hash(x, z, s) {
  let n = (x * 374761393 + z * 668265263 + s * 69069) | 0;
  n = Math.imul(n ^ (n >>> 13), 1274126177);
  return ((n ^ (n >>> 16)) >>> 0) / 4294967295;
}
function seedN(s) {
  let n = 2166136261;
  for (const c of s) n = Math.imul(n ^ c.charCodeAt(0), 16777619);
  return n | 0;
}
const plains = [[96, 96, 40, 20], [40, 40, 30, 20], [152, 40, 30, 21], [40, 152, 30, 19], [152, 152, 30, 21]];
function zone(x, z) {
  for (const q of plains) { let d = Math.hypot(x - q[0], z - q[1]); if (d < q[2]) return [d, ...q]; }
  return null;
}
function surface(x, z) {
  for (let y = H - 1; y >= 0; y--) {
    let b = get(x, y, z);
    if (b && b !== 11 && b !== 13 && b !== 16 && b !== 17 && b !== 18 && b !== 19 && b !== 21 && b !== 22) return y;
  }
  return 0;
}

function mountainHeight(x, z) {
  let m1 = Math.max(0, 1 - Math.hypot(x - 40, z - 40) / 50);
  let m2 = Math.max(0, 1 - Math.hypot(x - 160, z - 160) / 60);
  return Math.max(m1, m2) * 18;
}

// --- CONSTRUCCIONES ---

function buildHouse(bx, bz, stories, radius) {
  let gy = surface(bx, bz);
  let dirX = bx < 96 ? 1 : -1;
  let dirZ = bz < 96 ? 1 : -1;

  for (let x = bx - radius - 3; x <= bx + radius + 3; x++) {
    for (let z = bz - radius - 3; z <= bz + radius + 15; z++) {
      for (let y = gy + 1; y < gy + 20; y++) set(x, y, z, 0);
      for (let y = gy; y >= Math.min(0, gy - 5); y--) if (get(x, y, z) === 0) set(x, y, z, 2);
      set(x, gy, z, 1);
    }
  }
  for (let x = bx - radius; x <= bx + radius; x++) {
    for (let z = bz - radius; z <= bz + radius; z++) {
      set(x, gy, z, 3); set(x, gy + 1, z, 3);
    }
  }
  for (let x = bx - radius + 1; x <= bx + radius - 1; x++) {
    for (let z = bz - radius + 1; z <= bz + radius - 1; z++) {
      set(x, gy + 1, z, 9);
    }
  }
  let wallHeight = stories * 3;
  for (let y = gy + 2; y <= gy + 1 + wallHeight; y++) {
    for (let x = bx - radius; x <= bx + radius; x++) {
      for (let z = bz - radius; z <= bz + radius; z++) {
        if (x === bx - radius || x === bx + radius || z === bz - radius || z === bz + radius) {
          let isCorner = (x === bx - radius || x === bx + radius) && (z === bz - radius || z === bz + radius);
          if (isCorner) set(x, y, z, 4);
          else {
            let isWindowFloor = (y - (gy + 2)) % 3 === 1;
            if (isWindowFloor) {
              if ((x === bx - radius || x === bx + radius) && z > bz - radius + 1 && z < bz + radius - 1) set(x, y, z, 13);
              else if ((z === bz - radius || z === bz + radius) && x > bx - radius + 1 && x < bx + radius - 1) set(x, y, z, 13);
              else set(x, y, z, 9);
            } else set(x, y, z, 9);
          }
        }
      }
    }
  }
  let doorZ = bz + (dirZ > 0 ? radius : -radius);
  let doorX = bx + (dirX > 0 ? radius : -radius);
  if (Math.abs(bx - 96) > Math.abs(bz - 96)) {
    for (let y = gy + 2; y <= gy + 3; y++) set(doorX, y, bz, 0);
    set(bx + (dirX > 0 ? radius - 1 : -radius + 1), gy + 3, bz, 10);
  } else {
    for (let y = gy + 2; y <= gy + 3; y++) set(bx, y, doorZ, 0);
    set(bx, gy + 3, bz + (dirZ > 0 ? radius - 1 : -radius + 1), 10);
  }
  let roofY = gy + 2 + wallHeight;
  for (let layer = 0; layer <= radius; layer++) {
    let y = roofY + layer;
    let size = radius - layer;
    for (let x = bx - size; x <= bx + size; x++) {
      for (let z = bz - size; z <= bz + size; z++) {
        set(x, y, z, 15);
      }
    }
  }
  let chimX = bx + (radius - 2), chimZ = bz - (radius - 2);
  for (let y = roofY; y <= roofY + radius + 2; y++) set(chimX, y, chimZ, 14);
  
  for (let x = bx - radius - 2; x <= bx + radius + 2; x++) {
    for (let z = bz + (dirZ > 0 ? radius + 2 : -radius - 14); z <= bz + (dirZ > 0 ? radius + 14 : -radius - 2); z++) {
      if (get(x, gy, z) === 1 && get(x, gy + 1, z) === 0) {
        let r = hash(x, z, seed + 11);
        if (r < 0.15) set(x, gy + 1, z, 17);
        else if (r < 0.30) set(x, gy + 1, z, 18);
        else if (r < 0.50) set(x, gy + 1, z, 16);
      }
    }
  }
}

function buildFarm(bx, bz) {
  let gy = surface(bx, bz);
  // 1. Aplanar terreno de la granja
  for (let x = bx - 20; x <= bx + 20; x++) {
    for (let z = bz - 20; z <= bz + 20; z++) {
      for (let y = gy + 1; y < gy + 15; y++) set(x, y, z, 0);
      set(x, gy, z, 1);
    }
  }

  // 2. Casa de Campo Simple
  buildHouse(bx - 10, bz - 10, 1, 4);

  // 3. Pozo de Agua
  for (let x = bx; x <= bx + 3; x++) {
    for (let z = bz; z <= bz + 3; z++) {
      if (x === bx || x === bx + 3 || z === bz || z === bz + 3) {
        set(x, gy, z, 3); set(x, gy + 1, z, 3);
      } else {
        set(x, gy, z, 11); // Agua
      }
    }
  }
  // Techo del pozo
  for (let x = bx - 1; x <= bx + 4; x++) for (let z = bz - 1; z <= bz + 4; z++) set(x, gy + 4, z, 9);
  set(bx, gy + 2, bz, 4); set(bx + 3, gy + 2, bz, 4);
  set(bx, gy + 2, bz + 3, 4); set(bx + 3, gy + 2, bz + 3, 4);

  // 4. Establo de Caballos (Grande)
  let sx = bx + 8, sz = bz - 15;
  for (let x = sx - 6; x <= sx + 6; x++) {
    for (let z = sz - 6; z <= sz + 6; z++) {
      if (x === sx - 6 || x === sx + 6 || z === sz - 6 || z === sz + 6) {
        if ((x + z) % 2 === 0) set(x, gy + 1, z, 4); // Vallas
      }
    }
  }
  // Techo del establo
  for (let x = sx - 7; x <= sx + 7; x++) for (let z = sz - 7; z <= sz + 7; z++) set(x, gy + 5, z, 15);
  // Bloques de heno
  set(sx - 3, gy + 1, sz - 3, 21); set(sx + 3, gy + 1, sz + 3, 21);

  // 5. Gallinero
  let cx = bx + 12, cz = bz + 5;
  for (let x = cx - 4; x <= cx + 4; x++) {
    for (let z = cz - 4; z <= cz + 4; z++) {
      if (x === cx - 4 || x === cx + 4 || z === cz - 4 || z === cz + 4) {
        if ((x + z) % 2 === 0) set(x, gy + 1, z, 4);
      }
    }
  }
  for (let x = cx - 5; x <= cx + 5; x++) for (let z = cz - 5; z <= cz + 5; z++) set(x, gy + 3, z, 9);
  // Gallinas
  for(let i=0; i<3; i++) {
      let ax = cx + (Math.random()-0.5)*4, az = cz + (Math.random()-0.5)*4;
      animals.push({ x: ax, y: gy+2, z: az, type: 3, dir: Math.random()*6.28, to: Math.random()*6.28, state: 0, t: 2, home: [ax, az], phase: i });
  }

  // 6. Pocilga (Cerdos)
  let px = bx - 12, pz = bz + 10;
  for (let x = px - 5; x <= px + 5; x++) {
    for (let z = pz - 5; z <= pz + 5; z++) {
      if (x === px - 5 || x === px + 5 || z === pz - 5 || z === pz + 5) {
        if ((x + z) % 2 === 0) set(x, gy + 1, z, 4);
      } else {
        set(x, gy, z, 2); // Tierra (lodo)
      }
    }
  }
  // Cerdos
  for(let i=0; i<3; i++) {
      let ax = px + (Math.random()-0.5)*6, az = pz + (Math.random()-0.5)*6;
      animals.push({ x: ax, y: gy+1, z: az, type: 1, dir: Math.random()*6.28, to: Math.random()*6.28, state: 0, t: 2, home: [ax, az], phase: i });
  }

  // 7. Molino de Viento
  let wx = bx + 5, wz = bz + 12;
  for (let y = gy + 1; y <= gy + 8; y++) {
    for (let x = wx - 2; x <= wx + 2; x++) {
      for (let z = wz - 2; z <= wz + 2; z++) {
        if (x === wx - 2 || x === wx + 2 || z === wz - 2 || z === wz + 2) {
          set(x, y, z, 9);
        }
      }
    }
  }
  // Aspas (simples)
  set(wx, gy + 9, wz, 4);
  set(wx + 1, gy + 9, wz, 4); set(wx - 1, gy + 9, wz, 4);
  set(wx, gy + 9, wz + 1, 4); set(wx, gy + 9, wz - 1, 4);
  
  // 8. Campos de Cultivo (Hileras de pasto/trigo)
  for (let x = bx - 15; x <= bx - 5; x++) {
    for (let z = bz - 5; z <= bz + 5; z++) {
      if (x % 2 === 0) {
        set(x, gy, z, 2); // Surco de tierra
        if (Math.random() < 0.8) set(x, gy + 1, z, 22); // Cultivo
      }
    }
  }
}

function generate(s) {
  T.fill(0); WL.fill(0); particles = []; animals = [];
  seed = seedN(s);
  
  for (let x = 0; x < W; x++) for (let z = 0; z < D; z++) {
    let raw = 16 + Math.sin(x * .025) * 2.0 + Math.cos(z * .022) * 1.8 + (hash(x >> 2, z >> 2, seed) - .5) * .6;
    raw += mountainHeight(x, z);
    let q = zone(x, z);
    if (q) { let [d, cx, cz, r, h] = q, t = Math.min(1, (r - d) / 6); raw = d < r - 6 ? h : raw * (1 - t) + h * t; }
    let h = Math.floor(raw);
    h = Math.min(H - 2, h);
    for (let y = 0; y <= h; y++) set(x, y, z, y === 0 ? 12 : y === h ? 1 : y > h - 4 ? 2 : 3);
  }
  
  for (let i = 0; i < 15; i++) {
    let lx = 16 + hash(i, 7, seed) * (W - 32), lz = 16 + hash(i, 8, seed) * (D - 32);
    let r = 6 + hash(i, 9, seed) * 12, ly = surface(lx | 0, lz | 0) - 2;
    for (let dx = -r; dx <= r; dx++) for (let dz = -r; dz <= r; dz++) {
      if (Math.hypot(dx, dz) < r) {
        let x = lx | 0 + dx, z = lz | 0 + dz;
        for (let y = ly - 5; y <= ly; y++) if (inside(x, y, z) && y > 0) set(x, y, z, 11);
      }
    }
  }
  
  for (let gx = 8; gx < W - 8; gx += 9) for (let gz = 8; gz < D - 8; gz += 9) {
    if (zone(gx, gz) || hash(gx, gz, seed) < .5) continue;
    let y = surface(gx, gz);
    if (get(gx, y, gz) === 1) {
      for (let k = 1; k < 6; k++) set(gx, y + k, gz, 4);
      let leafType = hash(gx, gz, seed + 99) > 0.8 ? 20 : 5;
      for (let dx = -2; dx <= 2; dx++) for (let dz = -2; dz <= 2; dz++) for (let dy = 4; dy <= 6; dy++) {
        let dist = Math.abs(dx) + Math.abs(dz) + (dy === 6 ? 1 : 0);
        if (dist <= 3) if (get(gx + dx, y + dy, gz + dz) === 0) set(gx + dx, y + dy, gz + dz, leafType);
      }
    }
  }

  // CONSTRUCCIONES
  buildHouse(20, 20, 2, 7);     // Superior Izquierda (2 pisos)
  buildHouse(172, 172, 3, 10);  // Inferior Derecha (3 pisos)
  buildHouse(172, 20, 2, 8);    // Superior Derecha (2 pisos)
  buildHouse(20, 172, 2, 8);    // Inferior Izquierda (2 pisos)
  
  // Granja en el sector centro-derecha
  buildFarm(140, 96);
  
  // Vegetación natural
  for (let px = 0; px < W; px += 4) for (let pz = 0; pz < D; pz += 4) {
    let isPatch = hash(px >> 2, pz >> 2, seed + 42) > 0.75;
    if (isPatch) {
      for (let x = px; x < Math.min(W, px + 4); x++) {
        for (let z = pz; z < Math.min(D, pz + 4); z++) {
          let y = surface(x, z);
          if (get(x, y, z) === 1 && get(x, y+1, z) === 0) {
            let r = hash(x, z, seed + 7);
            if (r < 0.05) set(x, y+1, z, 16);
            else if (r < 0.06) set(x, y+1, z, 17);
            else if (r < 0.07) set(x, y+1, z, 18);
          }
        }
      }
    }
  }

  for (let x = 0; x < W; x += 6) for (let z = 0; z < D; z += 6) {
    if (hash(x, z, seed + 55) > 0.8) {
      for (let dx = 0; dx < 6; dx++) for (let dz = 0; dz < 6; dz++) {
        set(x + dx, 45, z + dz, 19);
      }
    }
  }

  // Fauna inicial (fuera de las construcciones)
  for (let i = 0; i < 40; i++) {
    let x = 30 + hash(i, 2, seed) * (W - 60), z = 30 + hash(i, 3, seed) * (D - 60), y = surface(x | 0, z | 0) + 1;
    animals.push({ x, y, z, type: i % 11, dir: hash(i, 4, seed) * 6.28, to: hash(i, 5, seed) * 6.28, state: 0, t: 1 + hash(i, 6, seed) * 4, home: [x, z], phase: i });
  }
  
  P.x = P.z = 96; P.y = surface(96, 96) + 1.01; P.spawn = [P.x, P.y, P.z];
  chunks.clear(); dirty.clear();
  for (let x = 0; x < W / CS; x++) for (let z = 0; z < D / CS; z++) dirty.add(x + ',' + z);
  _rayDirty = true; _hud.hbSel = -1; mapDirty = true;
}

const VS = `attribute vec3 p; attribute vec4 c; uniform mat4 m; varying vec4 v; void main(){ gl_Position = m * vec4(p, 1.0); v = c; }`;
const FS = `precision mediump float; varying vec4 v; uniform float s; void main(){ gl_FragColor = vec4(v.rgb * s, v.a); }`;
function sh(t, s) {
  let o = G.createShader(t); G.shaderSource(o, s); G.compileShader(o);
  if (!G.getShaderParameter(o, G.COMPILE_STATUS)) throw Error(G.getShaderInfoLog(o));
  return o;
}
const PR = G.createProgram();
G.attachShader(PR, sh(G.VERTEX_SHADER, VS));
G.attachShader(PR, sh(G.FRAGMENT_SHADER, FS));
G.linkProgram(PR); G.useProgram(PR);
const ap = G.getAttribLocation(PR, 'p'), ac = G.getAttribLocation(PR, 'c');
const um = G.getUniformLocation(PR, 'm'), us = G.getUniformLocation(PR, 's');
G.enableVertexAttribArray(ap); G.enableVertexAttribArray(ac);

const faces = [
  [[0, 0, -1], [0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]],
  [[0, 0, 1], [1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1]],
  [[-1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1]],
  [[1, 0, 0], [1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0]],
  [[0, -1, 0], [0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0]],
  [[0, 1, 0], [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1]]
];
const faceLight = [0.8, 0.8, 0.8, 0.8, 0.5, 1.0];
const _pcScratch = new Float32Array(4);

function pcInto(b, x, y, z, f) {
  const q = B[b];
  const n = (hash(x * 13 + f, z * 17 + y, seed + b) - .5) * .16;
  const l = (b === 16 || b === 17 || b === 18 || b === 22) ? 1.0 : faceLight[f]; 
  _pcScratch[0] = Math.max(.02, Math.min(1, (q[0] + n) * l));
  _pcScratch[1] = Math.max(.02, Math.min(1, (q[1] + n) * l));
  _pcScratch[2] = Math.max(.02, Math.min(1, (q[2] + n) * l));
  _pcScratch[3] = (b === 11 || b === 19) ? 0.6 : (b === 13 ? 0.4 : 1.0);
}

function mesh(cx, cz) {
  let aO = [], aT = [], x0 = cx * CS, z0 = cz * CS;
  for (let y = 0; y < H; y++) for (let z = z0; z < Math.min(D, z0 + CS); z++) for (let x = x0; x < Math.min(W, x0 + CS); x++) {
    let b = get(x, y, z); if (!b) continue;
    
    if (b === 16 || b === 17 || b === 18 || b === 22) {
      pcInto(b, x, y, z, 0);
      let r = _pcScratch[0], g = _pcScratch[1], bl = _pcScratch[2], a = _pcScratch[3];
      let cx0 = x + 0.5, cz0 = z + 0.5;
      let rBase = r * 0.6, gBase = g * 0.6, blBase = bl * 0.6;

      if (b === 17 || b === 18) {
        let sw = 0.04, sh = 0.4;
        aO.push(cx0-sw, y, cz0-sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y, cz0-sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y+sh, cz0-sw, r, g, bl, a);
        aO.push(cx0-sw, y, cz0-sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y+sh, cz0-sw, r, g, bl, a);
        aO.push(cx0-sw, y+sh, cz0-sw, r, g, bl, a);
        aO.push(cx0-sw, y, cz0+sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y, cz0+sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y+sh, cz0+sw, r, g, bl, a);
        aO.push(cx0-sw, y, cz0+sw, rBase*0.5, gBase*0.5, blBase*0.5, a);
        aO.push(cx0+sw, y+sh, cz0+sw, r, g, bl, a);
        aO.push(cx0-sw, y+sh, cz0+sw, r, g, bl, a);
      }
      
      let offset = (b === 17 || b === 18) ? 0.4 : 0;
      let hh = (b === 17 || b === 18) ? 0.2 : (b === 22 ? 0.6 : 0.4);
      let s = (b === 17 || b === 18) ? 0.12 : (b === 22 ? 0.15 : 0.2);

      aO.push(cx0-s, y+offset, cz0-s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset, cz0+s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset+hh, cz0+s, r, g, bl, a);
      aO.push(cx0-s, y+offset, cz0-s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset+hh, cz0+s, r, g, bl, a);
      aO.push(cx0-s, y+offset+hh, cz0-s, r, g, bl, a);
      
      aO.push(cx0-s, y+offset, cz0+s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset, cz0-s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset+hh, cz0-s, r, g, bl, a);
      aO.push(cx0-s, y+offset, cz0+s, rBase, gBase, blBase, a);
      aO.push(cx0+s, y+offset+hh, cz0-s, r, g, bl, a);
      aO.push(cx0-s, y+offset+hh, cz0+s, r, g, bl, a);
      
      continue;
    }

    for (let fi = 0; fi < 6; fi++) {
      const f = faces[fi], n = f[0];
      let nb = get(x + n[0], y + n[1], z + n[2]);
      if (nb === b && b !== 11 && b !== 13 && b !== 19) continue;
      if (b === 19 && nb === 19) continue;
      
      const q = f[1];
      pcInto(b, x, y, z, fi);
      let target = (b === 11 || b === 13 || b === 19) ? aT : aO;
      for (const k of [0, 1, 2, 0, 2, 3]) {
        target.push(x + q[k * 3], y + q[k * 3 + 1], z + q[k * 3 + 2], _pcScratch[0], _pcScratch[1], _pcScratch[2], _pcScratch[3]);
      }
    }
  }
  let key = cx + ',' + cz;
  let o = chunks.get(key) || { bO: G.createBuffer(), bT: G.createBuffer() };
  o.nO = aO.length / 7; o.nT = aT.length / 7; o.x = cx; o.z = cz;
  G.bindBuffer(G.ARRAY_BUFFER, o.bO); G.bufferData(G.ARRAY_BUFFER, new Float32Array(aO), G.STATIC_DRAW);
  G.bindBuffer(G.ARRAY_BUFFER, o.bT); G.bufferData(G.ARRAY_BUFFER, new Float32Array(aT), G.STATIC_DRAW);
  chunks.set(key, o); dirty.delete(key);
}

function visible() {
  let cx = P.x / CS | 0, cz = P.z / CS | 0;
  for (let x = Math.max(0, cx - CV); x <= Math.min(W / CS - 1, cx + CV); x++)
    for (let z = Math.max(0, cz - CV); z <= Math.min(D / CS - 1, cz + CV); z++) {
      let k = x + ',' + z;
      if (!chunks.has(k) || dirty.has(k)) mesh(x, z);
    }
  return [cx, cz];
}

function mm(a, b) {
  let o = new Float32Array(16);
  for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) for (let k = 0; k < 4; k++) o[c * 4 + r] += a[k * 4 + r] * b[c * 4 + k];
  return o;
}
function proj() {
  let f = 1 / Math.tan(.58), a = C.width / C.height, o = new Float32Array(16);
  o[0] = f / a; o[5] = f; o[10] = -1.001; o[11] = -1; o[14] = -.2; return o;
}
function view() {
  let cy = Math.cos(P.yaw), sy = Math.sin(P.yaw), cp = Math.cos(P.pitch), sp = Math.sin(P.pitch);
  let f = [-sy * cp, sp, -cy * cp], r = [cy, 0, -sy], u = [sy * sp, cp, cy * sp], e = [P.x, P.y + 1.55, P.z];
  let o = new Float32Array([r[0], u[0], -f[0], 0, r[1], u[1], -f[1], 0, r[2], u[2], -f[2], 0, 0, 0, 0, 1]);
  o[12] = -r[0] * e[0] - r[2] * e[2]; o[13] = -u[0] * e[0] - u[1] * e[1] - u[2] * e[2];
  o[14] = f[0] * e[0] + f[1] * e[1] + f[2] * e[2];
  return o;
}
const eb = G.createBuffer();
function box(a, x, y, z, sx, sy, sz, c, yaw = 0) {
  let co = Math.cos(yaw), si = Math.sin(yaw);
  for (const f of faces) {
    let q = f[1];
    for (const k of [0, 1, 2, 0, 2, 3]) {
      let lx = (q[k * 3] - .5) * sx, lz = (q[k * 3 + 2] - .5) * sz;
      a.push(x + lx * co - lz * si, y + q[k * 3 + 1] * sy, z + lx * si + lz * co, c[0], c[1], c[2], 1.0);
    }
  }
}

let _faunaArr = [], _faunaTyped = new Float32Array(65536);
function fauna(m) {
  const a = _faunaArr; a.length = 0;
  for (const e of animals) {
    let w = e.state ? Math.sin(e.phase * 6) * .1 : 0, cs = Math.cos(e.dir), sn = Math.sin(e.dir);
    let part = (ox, oy, oz, sx, sy, sz, c) => box(a, e.x + cs * ox - sn * oz, e.y + oy, e.z + sn * ox + cs * oz, sx, sy, sz, c, e.dir);
    let leg = (ox, oz, h, c, step = 0) => part(ox, step, oz, .15, h, .15, c);
    let eye = (ox, oy, oz) => part(ox, oy, oz, .06, .06, .06, [0, 0, 0]);
    let dark = [.22, .16, .11], white = [.92, .9, .83];

    if (e.type === 0) {
      let c = [.9, .88, .78]; part(0, .42, 0, 1.05, .7, .65, c); part(.62, .58, 0, .48, .5, .48, c);
      for (const q of [[-.35, -.22, w], [.34, -.22, -w], [-.35, .22, -w], [.34, .22, w]]) leg(q[0], q[1], .46, dark, q[2]);
      eye(.78, .65, -.15); eye(.78, .65, .15);
    } else if (e.type === 1) {
      let c = [.94, .53, .61]; part(0, .32, 0, .95, .55, .58, c); part(.55, .42, 0, .45, .42, .46, c);
      part(.82, .46, 0, .18, .2, .3, [.98, .68, .72]);
      for (const q of [[-.3, -.2], [-.3, .2], [.3, -.2], [.3, .2]]) leg(q[0], q[1], .32, [.65, .3, .34]);
      eye(.68, .52, -.15); eye(.68, .52, .15);
    } else if (e.type === 2) {
      let c = [.48, .31, .18]; part(0, .52, 0, 1.12, .78, .64, c); part(.7, .72, 0, .45, .55, .5, c);
      part(.93, .83, 0, .24, .26, .32, [.68, .53, .35]);
      for (const q of [[-.38, -.23], [-.38, .23], [.38, -.23], [.38, .23]]) leg(q[0], q[1], .58, dark, q[0] * w);
      part(-.72, .77, 0, .18, .7, .14, dark); eye(.88, .82, -.15); eye(.88, .82, .15);
      part(.93, 1.1, -.12, .06, .2, .06, [.8, .8, .8]); part(.93, 1.1, .12, .06, .2, .06, [.8, .8, .8]);
    } else if (e.type === 3) {
      let c = [.92, .9, .83]; part(0, .18, 0, .55, .5, .48, c); part(.38, .45, 0, .34, .36, .36, c);
      part(.6, .48, 0, .18, .14, .22, [.95, .62, .15]);
      leg(-.14, -.12, .22, [.75, .5, .12]); leg(-.14, .12, .22, [.75, .5, .12]);
      part(.35, .78, -.13, .08, .2, .08, [.82, .15, .12]); eye(.52, .56, -.12); eye(.52, .56, .12);
    } else if (e.type === 4) {
      let c = [.58, .37, .2]; part(0, .68, 0, 1.35, .85, .62, c); part(.72, 1.05, 0, .48, .72, .46, c);
      part(1.02, 1.28, 0, .44, .46, .42, c);
      for (const q of [[-.45, -.22], [-.45, .22], [.45, -.22], [.45, .22]]) leg(q[0], q[1], .78, dark, q[0] * w);
      part(-.78, .98, 0, .18, .85, .14, [.22, .14, .09]); part(.78, 1.5, 0, .14, .35, .5, [.22, .14, .09]);
      eye(1.18, 1.35, -.2); eye(1.18, 1.35, .2);
    } else if (e.type === 5) {
      let c = [.72, .52, .3]; part(0, .3, 0, .82, .55, .48, c); part(.5, .52, 0, .42, .48, .4, c);
      part(.75, .55, 0, .22, .2, .28, dark);
      for (const q of [[-.26, -.16], [-.26, .16], [.26, -.16], [.26, .16]]) leg(q[0], q[1], .34, dark, q[0] * w);
      part(.42, .88, -.15, .16, .24, .1, dark); part(.42, .88, .15, .16, .24, .1, dark);
      part(-.48, .62, 0, .13, .5, .12, c); eye(.65, .62, -.15); eye(.65, .62, .15);
    } else if (e.type === 6) {
      let c = [.86, .68, .3]; part(0, .42, 0, 1.18, .66, .55, c); part(.68, .65, 0, .42, .46, .4, c);
      part(.94, .66, 0, .24, .2, .3, dark);
      for (const q of [[-.38, -.19], [-.38, .19], [.38, -.19], [.38, .19]]) leg(q[0], q[1], .5, dark, q[0] * w);
      for (let k = -2; k <= 2; k++) part(k * .18, .7, -.285, .08, .18, .04, dark);
      part(-.68, .7, 0, .12, .55, .1, c); eye(.85, .72, -.15); eye(.85, .72, .15);
    } else if (e.type === 7) {
      let c = [.9, .47, .12]; part(0, .48, 0, 1.28, .72, .62, c); part(.72, .75, 0, .48, .5, .46, c);
      part(1.0, .76, 0, .25, .22, .32, white);
      for (const q of [[-.4, -.22], [-.4, .22], [.4, -.22], [.4, .22]]) leg(q[0], q[1], .56, dark, q[0] * w);
      for (let k = -2; k <= 2; k++) { part(k * .2, .7, -.32, .08, .3, .04, dark); part(k * .2, .7, .32, .08, .3, .04, dark); }
      part(-.75, .86, 0, .14, .58, .12, dark); eye(.9, .8, -.18); eye(.9, .8, .18);
    } else if (e.type === 8) {
      let c = [.58, .61, .62]; part(0, .78, 0, 1.65, 1.05, .88, c); part(.95, 1.02, 0, .72, .84, .7, c);
      part(1.37, .7, 0, .2, .9, .22, c); part(1.48, .28, 0, .28, .22, .28, c);
      part(.98, 1.3, -.45, .16, .62, .48, [.7, .72, .73]); part(.98, 1.3, .45, .16, .62, .48, [.7, .72, .73]);
      for (const q of [[-.5, -.3], [-.5, .3], [.5, -.3], [.5, .3]]) leg(q[0], q[1], .82, dark, q[0] * w);
      part(-.9, 1.1, 0, .14, .75, .12, dark); eye(1.25, 1.2, -.3); eye(1.25, 1.2, .3);
    } else if (e.type === 9) {
      let c = [.9, .65, .22]; part(0, 1.05, 0, 1.18, .72, .58, c); part(.58, 1.65, 0, .34, 1.5, .36, c);
      part(.72, 2.42, 0, .48, .48, .42, c);
      for (const q of [[-.38, -.2], [-.38, .2], [.38, -.2], [.38, .2]]) leg(q[0], q[1], 1.1, [.45, .29, .14], q[0] * w);
      for (let k = 0; k < 5; k++) part(-.35 + k * .2, 1.25 + (k % 2) * .35, -.3, .13, .18, .05, [.36, .23, .1]);
      part(.65, 2.72, -.14, .09, .3, .09, dark); part(.65, 2.72, .14, .09, .3, .09, dark);
      eye(.9, 2.5, -.2); eye(.9, 2.5, .2);
    } else {
      let c = [.82, .8, .72]; part(0, .25, 0, .6, .5, .42, c); part(.4, .48, 0, .36, .4, .34, c);
      part(.35, .94, -.11, .12, .55, .1, c); part(.35, .94, .11, .12, .55, .1, c);
      leg(-.2, -.12, .28, white, w); leg(-.2, .12, .28, white, -w); part(-.38, .55, 0, .16, .2, .18, white);
      eye(.5, .55, -.1); eye(.5, .55, .1);
    }
  }
  if (a.length > _faunaTyped.length) {
    let n = _faunaTyped.length; while (n < a.length) n *= 2; _faunaTyped = new Float32Array(n);
  }
  _faunaTyped.set(a);
  G.bindBuffer(G.ARRAY_BUFFER, eb);
  G.bufferData(G.ARRAY_BUFFER, _faunaTyped.subarray(0, a.length), G.DYNAMIC_DRAW);
  G.vertexAttribPointer(ap, 3, G.FLOAT, false, 28, 0);
  G.vertexAttribPointer(ac, 4, G.FLOAT, false, 28, 12);
  G.uniformMatrix4fv(um, false, m);
  G.drawArrays(G.TRIANGLES, 0, a.length / 7);
}

function spawnParticles(x, y, z, color) {
  for (let i = 0; i < 8; i++) {
    if (particles.length > 200) particles.shift();
    particles.push({
      x: x + 0.5, y: y + 0.5, z: z + 0.5,
      vx: (Math.random() - 0.5) * 4, vy: Math.random() * 4, vz: (Math.random() - 0.5) * 4,
      life: 1.0, c: color
    });
  }
}

function updateParticles(dt) {
  for (let i = particles.length - 1; i >= 0; i--) {
    let p = particles[i];
    p.vy -= 9.8 * dt;
    p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    p.life -= dt * 2;
    if (p.life <= 0 || p.y < 0) particles.splice(i, 1);
  }
}

function renderParticles(m) {
  if (particles.length === 0) return;
  let a = [];
  for (const p of particles) {
    let s = 0.15 * p.life;
    box(a, p.x, p.y, p.z, s, s, s, p.c);
  }
  G.bindBuffer(G.ARRAY_BUFFER, eb);
  G.bufferData(G.ARRAY_BUFFER, new Float32Array(a), G.DYNAMIC_DRAW);
  G.vertexAttribPointer(ap, 3, G.FLOAT, false, 28, 0);
  G.vertexAttribPointer(ac, 4, G.FLOAT, false, 28, 12);
  G.uniformMatrix4fv(um, false, m);
  G.drawArrays(G.TRIANGLES, 0, a.length / 7);
}

function updateMinimap() {
  if (!mapDirty || !mapCtx) return;
  mapDirty = false;
  const imgData = mapCtx.createImageData(100, 100);
  for (let i = 0; i < 100; i++) {
    for (let j = 0; j < 100; j++) {
      let x = Math.floor(i * W / 100), z = Math.floor(j * D / 100);
      let y = H - 1;
      while (y > 0 && (T[I(x, y, z)] === 0 || T[I(x, y, z)] === 19 || T[I(x, y, z)] === 16 || T[I(x, y, z)] === 17 || T[I(x, y, z)] === 18 || T[I(x, y, z)] === 22)) y--;
      let b = T[I(x, y, z)];
      let c = B[b] || [0, 0, 0];
      let idx = (i + j * 100) * 4;
      imgData.data[idx] = c[0] * 255;
      imgData.data[idx + 1] = c[1] * 255;
      imgData.data[idx + 2] = c[2] * 255;
      imgData.data[idx + 3] = 255;
    }
  }
  mapCtx.putImageData(imgData, 0, 0);
  mapCtx.fillStyle = 'red';
  let px = (P.x / W) * 100, pz = (P.z / D) * 100;
  mapCtx.fillRect(px - 2, pz - 2, 4, 4);
}

function resize() {
  let d = Math.min(1.5, devicePixelRatio || 1), w = innerWidth * d, h = innerHeight * d;
  if (C.width !== w || C.height !== h) { C.width = w; C.height = h; G.viewport(0, 0, w, h); }
}

function render() {
  resize();
  let day = .78 + .22 * Math.max(0, Math.sin(time * 6.283));
  G.clearColor(.08 + .25 * day, .12 + .42 * day, .2 + .55 * day, 1);
  G.clear(G.COLOR_BUFFER_BIT | G.DEPTH_BUFFER_BIT);
  G.enable(G.DEPTH_TEST); G.disable(G.CULL_FACE);
  let m = mm(proj(), view()), [cx, cz] = visible();
  G.uniformMatrix4fv(um, false, m); G.uniform1f(us, Math.max(.3, day));

  const cy = Math.cos(P.yaw), sy = Math.sin(P.yaw), cp = Math.cos(P.pitch), sp = Math.sin(P.pitch);
  const fx = -sy * cp, fy = sp, fz = -cy * cp;

  G.disable(G.BLEND);
  for (const o of chunks.values()) {
    if (Math.abs(o.x - cx) > CV || Math.abs(o.z - cz) > CV) continue;
    const dx = o.x * CS + CS * .5 - P.x, dy = H * .5 - (P.y + 1.55), dz = o.z * CS + CS * .5 - P.z;
    const dist2 = dx * dx + dy * dy + dz * dz;
    if (dist2 > 1024) { const inv = 1 / Math.sqrt(dist2); if ((dx * fx + dy * fy + dz * fz) * inv < -0.2) continue; }
    G.bindBuffer(G.ARRAY_BUFFER, o.bO);
    G.vertexAttribPointer(ap, 3, G.FLOAT, false, 28, 0);
    G.vertexAttribPointer(ac, 4, G.FLOAT, false, 28, 12);
    G.drawArrays(G.TRIANGLES, 0, o.nO);
  }

  G.enable(G.BLEND); G.blendFunc(G.SRC_ALPHA, G.ONE_MINUS_SRC_ALPHA); G.depthMask(false);
  for (const o of chunks.values()) {
    if (Math.abs(o.x - cx) > CV || Math.abs(o.z - cz) > CV || o.nT === 0) continue;
    G.bindBuffer(G.ARRAY_BUFFER, o.bT);
    G.vertexAttribPointer(ap, 3, G.FLOAT, false, 28, 0);
    G.vertexAttribPointer(ac, 4, G.FLOAT, false, 28, 12);
    G.drawArrays(G.TRIANGLES, 0, o.nT);
  }
  G.depthMask(true); G.disable(G.BLEND);

  fauna(m);
  renderParticles(m);
}

function updateWater() {
  if (waterQueue.size === 0) return;
  let count = 0;
  let nextQueue = new Set();
  for (const key of waterQueue) {
    if (count++ > 500) { nextQueue.add(key); continue; }
    let [x, y, z] = key.split(',').map(Number);
    let idx = I(x, y, z);
    if (T[idx] !== 11) continue;
    let level = WL[idx];

    let belowIdx = I(x, y - 1, z);
    if (inside(x, y - 1, z) && (T[belowIdx] === 0 || (T[belowIdx] === 11 && WL[belowIdx] < 8))) {
      if (T[belowIdx] === 0) T[belowIdx] = 11;
      WL[belowIdx] = 8; mark(x, z); nextQueue.add(`${x},${y - 1},${z}`);
      continue;
    }

    if (level > 1) {
      for (const [dx, dz] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
        let nx = x + dx, nz = z + dz, nIdx = I(nx, y, nz);
        if (!inside(nx, y, nz)) continue;
        let targetBlock = T[nIdx];
        if (targetBlock === 0 || (targetBlock === 11 && WL[nIdx] < level - 1)) {
          T[nIdx] = 11;
          WL[nIdx] = level - 1;
          mark(nx, nz); nextQueue.add(`${nx},${y},${nz}`);
        }
      }
    }
  }
  waterQueue = nextQueue;
}

const keys = {};
addEventListener('keydown', e => {
  keys[e.code] = 1;
  if (/^Digit[1-9]$/.test(e.code)) sel = Math.min(8, +e.code.slice(5) - 1);
  if (e.code === 'KeyF') P.fly = !P.fly;
  if (e.code === 'KeyR') Object.assign(P, { x: P.spawn[0], y: P.spawn[1], z: P.spawn[2], vy: 0 });
  if (e.code === 'KeyT') time = (time + .25) % 1;
  if (e.code === 'KeyE' && run && !pause) captureRelease();
  if (e.code === 'Escape' && run) togglePause();
  if (e.code === 'KeyK') src.remove.key = 1;
  if (e.code === 'KeyL') src.place.key = 1;
  if (e.code === 'F3') { e.preventDefault(); hudVisible = !hudVisible; $('#hud').classList.toggle('hidden', !hudVisible); }
  hud();
});
addEventListener('keyup', e => {
  keys[e.code] = 0;
  if (e.code === 'KeyK') src.remove.key = 0;
  if (e.code === 'KeyL') src.place.key = 0;
});
C.addEventListener('mousedown', e => {
  e.preventDefault();
  if (!run || pause) return;
  if (document.pointerLockElement !== C) { C.requestPointerLock(); return; }
  if (e.button === 0) src.remove.mouse = 1;
  else if (e.button === 2) src.place.mouse = 1;
});
addEventListener('mouseup', e => {
  if (e.button === 0) src.remove.mouse = 0;
  else if (e.button === 2) src.place.mouse = 0;
});
C.addEventListener('contextmenu', e => e.preventDefault());
addEventListener('mousemove', e => {
  if (document.pointerLockElement === C && !pause) {
    P.yaw -= e.movementX * .002;
    P.pitch = Math.max(-1.45, Math.min(1.45, P.pitch - e.movementY * .002));
    _rayDirty = true;
  }
});
addEventListener('wheel', e => { sel = (sel + (e.deltaY > 0 ? 1 : 8)) % 9; hud(); });
addEventListener('blur', () => {
  for (const k in keys) keys[k] = 0;
  src.remove.key = src.remove.mouse = 0; src.place.key = src.place.mouse = 0;
  touch.jump = touch.down = 0;
});

function ray() {
  if (!_rayDirty && _lastRay !== null) return _lastRay;
  let cp = Math.cos(P.pitch), d = [-Math.sin(P.yaw) * cp, Math.sin(P.pitch), -Math.cos(P.yaw) * cp], last = null;
  let result = null;
  for (let t = 0; t < 7; t += .06) {
    let x = Math.floor(P.x + d[0] * t), y = Math.floor(P.y + 1.55 + d[1] * t), z = Math.floor(P.z + d[2] * t);
    if (!last || x !== last[0] || y !== last[1] || z !== last[2]) {
      if (get(x, y, z)) { result = { h: [x, y, z], p: last }; break; }
      last = [x, y, z];
    }
  }
  _lastRay = result; _rayDirty = false;
  return result;
}
function mark(x, z) {
  let cx = x / CS | 0, cz = z / CS | 0;
  for (let dx = -1; dx <= 1; dx++) for (let dz = -1; dz <= 1; dz++)
    if (dx === 0 || dz === 0) dirty.add(cx + dx + ',' + (cz + dz));
}
function act(place) {
  let r = ray(); if (!r) return;
  if (place) {
    if (!r.p) return;
    let [x, y, z] = r.p;
    if (Math.abs(x - P.x) < .4 && Math.abs(z - P.z) < .4 && y < P.y + P.h && y + 1 > P.y) return;
    set(x, y, z, hot[sel]);
    if (hot[sel] === 11) waterQueue.add(`${x},${y},${z}`);
    mark(x, z); _rayDirty = true;
  } else {
    let [x, y, z] = r.h;
    if (get(x, y, z) === 12) return;
    let b = get(x, y, z);
    spawnParticles(x, y, z, B[b]);
    set(x, y, z, 0); WL[I(x, y, z)] = 0;
    for (const [dx, dy, dz] of [[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]]) {
      let nx=x+dx, ny=y+dy, nz=z+dz;
      if (inside(nx,ny,nz) && T[I(nx,ny,nz)] === 11) waterQueue.add(`${nx},${ny},${nz}`);
    }
    mark(x, z); _rayDirty = true;
  }
}
function col(x, y, z) {
  for (let X = Math.floor(x - P.r + .001); X <= Math.floor(x + P.r - .001); X++)
    for (let Y = Math.floor(y + .001); Y <= Math.floor(y + P.h - .001); Y++)
      for (let Z = Math.floor(z - P.r + .001); Z <= Math.floor(z + P.r - .001); Z++)
        if ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 20, 21].includes(get(X, Y, Z))) return 1;
}
function physics(dt) {
  let f = (keys.KeyW || keys.ArrowUp ? 1 : 0) - (keys.KeyS || keys.ArrowDown ? 1 : 0) - touch.moveY;
  let s = (keys.KeyD || keys.ArrowRight ? 1 : 0) - (keys.KeyA || keys.ArrowLeft ? 1 : 0) + touch.moveX;
  let l = Math.hypot(f, s) || 1, sp = (keys.ShiftLeft || touch.sprint) ? 7 : 4.3;
  let dx = (-Math.sin(P.yaw) * f + Math.cos(P.yaw) * s) * sp * dt / l;
  let dz = (-Math.cos(P.yaw) * f - Math.sin(P.yaw) * s) * sp * dt / l;
  if (P.fly) P.vy = (((keys.Space || touch.jump) ? 1 : 0) - ((keys.ControlLeft || touch.down) ? 1 : 0)) * 7;
  else {
    P.vy -= 18 * dt;
    if ((keys.Space || touch.jump) && P.ground) { P.vy = 7.2; P.ground = 0; }
  }
  if (P.fly || !col(P.x + dx, P.y, P.z)) P.x += dx;
  if (P.fly || !col(P.x, P.y, P.z + dz)) P.z += dz;
  let ny = P.y + P.vy * dt;
  if (P.fly || !col(P.x, ny, P.z)) { P.y = ny; P.ground = 0; }
  else { if (P.vy < 0) P.ground = 1; P.vy = 0; }
  P.x = Math.max(.4, Math.min(W - .4, P.x));
  P.z = Math.max(.4, Math.min(D - .4, P.z));
  if (P.y < 0) Object.assign(P, { x: P.spawn[0], y: P.spawn[1], z: P.spawn[2], vy: 0 });
}
function animalAI(dt) {
  for (const a of animals) {
    a.phase += dt; a.t -= dt;
    let pd = Math.hypot(a.x - P.x, a.z - P.z);
    if (pd < 2.4) { a.to = Math.atan2(a.z - P.z, a.x - P.x); a.state = 1; a.t = 2; }
    else if (a.t <= 0) { a.state = Math.random() < .65 ? 1 : 0; a.t = 2 + Math.random() * 4; a.to += Math.random() * 2 - 1; }
    let turn = ((a.to - a.dir + 9.425) % 6.283) - 3.142;
    a.dir += Math.max(-dt, Math.min(dt, turn));
    if (a.state) {
      let nx = a.x + Math.cos(a.dir) * dt * .35, nz = a.z + Math.sin(a.dir) * dt * .35, ny = surface(nx | 0, nz | 0) + 1;
      if (get(nx|0, Math.floor(a.y), nz|0) === 11) {
        a.to += Math.PI;
      } else if (Math.abs(ny - a.y) < 1.1) {
        a.x = nx; a.z = nz; a.y += (ny - a.y) * Math.min(1, dt * 7);
      } else a.to += 2;
    }
    let isInWater = get(a.x | 0, Math.floor(a.y), a.z | 0) === 11;
    let gy = isInWater ? a.y : surface(a.x | 0, a.z | 0) + 1;
    if (a.y > gy + 0.02 && !isInWater) a.y = Math.max(gy, a.y - 8 * dt);
    else if (a.y < gy - 0.02) a.y = gy;
  }
}

const _hud = { stats: '', statsClass: '', tip: '', status: '', cb: '', hbSel: -1 };
function hud() {
  let r = ray();
  let stats = `CONSTRUCCIÓN · ${fps} FPS · ${P.fly ? 'VUELO' : 'SUELO'} · regiones ${chunks.size}`;
  if (stats !== _hud.stats) { $('#stats').textContent = stats; _hud.stats = stats; }
  let cls = fps >= 50 ? 'fps-good' : fps >= 30 ? 'fps-mid' : 'fps-bad';
  if (cls !== _hud.statsClass) {
    const el = $('#stats'); el.classList.remove('fps-good', 'fps-mid', 'fps-bad'); el.classList.add(cls); _hud.statsClass = cls;
  }
  let tip = performance.now() < _tipUntil ? _tipText : (r ? N[get(...r.h)] : '');
  if (tip !== _hud.tip) { $('#tip').textContent = tip; _hud.tip = tip; }
  let status = captured ? `Transportando ${ANIMAL_NAMES[captured.type] || 'animal'} · E/Dejar` : 'Espada de traslado · E/Atrapar';
  if (status !== _hud.status) { $('#captureStatus').textContent = status; _hud.status = status; }
  let cbT = captured ? 'Dejar' : 'Atrapar';
  if (cbT !== _hud.cb) { let cb = $('#touchCapture'); if (cb) cb.textContent = cbT; _hud.cb = cbT; }
  if (sel !== _hud.hbSel) {
    $('#hotbar').innerHTML = hot.map((b, i) =>
      `<div class="slot ${i === sel ? 'sel' : ''}"><span class="slotIcon">${IC[b]}</span><small>∞</small><span class="slotName">${N[b]}</span></div>`
    ).join('');
    _hud.hbSel = sel;
  }
}

const SAVE_KEY = 'blockforge-review-v14';
const SAVE_VERSION = 14;
function _encodeWorld(arr) {
  let s = ''; const CH = 8192;
  for (let i = 0; i < arr.length; i += CH) s += String.fromCharCode.apply(null, arr.subarray(i, Math.min(i + CH, arr.length)));
  return btoa(s);
}
function _decodeWorld(str) {
  const s = atob(str); const arr = new Uint8Array(s.length);
  for (let i = 0; i < s.length; i++) arr[i] = s.charCodeAt(i);
  return arr;
}
function _buildSavePayload() {
  return { version: SAVE_VERSION, seed: $('#seed').value, w: _encodeWorld(T), p: P, time, animals, captured };
}
function _applySavePayload(d) {
  if (!d || d.version !== SAVE_VERSION) return 0;
  let world = typeof d.w === 'string' ? _decodeWorld(d.w) : d.w;
  if (!world || world.length !== T.length) return 0;
  T.set(world);
  if (d.p && typeof d.p.x === 'number') Object.assign(P, d.p);
  if (typeof d.time === 'number') time = d.time;
  animals = Array.isArray(d.animals) ? d.animals : [];
  captured = d.captured || null;
  if (typeof d.seed === 'string') $('#seed').value = d.seed;
  chunks.clear(); dirty.clear();
  for (let x = 0; x < W / CS; x++) for (let z = 0; z < D / CS; z++) dirty.add(x + ',' + z);
  waterQueue.clear(); particles = []; mapDirty = true;
  _rayDirty = true; _hud.hbSel = -1;
  return 1;
}
function save(silent) {
  try {
    localStorage.setItem(SAVE_KEY, JSON.stringify(_buildSavePayload()));
    if (!silent) showTip('Guardado ✓', 800);
  } catch (e) { if (!silent) showTip('Error al guardar', 1500); }
}
function load() {
  try {
    let raw = localStorage.getItem(SAVE_KEY);
    return raw ? _applySavePayload(JSON.parse(raw)) : 0;
  } catch { return 0; }
}

function start(fresh) {
  animals = []; captured = null;
  if (fresh || !load()) generate($('#seed').value);
  run = true; pause = false; hudVisible = true;
  $('#hud').classList.remove('hidden'); $('#menu').classList.add('hidden'); $('#pause').classList.add('hidden');
  if (coarse) $('#touchControls').classList.remove('hidden'); else C.requestPointerLock();
  _rayDirty = true; _hud.hbSel = -1; mapDirty = true;
  hud();
}
function togglePause() {
  pause = !pause; $('#pause').classList.toggle('hidden', !pause);
  if (pause) {
    document.exitPointerLock();
    src.remove.key = src.remove.mouse = src.remove.touch = 0; src.place.key = src.place.mouse = src.place.touch = 0;
    touch.jump = touch.down = 0;
  } else { _rayDirty = true; if (!coarse) C.requestPointerLock(); }
}
$('#new').onclick = () => start(1);
$('#continue').onclick = () => start(0);
$('#resume').onclick = togglePause;
$('#save').onclick = () => save(false);
$('#export').onclick = () => {
  save(true);
  const blob = new Blob([JSON.stringify(_buildSavePayload())], { type: 'application/json' });
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob);
  a.download = `blockforge-v14-${Date.now()}.json`; a.click(); showTip('Exportado', 1000);
};
$('#import').addEventListener('change', e => {
  const file = e.target.files[0]; e.target.value = ''; if (!file) return;
  const reader = new FileReader();
  reader.onload = () => { if (_applySavePayload(JSON.parse(reader.result))) { hud(); if (pause) togglePause(); else if (!coarse) C.requestPointerLock(); } else showTip('Archivo inválido', 1500); };
  reader.readAsText(file);
});
$('#exit').onclick = () => {
  save(true); run = false; pause = true; document.exitPointerLock();
  $('#pause').classList.add('hidden'); $('#hud').classList.add('hidden'); $('#touchControls').classList.add('hidden'); $('#menu').classList.remove('hidden');
};

function captureRelease() {
  if (captured) {
    let x = P.x - Math.sin(P.yaw) * 2.2, z = P.z - Math.cos(P.yaw) * 2.2;
    captured.x = Math.max(1, Math.min(W - 2, x)); captured.z = Math.max(1, Math.min(D - 2, z));
    captured.y = surface(Math.floor(captured.x), Math.floor(captured.z)) + 1;
    animals.push(captured); captured = null; _rayDirty = true; hud(); return;
  }
  let best = -1, dist = 4.5;
  for (let i = 0; i < animals.length; i++) {
    let a = animals[i], dx = a.x - P.x, dy = (a.y + .5) - (P.y + 1.2), dz = a.z - P.z, d = Math.hypot(dx, dy, dz);
    if (d > dist) continue;
    let fx = -Math.sin(P.yaw) * Math.cos(P.pitch), fy = Math.sin(P.pitch), fz = -Math.cos(P.yaw) * Math.cos(P.pitch);
    if ((dx * fx + dy * fy + dz * fz) / d > .72) { best = i; dist = d; }
  }
  if (best >= 0) { captured = animals.splice(best, 1)[0]; hud(); }
}

function bindHold(id, on, off) {
  let e = $(id);
  e.addEventListener('pointerdown', q => { q.preventDefault(); e.setPointerCapture(q.pointerId); on(); });
  let end = q => { q.preventDefault(); off(); };
  e.addEventListener('pointerup', end); e.addEventListener('pointercancel', end);
}
function setupTouch() {
  if (!coarse) return;
  let mz = $('#moveZone'), stick = $('#moveStick'), look = $('#lookZone');
  mz.addEventListener('pointerdown', e => { touch.moveId = e.pointerId; mz.setPointerCapture(e.pointerId); moveTouch(e); });
  mz.addEventListener('pointermove', e => { if (e.pointerId === touch.moveId) moveTouch(e); });
  let mend = () => { touch.moveId = null; touch.moveX = touch.moveY = 0; stick.style.transform = 'translate(0,0)'; };
  mz.addEventListener('pointerup', mend); mz.addEventListener('pointercancel', mend);
  function moveTouch(e) {
    let r = $('#moveBase').getBoundingClientRect(), dx = e.clientX - (r.left + r.width / 2), dy = e.clientY - (r.top + r.height / 2);
    let max = r.width * .35, d = Math.hypot(dx, dy) || 1, k = Math.min(1, max / d); dx *= k; dy *= k;
    touch.moveX = dx / max; touch.moveY = dy / max; stick.style.transform = `translate(${dx}px,${dy}px)`;
  }
  look.addEventListener('pointerdown', e => { touch.lookId = e.pointerId; touch.lookX = e.clientX; touch.lookY = e.clientY; });
  look.addEventListener('pointermove', e => {
    if (e.pointerId !== touch.lookId) return;
    P.yaw -= (e.clientX - touch.lookX) * .006; P.pitch = Math.max(-1.45, Math.min(1.45, P.pitch - (e.clientY - touch.lookY) * .006));
    touch.lookX = e.clientX; touch.lookY = e.clientY; _rayDirty = true;
  });
  look.addEventListener('pointerup', () => touch.lookId = null); look.addEventListener('pointercancel', () => touch.lookId = null);
  bindHold('#touchJump', () => touch.jump = 1, () => touch.jump = 0); bindHold('#touchDown', () => touch.down = 1, () => touch.down = 0);
  bindHold('#touchRemove', () => src.remove.touch = 1, () => src.remove.touch = 0); bindHold('#touchPlace', () => src.place.touch = 1, () => src.place.touch = 0);
  $('#touchCapture').onpointerdown = captureRelease;
  $('#touchFly').onpointerdown = () => { P.fly = !P.fly; hud(); };
  $('#touchNext').onpointerdown = () => { sel = (sel + 1) % 9; hud(); };
  $('#touchPause').onpointerdown = togglePause;
  document.addEventListener('touchmove', e => { if (e.target === C || e.target.closest('#touchControls')) e.preventDefault(); }, { passive: false });
}
setupTouch();
document.addEventListener('visibilitychange', () => { if (document.hidden && run) save(true); });

let last = performance.now(), fa = 0, ff = 0, auto = 0, _saveScheduled = false, frameCount = 0;
function loop(n) {
  let dt = Math.min(.04, (n - last) / 1000); last = n;
  fa += dt; ff++;
  if (fa > .5) { fps = Math.round(ff / fa); fa = ff = 0; }
  if (run && !pause) {
    time = (time + dt / 300) % 1;
    physics(dt); _rayDirty = true; animalAI(dt); updateWater(); updateParticles(dt);
    action -= dt;
    if (action <= 0 && (wantRemove() || wantPlace())) { act(wantPlace()); action = wantPlace() ? .16 : .10; }
    auto += dt;
    if (auto > 30 && !_saveScheduled) {
      auto = 0; _saveScheduled = true;
      const doSave = () => { save(false); _saveScheduled = false; };
      if (typeof requestIdleCallback === 'function') requestIdleCallback(doSave, { timeout: 2000 }); else setTimeout(doSave, 0);
    }
    if (++frameCount % 30 === 0) updateMinimap();
    hud();
  }
  render(); requestAnimationFrame(loop);
}
requestAnimationFrame(loop);