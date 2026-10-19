// Tank Battle engine (Three.js r128, loaded globally from index.html)
const THREE = window.THREE;

const TERRAIN = 600;          // rendered terrain size
const WORLD = 400;            // playable area size
const LIMIT = WORLD / 2 - 10; // movement bound
const SPAWN = { x: 20, z: 150 };
const PLAYER_SPEED = 14;
const ENEMY_SPEED = 7;
const TURN_SPEED = 1.4;
const SHELL_SPEED = 90;
const PLAYER_RELOAD = 0.8;
const TANK_RADIUS = 2.6;
const PLAYER_DAMAGE = 20;
const GAME_KEYS = new Set(['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space']);

let dotnet, renderer, scene, camera, container, minimap, mctx, flashEl, audio;
let player;
let heli;
let heliTime = 0;
let enemies = [];
let shells = [];
let effects = [];
const trees = [];
const keys = {};
let state = 'start';
let level = 1;
let health = 100;
let levelTimer = 0;
let lastTime = 0;
let fireRequested = false;
let lastReport = '';

const shellGeo = new THREE.SphereGeometry(0.25, 8, 6);
const shellMatP = new THREE.MeshBasicMaterial({ color: 0xffee88 });
const shellMatE = new THREE.MeshBasicMaterial({ color: 0xff6644 });
const fxGeo = new THREE.SphereGeometry(1, 12, 8);

// ---------- helpers ----------

function rng(seed) {
    return function () {
        seed = (seed + 0x6D2B79F5) | 0;
        let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}

function smooth(e0, e1, v) {
    const t = Math.min(1, Math.max(0, (v - e0) / (e1 - e0)));
    return t * t * (3 - 2 * t);
}

function angleDiff(a, b) {
    let d = a - b;
    while (d > Math.PI) d -= Math.PI * 2;
    while (d < -Math.PI) d += Math.PI * 2;
    return d;
}

function roadDist(x, z) {
    return Math.min(Math.abs(x - 20), Math.abs(z + 30), Math.abs(Math.hypot(x, z) - 110));
}

function rawHeight(x, z) {
    return 7 * Math.sin(x * 0.018) * Math.cos(z * 0.022)
        + 4 * Math.sin(x * 0.045 + 1.3) * Math.sin(z * 0.038 + 0.7)
        + 1.5 * Math.sin((x + z) * 0.09);
}

function heightAt(x, z) {
    // Roads are flattened compared to the surrounding hills
    const f = smooth(5, 14, roadDist(x, z));
    return rawHeight(x, z) * (0.35 + 0.65 * f);
}

// ---------- world ----------

function buildTerrain() {
    const seg = 240;
    const geo = new THREE.PlaneGeometry(TERRAIN, TERRAIN, seg, seg);
    geo.rotateX(-Math.PI / 2);
    const pos = geo.attributes.position;
    const colors = new Float32Array(pos.count * 3);
    const r = rng(7);
    for (let i = 0; i < pos.count; i++) {
        const x = pos.getX(i), z = pos.getZ(i);
        const y = heightAt(x, z);
        pos.setY(i, y);
        const n = r() * 0.05;
        if (roadDist(x, z) < 4.5) {
            colors[i * 3] = 0.45 + n; colors[i * 3 + 1] = 0.40 + n; colors[i * 3 + 2] = 0.31 + n;
        } else {
            colors[i * 3] = 0.18 + n; colors[i * 3 + 1] = 0.40 + y * 0.012 + n; colors[i * 3 + 2] = 0.12;
        }
    }
    geo.setAttribute('color', new THREE.BufferAttribute(colors, 3));
    geo.computeVertexNormals();
    scene.add(new THREE.Mesh(geo, new THREE.MeshLambertMaterial({ vertexColors: true })));
}

function buildVegetation() {
    const r = rng(42);
    const spots = [];
    for (let i = 0; i < 4000 && spots.length < 220; i++) {
        const x = (r() - 0.5) * (WORLD + 120), z = (r() - 0.5) * (WORLD + 120);
        if (roadDist(x, z) < 9) continue;
        if (Math.hypot(x - SPAWN.x, z - SPAWN.z) < 15) continue;
        if (spots.some(t => Math.hypot(t.x - x, t.z - z) < 6)) continue;
        spots.push({ x, z, s: 0.8 + r() * 0.6 });
    }

    const trunks = new THREE.InstancedMesh(new THREE.CylinderGeometry(0.35, 0.5, 3, 6),
        new THREE.MeshLambertMaterial({ color: 0x5a3d22 }), spots.length);
    const crowns = new THREE.InstancedMesh(new THREE.ConeGeometry(2.4, 6, 7),
        new THREE.MeshLambertMaterial({ color: 0x24622a }), spots.length);
    const m = new THREE.Matrix4(), q = new THREE.Quaternion(), s = new THREE.Vector3(), p = new THREE.Vector3();

    spots.forEach((t, i) => {
        const y = heightAt(t.x, t.z);
        s.set(t.s, t.s, t.s);
        p.set(t.x, y + 1.5 * t.s, t.z); m.compose(p, q, s); trunks.setMatrixAt(i, m);
        p.set(t.x, y + 5.5 * t.s, t.z); m.compose(p, q, s); crowns.setMatrixAt(i, m);
        trees.push({ x: t.x, z: t.z, r: t.s, top: y + 8.5 * t.s });
    });
    scene.add(trunks, crowns);

    const bushCount = 380;
    const bushes = new THREE.InstancedMesh(new THREE.IcosahedronGeometry(1.2, 0),
        new THREE.MeshLambertMaterial({ color: 0x3f7a2c }), bushCount);
    const e = new THREE.Euler();
    let n = 0;
    for (let i = 0; i < 4000 && n < bushCount; i++) {
        const x = (r() - 0.5) * (WORLD + 120), z = (r() - 0.5) * (WORLD + 120);
        if (roadDist(x, z) < 6) continue;
        const sc = 0.6 + r() * 0.8;
        s.set(sc * 1.3, sc, sc * 1.3);
        p.set(x, heightAt(x, z) + 0.4 * sc, z);
        q.setFromEuler(e.set(0, r() * Math.PI, 0));
        m.compose(p, q, s);
        bushes.setMatrixAt(n++, m);
    }
    bushes.count = n;
    scene.add(bushes);
}

// ---------- tanks ----------

function createTank(hullColor, turretColor) {
    const group = new THREE.Group();
    const hullMat = new THREE.MeshLambertMaterial({ color: hullColor });
    const turretMat = new THREE.MeshLambertMaterial({ color: turretColor });
    const darkMat = new THREE.MeshLambertMaterial({ color: 0x222222 });

    const hull = new THREE.Mesh(new THREE.BoxGeometry(3.4, 1.1, 5.4), hullMat);
    hull.position.y = 0.95;
    const trackL = new THREE.Mesh(new THREE.BoxGeometry(0.8, 0.9, 5.8), darkMat);
    trackL.position.set(-1.75, 0.45, 0);
    const trackR = trackL.clone();
    trackR.position.x = 1.75;
    const turret = new THREE.Mesh(new THREE.BoxGeometry(2.2, 0.8, 2.6), turretMat);
    turret.position.set(0, 1.9, 0.3);
    const barrel = new THREE.Mesh(new THREE.CylinderGeometry(0.16, 0.2, 4.2, 10), darkMat);
    barrel.rotation.x = Math.PI / 2;
    barrel.position.set(0, 1.95, -3.0);
    group.add(hull, trackL, trackR, turret, barrel);
    scene.add(group);

    return { group, mats: [hullMat, turretMat], x: 0, z: 0, heading: 0, speed: 0, reload: 0, alive: true };
}

function placeTank(t) {
    const fx = -Math.sin(t.heading), fz = -Math.cos(t.heading);
    const rx = Math.cos(t.heading), rz = -Math.sin(t.heading);
    const hF = heightAt(t.x + fx * 2.5, t.z + fz * 2.5);
    const hB = heightAt(t.x - fx * 2.5, t.z - fz * 2.5);
    const hR = heightAt(t.x + rx * 1.6, t.z + rz * 1.6);
    const hL = heightAt(t.x - rx * 1.6, t.z - rz * 1.6);
    t.group.position.set(t.x, (hF + hB + hR + hL) / 4, t.z);
    t.group.rotation.set(Math.atan2(hF - hB, 5), t.heading, Math.atan2(hR - hL, 3.2), 'YXZ');
    t.group.updateMatrixWorld(true);
}

function resolveCollisions(t) {
    for (const tr of trees) {
        const dx = t.x - tr.x, dz = t.z - tr.z;
        const min = tr.r + TANK_RADIUS * 0.8;
        const d2 = dx * dx + dz * dz;
        if (d2 < min * min && d2 > 1e-6) {
            const d = Math.sqrt(d2);
            t.x = tr.x + dx / d * min;
            t.z = tr.z + dz / d * min;
        }
    }
    for (const o of [player, ...enemies]) {
        if (o === t) continue;
        const dx = t.x - o.x, dz = t.z - o.z;
        const min = TANK_RADIUS * 2;
        const d2 = dx * dx + dz * dz;
        if (d2 < min * min && d2 > 1e-6) {
            const d = Math.sqrt(d2);
            t.x = o.x + dx / d * min;
            t.z = o.z + dz / d * min;
        }
    }
    t.x = Math.max(-LIMIT, Math.min(LIMIT, t.x));
    t.z = Math.max(-LIMIT, Math.min(LIMIT, t.z));
}

function muzzle(t) {
    const p = new THREE.Vector3(0, 1.95, -5.2).applyMatrix4(t.group.matrixWorld);
    const d = new THREE.Vector3(0, 0, -1).applyQuaternion(t.group.quaternion);
    return { p, d };
}

function tankCenter(t) {
    return new THREE.Vector3(t.x, t.group.position.y + 1.3, t.z);
}

function hasLineOfSight(a, b) {
    const ay = a.group.position.y + 2, by = b.group.position.y + 2;
    for (let i = 1; i < 20; i++) {
        const k = i / 20;
        if (heightAt(a.x + (b.x - a.x) * k, a.z + (b.z - a.z) * k) > ay + (by - ay) * k) return false;
    }
    return true;
}

function fire(t, dir, isPlayer, p) {
    const mesh = new THREE.Mesh(shellGeo, isPlayer ? shellMatP : shellMatE);
    mesh.position.copy(p);
    scene.add(mesh);
    shells.push({ mesh, v: dir.multiplyScalar(SHELL_SPEED), owner: t, life: 2.5 });
    explode(p, 0.7);
    const dist = player.group.position.distanceTo(p);
    sound('shot', isPlayer ? 0.6 : Math.max(0.08, 0.6 - dist / 250));
}

function playerFire() {
    if (player.reload > 0) return;
    player.reload = PLAYER_RELOAD;
    const { p, d } = muzzle(player);
    // Vertical aim assist: keep horizontal aim, adjust elevation to the enemy in the sights
    const hx = d.x, hz = d.z, hl = Math.hypot(hx, hz) || 1;
    let best = null, bestAng = 0.1;
    for (const e of enemies) {
        if (!e.alive) continue;
        const dx = e.x - p.x, dz = e.z - p.z, dist = Math.hypot(dx, dz);
        const ang = Math.acos(Math.min(1, (dx * hx + dz * hz) / (dist * hl)));
        if (ang < bestAng && dist < 200) { best = e; bestAng = ang; }
    }
    if (best) {
        const c = tankCenter(best);
        const dist = Math.hypot(c.x - p.x, c.z - p.z);
        d.set(hx / hl, (c.y - p.y) / dist, hz / hl).normalize();
    }
    fire(player, d, true, p);
}

function enemyFire(e) {
    const { p } = muzzle(e);
    const spread = Math.max(0.02, 0.09 - level * 0.005);
    const d = tankCenter(player).sub(p).normalize();
    d.x += (Math.random() - 0.5) * spread;
    d.y += (Math.random() - 0.5) * spread * 0.5;
    d.z += (Math.random() - 0.5) * spread;
    fire(e, d.normalize(), false, p);
}

// ---------- update ----------

function updatePlayer(dt) {
    const fwd = (keys.KeyW || keys.ArrowUp ? 1 : 0) - (keys.KeyS || keys.ArrowDown ? 1 : 0);
    const turn = (keys.KeyA || keys.ArrowLeft ? 1 : 0) - (keys.KeyD || keys.ArrowRight ? 1 : 0);
    player.heading += turn * TURN_SPEED * dt;
    const target = fwd * PLAYER_SPEED * (fwd < 0 ? 0.5 : 1);
    player.speed += (target - player.speed) * Math.min(1, dt * 3);
    player.x += -Math.sin(player.heading) * player.speed * dt;
    player.z += -Math.cos(player.heading) * player.speed * dt;
    resolveCollisions(player);
    player.reload -= dt;
    if (keys.Space || fireRequested) playerFire();
    fireRequested = false;
}

function updateEnemy(e, dt) {
    e.reload -= dt;
    e.wobbleTimer -= dt;
    if (e.wobbleTimer <= 0) {
        e.wobble = (Math.random() - 0.5) * 1.2;
        e.wobbleTimer = 2 + Math.random() * 3;
    }
    const dx = player.x - e.x, dz = player.z - e.z;
    const dist = Math.hypot(dx, dz);
    const toPlayer = Math.atan2(-dx, -dz);
    const approaching = dist > e.engage;
    const desired = approaching ? toPlayer + e.wobble : toPlayer;
    const diff = angleDiff(desired, e.heading);
    const maxTurn = TURN_SPEED * 0.8 * dt;
    e.heading += Math.max(-maxTurn, Math.min(maxTurn, diff));

    const speed = approaching ? ENEMY_SPEED * Math.min(1.6, 1 + level * 0.04) : 0;
    e.x += -Math.sin(e.heading) * speed * dt;
    e.z += -Math.cos(e.heading) * speed * dt;
    resolveCollisions(e);
    placeTank(e);

    if (state === 'playing' && e.reload <= 0 && dist < 130
        && Math.abs(angleDiff(toPlayer, e.heading)) < 0.15 && hasLineOfSight(e, player)) {
        e.reload = Math.max(1.8, 4 - level * 0.15) + Math.random() * 2;
        enemyFire(e);
    }
}

function updateShells(dt) {
    for (let i = shells.length - 1; i >= 0; i--) {
        const s = shells[i];
        s.life -= dt;
        // Sub-steps prevent tunnelling through tanks
        const steps = Math.ceil(SHELL_SPEED * dt / 1.5);
        let done = s.life <= 0;
        for (let k = 0; k < steps && !done; k++) {
            s.mesh.position.addScaledVector(s.v, dt / steps);
            done = checkShellHit(s);
        }
        if (done) {
            scene.remove(s.mesh);
            shells.splice(i, 1);
        }
    }
}

function checkShellHit(s) {
    const p = s.mesh.position;
    if (p.y < heightAt(p.x, p.z)) {
        explode(p, 1.2);
        return true;
    }
    for (const tr of trees) {
        const dx = p.x - tr.x, dz = p.z - tr.z, rr = tr.r * 1.6;
        if (dx * dx + dz * dz < rr * rr && p.y < tr.top) {
            explode(p, 1.2);
            return true;
        }
    }
    const targets = s.owner === player ? enemies : [player];
    for (const t of targets) {
        if (!t.alive) continue;
        const dx = p.x - t.x, dz = p.z - t.z, dy = p.y - (t.group.position.y + 1.3);
        if (dx * dx + dz * dz < TANK_RADIUS * TANK_RADIUS && dy > -1.5 && dy < 2.2) {
            if (t === player) hitPlayer(p);
            else destroyEnemy(t);
            return true;
        }
    }
    return false;
}

function hitPlayer(p) {
    explode(p, 1.5);
    sound('boom', 0.7);
    if (state !== 'playing') return;
    health -= PLAYER_DAMAGE;
    flash();
    if (health <= 0) {
        health = 0;
        player.alive = false;
        player.mats.forEach(m => m.color.setHex(0x1a1a1a));
        explode(tankCenter(player), 4);
        sound('boom', 1);
        state = 'gameover';
    }
    report();
}

function destroyEnemy(e) {
    e.alive = false;
    e.mats.forEach(m => m.color.setHex(0x1a1a1a));
    explode(tankCenter(e), 4);
    sound('boom', 0.9);
    if (state === 'playing' && enemies.every(x => !x.alive)) {
        state = 'levelup';
        levelTimer = 3;
    }
    report();
}

function explode(pos, size) {
    const mesh = new THREE.Mesh(fxGeo, new THREE.MeshBasicMaterial({ color: 0xffaa33, transparent: true, opacity: 1, depthWrite: false }));
    mesh.position.copy(pos);
    mesh.scale.setScalar(size * 0.3);
    scene.add(mesh);
    effects.push({ mesh, t: 0, dur: 0.4 + size * 0.15, size });
}

function updateEffects(dt) {
    for (let i = effects.length - 1; i >= 0; i--) {
        const f = effects[i];
        f.t += dt;
        const k = f.t / f.dur;
        if (k >= 1) {
            scene.remove(f.mesh);
            f.mesh.material.dispose();
            effects.splice(i, 1);
            continue;
        }
        f.mesh.scale.setScalar(f.size * (0.3 + k * 1.2));
        f.mesh.material.opacity = 1 - k;
        f.mesh.material.color.setRGB(1 - k * 0.5, 0.67 - k * 0.2, 0.2 + k * 0.3);
    }
}

// ---------- helicopter (ambient, always flying) ----------

function createHelicopter() {
    const g = new THREE.Group();
    const bodyMat = new THREE.MeshLambertMaterial({ color: 0x3b4a32 });
    const darkMat = new THREE.MeshLambertMaterial({ color: 0x1e1e1e });
    const glassMat = new THREE.MeshLambertMaterial({ color: 0x223344 });

    const body = new THREE.Mesh(new THREE.SphereGeometry(1, 14, 10), bodyMat);
    body.scale.set(1.3, 1.2, 2.6);
    const glass = new THREE.Mesh(new THREE.SphereGeometry(1, 12, 8), glassMat);
    glass.scale.set(1.0, 0.8, 1.2);
    glass.position.set(0, 0.35, -1.7);
    const boom = new THREE.Mesh(new THREE.CylinderGeometry(0.18, 0.35, 5.5, 8), bodyMat);
    boom.rotation.x = Math.PI / 2;
    boom.position.set(0, 0.3, 4.4);
    const fin = new THREE.Mesh(new THREE.BoxGeometry(0.15, 1.6, 1.0), bodyMat);
    fin.position.set(0, 1.0, 7.0);
    const mast = new THREE.Mesh(new THREE.CylinderGeometry(0.15, 0.15, 0.6, 6), darkMat);
    mast.position.y = 1.4;

    const rotor = new THREE.Group();
    rotor.position.y = 1.75;
    const blade = new THREE.BoxGeometry(12, 0.06, 0.45);
    const b1 = new THREE.Mesh(blade, darkMat);
    const b2 = new THREE.Mesh(blade, darkMat);
    b2.rotation.y = Math.PI / 2;
    rotor.add(b1, b2);

    const tail = new THREE.Group();
    tail.position.set(0.2, 1.1, 7.2);
    const tailBlade = new THREE.BoxGeometry(0.05, 2.2, 0.25);
    const t1 = new THREE.Mesh(tailBlade, darkMat);
    const t2 = new THREE.Mesh(tailBlade, darkMat);
    t2.rotation.x = Math.PI / 2;
    tail.add(t1, t2);

    const skidGeo = new THREE.BoxGeometry(0.12, 0.12, 4);
    const strutGeo = new THREE.BoxGeometry(0.1, 0.6, 0.1);
    for (const side of [-0.9, 0.9]) {
        const skid = new THREE.Mesh(skidGeo, darkMat);
        skid.position.set(side, -1.5, 0);
        const s1 = new THREE.Mesh(strutGeo, darkMat);
        s1.position.set(side, -1.2, -0.9);
        const s2 = s1.clone();
        s2.position.z = 0.9;
        g.add(skid, s1, s2);
    }

    g.add(body, glass, boom, fin, mast, rotor, tail);
    scene.add(g);
    return { group: g, rotor, tail, x: 0, z: 0, y: 40, heading: 0, bank: 0 };
}

function heliPath(t) {
    // Lissajous route across the whole map
    return { x: 150 * Math.sin(t * 0.06), z: 130 * Math.sin(t * 0.09 + 1) };
}

function updateHelicopter(dt) {
    heliTime += dt;
    const p = heliPath(heliTime), n = heliPath(heliTime + 0.5);
    const heading = Math.atan2(-(n.x - p.x), -(n.z - p.z));
    const turnRate = angleDiff(heading, heli.heading) / Math.max(dt, 1e-3);
    heli.heading = heading;
    const targetBank = Math.max(-0.5, Math.min(0.5, turnRate * 1.2));
    heli.bank += (targetBank - heli.bank) * Math.min(1, dt * 2);
    const targetY = Math.max(heightAt(p.x, p.z) + 26, 30);
    heli.y += (targetY - heli.y) * Math.min(1, dt * 0.8);
    heli.x = p.x;
    heli.z = p.z;
    heli.group.position.set(p.x, heli.y, p.z);
    heli.group.rotation.set(-0.12, heading, heli.bank, 'YXZ');
    heli.rotor.rotation.y += dt * 25;
    heli.tail.rotation.x += dt * 40;
}

// ---------- level flow ----------

function clearLevel() {
    enemies.forEach(e => scene.remove(e.group));
    enemies = [];
    shells.forEach(s => scene.remove(s.mesh));
    shells = [];
}

function spawnEnemy() {
    for (let tries = 0; tries < 300; tries++) {
        const ang = Math.random() * Math.PI * 2;
        const dist = 90 + Math.random() * 90;
        const x = player.x + Math.sin(ang) * dist, z = player.z + Math.cos(ang) * dist;
        if (Math.abs(x) > LIMIT || Math.abs(z) > LIMIT) continue;
        if (trees.some(t => Math.hypot(t.x - x, t.z - z) < 5)) continue;
        if (enemies.some(e => Math.hypot(e.x - x, e.z - z) < 12)) continue;
        return makeEnemy(x, z);
    }
    return makeEnemy((Math.random() - 0.5) * LIMIT * 2, -LIMIT + Math.random() * 40);
}

function makeEnemy(x, z) {
    const e = createTank(0x7a2e24, 0x8e3a2c);
    Object.assign(e, {
        x, z,
        heading: Math.random() * Math.PI * 2,
        reload: 2 + Math.random() * 3,
        engage: 40 + Math.random() * 30,
        wobble: 0, wobbleTimer: 0
    });
    resolveCollisions(e);
    placeTank(e);
    enemies.push(e);
}

function startLevel() {
    clearLevel();
    health = 100;
    player.alive = true;
    player.mats[0].color.setHex(0x556b2f);
    player.mats[1].color.setHex(0x6b7f3a);
    Object.assign(player, { x: SPAWN.x, z: SPAWN.z, heading: 0, speed: 0, reload: 0 });
    placeTank(player);
    for (let i = 0; i < level; i++) spawnEnemy();
    state = 'playing';
    report();
}

export function startGame() {
    initAudio();
    level = 1;
    startLevel();
}

function report() {
    const alive = enemies.filter(e => e.alive).length;
    const key = `${state}|${level}|${alive}|${health}`;
    if (key === lastReport || !dotnet) return;
    lastReport = key;
    dotnet.invokeMethodAsync('OnStatus', state, level, alive, Math.max(0, Math.round(health)));
}

// ---------- audio / fx ----------

function initAudio() {
    try {
        if (!audio) audio = new (window.AudioContext || window.webkitAudioContext)();
        if (audio.state === 'suspended') audio.resume();
    } catch { }
}

function sound(kind, volume) {
    if (!audio || audio.state !== 'running') return;
    const boom = kind === 'boom';
    const dur = boom ? 0.9 : 0.35;
    const buf = audio.createBuffer(1, Math.floor(audio.sampleRate * dur), audio.sampleRate);
    const data = buf.getChannelData(0);
    for (let i = 0; i < data.length; i++) data[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / data.length, boom ? 2 : 3);
    const src = audio.createBufferSource();
    src.buffer = buf;
    const filter = audio.createBiquadFilter();
    filter.type = 'lowpass';
    filter.frequency.value = boom ? 600 : 1400;
    const gain = audio.createGain();
    gain.gain.value = volume;
    src.connect(filter).connect(gain).connect(audio.destination);
    src.start();
}

function flash() {
    flashEl.style.transition = 'none';
    flashEl.style.opacity = '0.45';
    setTimeout(() => {
        flashEl.style.transition = 'opacity .5s';
        flashEl.style.opacity = '0';
    }, 30);
}

function drawMinimap() {
    const w = minimap.width, s = w / WORLD;
    const mx = x => (x + WORLD / 2) * s, my = z => (z + WORLD / 2) * s;
    mctx.clearRect(0, 0, w, w);
    mctx.fillStyle = 'rgba(20,40,20,0.6)';
    mctx.fillRect(0, 0, w, w);
    mctx.strokeStyle = 'rgba(210,190,150,0.6)';
    mctx.lineWidth = 2;
    mctx.beginPath();
    mctx.moveTo(mx(20), 0); mctx.lineTo(mx(20), w);
    mctx.moveTo(0, my(-30)); mctx.lineTo(w, my(-30));
    mctx.moveTo(mx(110), my(0)); mctx.arc(mx(0), my(0), 110 * s, 0, Math.PI * 2);
    mctx.stroke();
    for (const e of enemies) {
        mctx.fillStyle = e.alive ? '#ff4433' : '#555';
        mctx.fillRect(mx(e.x) - 3, my(e.z) - 3, 6, 6);
    }
    mctx.fillStyle = '#ffd84a';
    mctx.beginPath();
    mctx.arc(mx(heli.x), my(heli.z), 3, 0, Math.PI * 2);
    mctx.fill();
    const px = mx(player.x), py = my(player.z);
    mctx.strokeStyle = '#7f7';
    mctx.beginPath();
    mctx.moveTo(px, py);
    mctx.lineTo(px - Math.sin(player.heading) * 9, py - Math.cos(player.heading) * 9);
    mctx.stroke();
    mctx.fillStyle = '#7f7';
    mctx.beginPath();
    mctx.arc(px, py, 3.5, 0, Math.PI * 2);
    mctx.fill();
}

// ---------- main loop ----------

function loop(now) {
    requestAnimationFrame(loop);
    const dt = Math.min(0.05, (now - lastTime) / 1000 || 0);
    lastTime = now;

    if (state === 'playing' || state === 'levelup') {
        updatePlayer(dt);
        for (const e of enemies) if (e.alive) updateEnemy(e, dt);
    }
    updateHelicopter(dt);
    updateShells(dt);
    updateEffects(dt);

    if (state === 'levelup') {
        levelTimer -= dt;
        if (levelTimer <= 0) {
            level++;
            startLevel();
        }
    }

    placeTank(player);
    renderer.render(scene, camera);
    drawMinimap();
}

function onResize() {
    const w = container.clientWidth, h = container.clientHeight;
    renderer.setSize(w, h);
    camera.aspect = w / h;
    camera.updateProjectionMatrix();
}

function bindInput() {
    window.addEventListener('keydown', e => {
        if (GAME_KEYS.has(e.code)) {
            keys[e.code] = true;
            e.preventDefault();
        }
        initAudio();
    });
    window.addEventListener('keyup', e => { keys[e.code] = false; });
    window.addEventListener('blur', () => { for (const k in keys) keys[k] = false; });
    window.addEventListener('pointerdown', initAudio);
    renderer.domElement.addEventListener('pointerdown', e => {
        if (e.pointerType === 'mouse' && state === 'playing') fireRequested = true;
    });
    document.querySelectorAll('[data-key]').forEach(el => {
        const k = el.dataset.key;
        el.addEventListener('pointerdown', e => { e.preventDefault(); keys[k] = true; });
        ['pointerup', 'pointerleave', 'pointercancel'].forEach(t =>
            el.addEventListener(t, e => { e.preventDefault(); keys[k] = false; }));
    });
}

export function init(containerId, minimapId, ref) {
    dotnet = ref;
    container = document.getElementById(containerId);
    minimap = document.getElementById(minimapId);
    mctx = minimap.getContext('2d');

    renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    container.appendChild(renderer.domElement);

    scene = new THREE.Scene();
    scene.background = new THREE.Color(0x9cc7e8);
    scene.fog = new THREE.Fog(0x9cc7e8, 90, 280);
    scene.add(new THREE.HemisphereLight(0xdfefff, 0x445533, 0.9));
    const sun = new THREE.DirectionalLight(0xffffff, 0.7);
    sun.position.set(80, 120, 40);
    scene.add(sun);

    camera = new THREE.PerspectiveCamera(70, 1, 0.1, 700);

    buildTerrain();
    buildVegetation();
    heli = createHelicopter();

    // Player tank with the camera mounted on top of the turret
    player = createTank(0x556b2f, 0x6b7f3a);
    player.group.add(camera);
    camera.position.set(0, 2.95, 0.6);
    Object.assign(player, { x: SPAWN.x, z: SPAWN.z });
    placeTank(player);

    flashEl = document.createElement('div');
    flashEl.style.cssText = 'position:fixed;inset:0;background:#f00;opacity:0;pointer-events:none;z-index:12';
    document.body.appendChild(flashEl);

    onResize();
    window.addEventListener('resize', onResize);
    bindInput();
    requestAnimationFrame(loop);
}
