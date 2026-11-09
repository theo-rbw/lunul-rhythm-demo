/*
 * Rhythm Simulator lighting (v2): a consumer of the presence timeline.
 * For any minute it decides each zone's intensity (0-100 %) and colour temperature, and says which rule decided it.
 *
 * Rules, applied in order (every zone, every minute, lands in exactly one):
 *   Occupied zones are set only by their own occupants.
 *   Any zone:
 *     S1  An infant is asleep there -> the infant's asleep preference (off), whoever else is present.
 *   Owned zones (lighting.zoneRanking):
 *     H1  The highest-ranked person present controls the zone; people sharing that rank are averaged.
 *         They use their own state: an owner asleep means off, an owner awake means their preference.
 *   Zones with no owner:
 *     O1  An infant is there            -> the infant's preference (asleep = off).
 *     O2  Otherwise someone is asleep   -> the sleeper's preference (off).
 *     O3  Otherwise                     -> the average of the occupants' preferences (one occupant = theirs).
 *   Unoccupied zones (public or private):
 *     U1  An occupied zone (public or private) in line of sight -> Acuity x its intensity, in its colour
 *                                             (several: the brightest one).
 *     U2  An occupied public zone two steps away through an empty public zone, and this zone is public
 *                                             -> Acuity x Acuity x its intensity. Not from a zone lit only by the night floor.
 *         If U1 and U2 both reach a zone, the higher value wins.
 *     U3  Neither                            -> off.
 */
(function (root) {
  'use strict';

  const hm = s => { const [h, m] = s.split(':').map(Number); return h * 60 + m; };

  function pointInPolygon(x, y, poly) {
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const [xi, yi] = poly[i], [xj, yj] = poly[j];
      if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }
  function distToSegment(px, py, [ax, ay], [bx, by]) {
    const dx = bx - ax, dy = by - ay, l2 = dx * dx + dy * dy;
    const t = l2 ? Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / l2)) : 0;
    return Math.hypot(px - ax - t * dx, py - ay - t * dy);
  }
  // Centre: the point deepest inside the zone (so L-shaped rooms get a centre inside them).
  // Radius: the smallest circle around that centre that covers the whole zone.
  function centreAndRadius(poly) {
    const xs = poly.map(p => p[0]), ys = poly.map(p => p[1]);
    const [x0, x1, y0, y1] = [Math.min(...xs), Math.max(...xs), Math.min(...ys), Math.max(...ys)];
    let best = [(x0 + x1) / 2, (y0 + y1) / 2], bestD = -1;
    for (let x = x0; x <= x1; x += 0.25) for (let y = y0; y <= y1; y += 0.25) {
      if (!pointInPolygon(x, y, poly)) continue;
      let d = Infinity;
      for (let i = 0; i < poly.length; i++) d = Math.min(d, distToSegment(x, y, poly[i], poly[(i + 1) % poly.length]));
      if (d > bestD) { bestD = d; best = [x, y]; }
    }
    const radius = Math.max(...poly.map(([x, y]) => Math.hypot(x - best[0], y - best[1])));
    return { cx: best[0], cy: best[1], radius };
  }

  // Colour temperature (K) to RGB, from the same palette as the other app's solar graph.
  const DEFAULT_PALETTE = [[1800, '#ff8016'], [2400, '#ffac54'], [3000, '#ffdba8'], [3500, '#e2ecf2'], [4000, '#96cefa']];
  const hexRgb = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  function paletteRgb(k, palette) {
    const pal = palette || DEFAULT_PALETTE;
    if (k <= pal[0][0]) return hexRgb(pal[0][1]);
    for (let i = 1; i < pal.length; i++) if (k <= pal[i][0]) {
      const f = (k - pal[i - 1][0]) / (pal[i][0] - pal[i - 1][0]), a = hexRgb(pal[i - 1][1]), b = hexRgb(pal[i][1]);
      return a.map((c, j) => Math.round(c + (b[j] - c) * f));
    }
    return hexRgb(pal[pal.length - 1][1]);
  }
  // Average colour temperatures in mireds, which is closer to how the eye blends warm and cool light.
  const mixKelvin = ks => ks.length ? 1e6 / (ks.reduce((s, k) => s + 1e6 / k, 0) / ks.length) : 2700;

  function build(planRaw, P, household) {
    const L = household.lighting || {};
    const rules = Object.assign({ outsideOwnRoom: 'shared', sleepingInfantWins: true, infantWins: true, sleeperWins: true, neighbours: 'brightest', spillHops: 2, transitCountsAsOccupied: true, privateLightsNeighbours: true }, L.rules || {});
    const ranking = Object.fromEntries(Object.entries(L.zoneRanking || {}).filter(([k]) => !k.startsWith('_')));
    const privacy = planRaw.privacy || { privateTypes: ['bedroom', 'bath', 'office', 'gym'] };
    const zones = P.zones.map(z => Object.assign({
      index: z.index, id: z.id, name: z.name, room: z.room, level: z.level, polygon: z.polygon,
      private: (privacy.privateTypes || []).includes(z.type)
    }, centreAndRadius(z.polygon)));
    const roomType = Object.fromEntries(planRaw.rooms.map(r => [r.id, r.type]));

    // Line of sight: zone pairs joined by an opening, a stair, or a door that is never closed.
    const pairs = new Map();
    const link = (a, b, via) => {
      if (a < 0 || b < 0 || a === b) return;
      const k = Math.min(a, b) + '|' + Math.max(a, b);
      if (!pairs.has(k)) pairs.set(k, { a: Math.min(a, b), b: Math.max(a, b), via });
    };
    const los = planRaw.lineOfSight || {};
    for (const d of planRaw.doorways || []) {
      if (d.kind === 'exit' || d.closable) continue;
      if (los.exteriorDoorsBlock !== false && d.rooms.some(r => r === 'outside' || roomType[r] === 'exterior')) continue;
      const [x, y] = d.at, o = 0.7;
      const [p1, p2] = d.axis === 'h' ? [[x, y - o], [x, y + o]] : [[x - o, y], [x + o, y]];
      link(P.zoneAt(d.level, p1[0], p1[1]), P.zoneAt(d.level, p2[0], p2[1]), d.kind === 'stair' ? 'stair' : d.kind === 'opening' ? 'open plan' : 'door kept open');
    }
    for (const r of planRaw.rooms) {
      const zs = zones.filter(z => z.room === r.id);
      for (let i = 0; i < zs.length; i++) for (let j = i + 1; j < zs.length; j++) link(zs[i].index, zs[j].index, 'same room');
    }
    for (const [ra, rb] of los.vertical || []) {
      for (const za of zones.filter(z => z.room === ra)) for (const zb of zones.filter(z => z.room === rb)) link(za.index, zb.index, 'stairwell');
    }
    const neighbours = zones.map(() => []);
    for (const { a, b } of pairs.values()) { neighbours[a].push(b); neighbours[b].push(a); }

    // Preferences.
    const profiles = L.profiles || {};
    const byRole = L.profileByRole || {};
    const curve = prof => (prof.awake || []).map(([t, i, k]) => [hm(t), i / 100, k]).sort((u, v) => u[0] - v[0]);
    const curves = Object.fromEntries(Object.entries(profiles).map(([id, prof]) => [id, curve(prof)]));
    // Imported preferences: 96 values a day. A person gets their own curve in their own rooms and the shared curve elsewhere.
    const prefs = L.preferences || null;
    const palette = prefs && prefs.palette;
    const kelvinToRgb = k => paletteRgb(k, palette);
    const dayTypeOf = minute => Math.floor(minute / 1440) % 7 >= 5 ? 'weekend' : 'weekday';
    const curveFor = (id, dayType) => ((prefs.people[id] || prefs.shared)[dayType]);
    function sample(c, tod) {
      const x = tod / 15, i = Math.min(95, Math.floor(x)), j = (i + 1) % 96, f = x - i;
      return { intensity: (c.b[i] + (c.b[j] - c.b[i]) * f) / 100, kelvin: c.k[i] + (c.k[j] - c.k[i]) * f };
    }
    // Night floor. Anyone awake gets at least a dim level where they are, higher before they've slept tonight than after.
    // While the floor is what's lighting them, the route to their bed glows at the same level. A zone with a sleeper is never lifted.
    const FLOOR = Object.assign({ beforeSleep: 10, afterSleep: 5, kelvin: 1800, fadeOutMinutes: 3, route: true }, L.nightFloor || {});
    const walk = zones.map(() => []);
    const walkLink = (a, b) => {
      if (a < 0 || b < 0 || a === b) return;
      const d = Math.hypot(zones[a].cx - zones[b].cx, zones[a].cy - zones[b].cy);
      walk[a].push([b, d]); walk[b].push([a, d]);
    };
    for (const d of planRaw.doorways || []) {
      if (d.kind === 'exit' || d.rooms.includes('outside')) continue;
      const [x, y] = d.at, o = 0.7;
      const [p1, p2] = d.axis === 'h' ? [[x, y - o], [x, y + o]] : [[x - o, y], [x + o, y]];
      walkLink(P.zoneAt(d.level, p1[0], p1[1]), P.zoneAt(d.level, p2[0], p2[1]));
    }
    for (const { a, b, via } of pairs.values()) if (via === 'same room' || via === 'stairwell') walkLink(a, b);
    const routes = new Map();
    function routeBetween(from, to) {
      const key = from + '|' + to;
      if (routes.has(key)) return routes.get(key);
      const dist = zones.map(() => Infinity), prev = zones.map(() => -1), done = zones.map(() => false);
      dist[from] = 0;
      for (;;) {
        let u = -1;
        for (let i = 0; i < zones.length; i++) if (!done[i] && dist[i] < Infinity && (u < 0 || dist[i] < dist[u])) u = i;
        if (u < 0) break;
        done[u] = true;
        for (const [v, d] of walk[u]) if (dist[u] + d < dist[v]) { dist[v] = dist[u] + d; prev[v] = u; }
      }
      const path = [];
      if (dist[to] < Infinity) for (let z = to; z !== from && z >= 0; z = prev[z]) path.push(z);
      routes.set(key, path);
      return path;
    }
    const floors = new WeakMap();
    function floorTable(week, before) {
      let byWeek = floors.get(week); if (!byWeek) floors.set(week, byWeek = {});
      if (byWeek[before]) return byWeek[before];
      const after = before * FLOOR.afterSleep / FLOOR.beforeSleep, n = week.presence[week.people[0].id].zone.length;
      const Z = zones.length, out = zones.map(() => new Float32Array(n)), who = zones.map(() => new Int8Array(n).fill(-1));
      const asleepAt = new Int32Array(Z).fill(-1), infantAt = new Int32Array(Z).fill(-1);
      const levels = {}, slept = week.people.map(() => -1e9), fall = before / Math.max(1, FLOOR.fadeOutMinutes), env = new Float32Array(Z), target = new Float32Array(Z);
      const plans = week.people.map(p => {
        const own = prefs && prefs.people[p.id];
        levels[p.id] = new Float32Array(n);
        if (!own || p.role === 'infant' || !FLOOR.route) return null;
        const rooms = new Set(zones.filter(z => (own.rooms || []).includes(z.id)).map(z => z.index));
        const bed = zones.find(z => z.id === p.homeZone) || zones.find(z => rooms.has(z.index));
        return bed ? { rooms, bed: bed.index } : null;
      });
      for (let m = 0; m < n; m++) {
        target.fill(0);
        const night = Math.floor((m - 1080) / 1440) * 1440 + 1080; // tonight began at 18:00
        week.people.forEach((p, i) => {
          const pr = week.presence[p.id];
          if (pr.state[m] === 2 && pr.zone[m] >= 0) { asleepAt[pr.zone[m]] = m; slept[i] = m; if (p.role === 'infant') infantAt[pr.zone[m]] = m; }
        });
        week.people.forEach((p, i) => {
          const pr = week.presence[p.id], z = pr.zone[m];
          if (z < 0 || pr.state[m] === 2) return;
          const level = (slept[i] >= night ? after : before) / 100;
          levels[p.id][m] = level;
          if (asleepAt[z] !== m && level > target[z]) { target[z] = level; who[z][m] = -1; }
          const plan = plans[i];
          if (!plan || plan.rooms.has(z) || preference(p, m, false, zones[z]).intensity >= level) return;
          for (const r of routeBetween(z, plan.bed)) if (asleepAt[r] !== m && level >= target[r]) { target[r] = level; who[r][m] = i; }
        });
        for (let z = 0; z < Z; z++) {
          env[z] = infantAt[z] === m ? 0 : target[z] >= env[z] ? target[z] : Math.max(target[z], env[z] - fall / 100);
          out[z][m] = env[z];
        }
      }
      return (byWeek[before] = { out, who, levels });
    }
    // The floor for a zone at a moment; a rise takes the following minute, so it fades in during play.
    function floorAt(table, zone, minute) {
      const m = Math.floor(minute), c = table.out[zone], f = minute - m;
      const a = c[Math.max(0, m - 1)], b = c[Math.min(c.length - 1, m)];
      return a + (b - a) * f;
    }
    // Strip preview: the curve, lifted to the floor while the selected person, or anyone for the whole home, is awake.
    function previewAt(week, who, minute, before) {
      const owner = who === 'home' ? prefs.shared : (prefs.people[who] || prefs.shared);
      const v = sample(owner[dayTypeOf(minute)], ((minute % 1440) + 1440) % 1440);
      if (!before) return v;
      const t = floorTable(week, before);
      const ids = who === 'home' ? Object.keys(t.levels) : [who];
      const level = Math.max(0, ...ids.map(id => t.levels[id] ? t.levels[id][minute] || 0 : 0));
      return level > v.intensity ? { intensity: level, kelvin: FLOOR.kelvin, floor: true } : v;
    }
    function preference(person, minute, asleep, zone) {
      if (prefs) {
        const own = prefs.people[person.id];
        const useOwn = own && (rules.outsideOwnRoom === 'own' || !zone || (own.rooms || []).includes(zone.id));
        const v = sample((useOwn ? own : prefs.shared)[dayTypeOf(minute)], ((minute % 1440) + 1440) % 1440);
        return { intensity: asleep ? 0 : v.intensity, kelvin: v.kelvin, source: useOwn ? 'own' : 'shared' };
      }
      const id = person.lighting || byRole[person.role] || 'adult';
      const prof = profiles[id] || profiles.adult || { asleep: [0, 2200] };
      if (asleep) { const [i, k] = prof.asleep || [0, 2200]; return { intensity: i / 100, kelvin: k, profile: id }; }
      const c = curves[id] || curves.adult || [[0, 0.5, 2700]];
      const tod = ((minute % 1440) + 1440) % 1440;
      let i = c.length - 1;
      while (i > 0 && c[i][0] > tod) i--;
      const a = c[i], b = c[(i + 1) % c.length];
      const span = ((b[0] - a[0]) + 1440) % 1440 || 1440;
      const f = (((tod - a[0]) + 1440) % 1440) / span;
      return { intensity: a[1] + (b[1] - a[1]) * f, kelvin: a[2] + (b[2] - a[2]) * f, profile: id };
    }

    // Lighting for every zone at one minute of the week.
    function at(week, minute, acuity, floorPercent) {
      const m = Math.max(0, Math.min(week.presence[week.people[0].id].zone.length - 1, Math.floor(minute)));
      const occ = zones.map(() => []);
      for (const p of week.people) {
        const pr = week.presence[p.id];
        const z = pr.zone[m], st = pr.state[m];
        if (z < 0) continue;
        if (st === 3 && !rules.transitCountsAsOccupied) continue;
        occ[z].push({ person: p, asleep: st === 2 });
      }
      const out = zones.map(z => ({ zone: z, occupants: occ[z.index], intensity: 0, kelvin: 2700, rule: 'U3', reason: 'Off: no one here or within reach', source: null }));
      // Occupied zones first: only their own occupants count.
      for (const o of out) {
        const list = o.occupants;
        if (!list.length) continue;
        const infants = list.filter(x => x.person.role === 'infant');
        const sleepers = list.filter(x => x.asleep);
        let chosen, rule, reason;
        const rank = ranking[o.zone.id];
        const sleepingInfants = infants.filter(x => x.asleep);
        if (rules.sleepingInfantWins && sleepingInfants.length) { chosen = sleepingInfants; rule = 'S1'; reason = 'Infant asleep'; }
        else if (rank) {
          const rankOf = x => { const i = rank.findIndex(tier => tier.includes(x.person.id)); return i < 0 ? rank.length : i; };
          const top = Math.min(...list.map(rankOf));
          chosen = list.filter(x => rankOf(x) === top);
          const names = chosen.map(x => x.person.name).join(' and ');
          rule = 'H1';
          reason = chosen.length === list.length && chosen.length === 1 ? `${names}’s preference`
            : chosen.length === list.length ? `Average of ${names}`
            : `${names} ${chosen.length > 1 ? 'outrank' : 'outranks'} ${list.filter(x => rankOf(x) !== top).map(x => x.person.name).join(', ')}`;
          if (chosen.every(x => x.asleep)) reason += ' (asleep)';
        }
        else if (rules.infantWins && infants.length) { chosen = infants; rule = 'O1'; reason = 'Infant’s preference'; }
        else if (rules.sleeperWins && sleepers.length) { chosen = sleepers; rule = 'O2'; reason = 'Someone asleep'; }
        else { chosen = list; rule = 'O3'; reason = list.length === 1 ? list[0].person.name + '’s preference' : `Average of ${list.length} people`; }
        const vals = chosen.map(x => preference(x.person, minute, x.asleep, o.zone));
        o.intensity = vals.reduce((s, p) => s + p.intensity, 0) / vals.length;
        o.kelvin = mixKelvin(vals.map(p => p.kelvin));
        if (rule !== 'S1' && vals.every(v => v.source === 'shared')) reason = rule === 'H1' ? reason + ' · home settings' : 'Home settings';
        o.rule = rule; o.reason = reason;
      }
      // Night floor for occupied zones (a sleeping infant's zone stays off).
      const table = prefs && floorPercent ? floorTable(week, floorPercent) : null;
      if (table) for (const o of out) {
        if (!o.occupants.length || o.rule === 'S1') continue;
        const f = floorAt(table, o.zone.index, minute);
        if (f > o.intensity) { o.intensity = f; o.kelvin = FLOOR.kelvin; o.rule = 'F1'; o.reason = 'Night floor'; }
      }
      // Unoccupied zones: borrow from the brightest occupied zone in line of sight.
      const k = Math.max(0, Math.min(1, acuity));
      for (const o of out) {
        if (o.occupants.length) continue;
        let best = null;
        for (const n of neighbours[o.zone.index]) {
          const src = out[n];
          if (!src.occupants.length) continue;
          if (src.zone.private && !rules.privateLightsNeighbours) continue;
          if (!best || src.intensity > best.intensity) best = src;
        }
        if (best) {
          o.intensity = best.intensity * k; o.kelvin = best.kelvin; o.rule = 'U1'; o.source = best.zone;
          o.reason = `${Math.round(k * 100)}% of ${best.zone.name}`;
        }
      }
      // Second step: public source, through an empty public zone, to an empty public zone.
      if (rules.spillHops >= 2) for (const o of out) {
        if (o.occupants.length || o.zone.private) continue;
        for (const n of neighbours[o.zone.index]) {
          const mid = out[n];
          if (mid.occupants.length || mid.zone.private) continue;
          for (const n2 of neighbours[n]) {
            const src = out[n2];
            if (n2 === o.zone.index || !src.occupants.length || src.zone.private || src.rule === 'F1') continue;
            const v = src.intensity * k * k;
            if (v > o.intensity) {
              o.intensity = v; o.kelvin = src.kelvin; o.rule = 'U2'; o.source = src.zone;
              o.reason = `${Math.round(k * k * 100)}% of ${src.zone.name}, through ${mid.zone.name}`;
            }
          }
        }
      }
      // Route to bed: empty zones on someone's way back glow at their floor, fading after they pass.
      if (table) for (const o of out) {
        if (o.occupants.length) continue;
        const f = floorAt(table, o.zone.index, minute);
        if (f <= o.intensity) continue;
        const i = table.who[o.zone.index][m];
        o.intensity = f; o.kelvin = FLOOR.kelvin; o.rule = 'R1'; o.source = null;
        o.reason = i >= 0 ? `Route to ${week.people[i].name}’s bed` : 'Fading out';
      }
      for (const o of out) o.rgb = kelvinToRgb(o.kelvin);
      return out;
    }

    return { zones, neighbours, pairs: [...pairs.values()], rules, ranking, at, preference, kelvinToRgb, prefs, curveFor, sample, dayTypeOf, previewAt, floorTable, routeBetween, defaultFloor: FLOOR.beforeSleep, defaultAcuity: (L.acuity ?? 50) / 100 };
  }

  const api = { build, paletteRgb };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.RhythmLighting = api;
})(typeof self !== 'undefined' ? self : this);
