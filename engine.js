/*
 * Rhythm Simulator engine.
 * household.json + plan.json + seed  ->  a whole week of presence, generated before playback.
 *
 * Pipeline (each stage only reads the one before it):
 *   1. Rhythm generator   commitments per person (sleep, anchors, meals, routines), painted by priority
 *   2. Infant custody     who holds each dependent minute by minute; hand-overs become commitments
 *   3. Fillers            gaps between commitments filled from the role's weighted activity library
 *   4. Path planner       blocks become dwell / move / away segments through the doorway graph
 *   5. Presence timeline  zone + state per person per minute, and the event stream (events.json)
 *   6. Checks             the brief's "always true" rules, verified on the generated week
 */
(function (root) {
  'use strict';

  const DAY = 1440;
  const WEEK = 7 * DAY;
  const DAY_KEYS = ['mon', 'tue', 'wed', 'thu', 'fri', 'sat', 'sun'];
  const DAY_NAMES = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'];
  const isWeekend = d => d >= 5;
  const STATE_CODE = { away: 0, active: 1, asleep: 2, transit: 3 };

  // ---------------------------------------------------------------- randomness
  function hash32(str) {
    let h = 2166136261 >>> 0;
    for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 16777619); }
    return h >>> 0;
  }
  function makeRng(seed) {
    let a = hash32(String(seed)) || 1;
    const next = () => {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    return {
      next,
      int: (lo, hi) => Math.floor(lo + (hi - lo + 1) * next()),
      chance: p => next() < p,
      bell() { let u = 0; while (u === 0) u = next(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * next()); },
      weighted(items, w) {
        const total = items.reduce((s, it) => s + w(it), 0);
        let r = next() * total;
        for (const it of items) { r -= w(it); if (r <= 0) return it; }
        return items[items.length - 1];
      }
    };
  }

  // ---------------------------------------------------------------- time helpers
  const hm = s => { const [h, m] = s.split(':').map(Number); return h * 60 + m; };
  // [time, window] -> minute of day. Bell-shaped: sd = window / 2, clipped at 1.5 windows.
  const jitter = (rng, spec) => Math.round(hm(spec[0]) + Math.max(-3, Math.min(3, rng.bell())) * spec[1] / 2);
  const span = (rng, range) => rng.int(range[0], range[1]);
  // Bedtimes before noon belong to the following night (e.g. "00:45").
  const nightTime = m => (m < 12 * 60 ? m + DAY : m);

  function isoAt(weekStart, minute) {
    const [Y, M, D] = weekStart.split('-').map(Number);
    return new Date(Date.UTC(Y, M - 1, D) + Math.round(minute * 60) * 1000).toISOString().slice(0, 19);
  }
  function clock(minute) {
    const m = ((Math.floor(minute) % DAY) + DAY) % DAY;
    return String(Math.floor(m / 60)).padStart(2, '0') + ':' + String(m % 60).padStart(2, '0');
  }

  // ---------------------------------------------------------------- geometry
  function pointInPolygon(x, y, poly) {
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const [xi, yi] = poly[i], [xj, yj] = poly[j];
      if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  // ---------------------------------------------------------------- spatial model
  function buildPlan(plan, speedMps) {
    const unitM = plan.metersPerUnit || 0.3048;
    const zones = [], rooms = [];
    for (const room of plan.rooms) {
      rooms.push(room);
      const zs = room.zones && room.zones.length ? room.zones : [{ id: room.id, name: room.name, polygon: room.polygon }];
      for (const z of zs) zones.push({ id: z.id, name: z.name, room: room.id, roomName: room.name, type: room.type, level: room.level, polygon: z.polygon, lighting: z.lighting || {} });
    }
    zones.forEach((z, i) => { z.index = i; });
    const zoneIndex = Object.fromEntries(zones.map(z => [z.id, z.index]));
    const zoneAt = (level, x, y) => {
      for (const z of zones) if (z.level === level && pointInPolygon(x, y, z.polygon)) return z.index;
      return -1;
    };
    const roomAt = (level, x, y) => {
      for (const r of rooms) if (r.level === level && pointInPolygon(x, y, r.polygon)) return r.id;
      return 'outside';
    };

    const nodes = {};
    for (const [id, [level, x, y]] of Object.entries(plan.nodes)) {
      nodes[id] = { id, level, x, y, adj: [], zone: zoneAt(level, x, y), room: roomAt(level, x, y) };
    }
    const secFor = feet => (feet * unitM) / speedMps;
    const link = (a, b, sec, via) => {
      nodes[a].adj.push({ to: b, sec, via: via || null });
      nodes[b].adj.push({ to: a, sec, via: via ? via.slice().reverse() : null });
    };
    const badEdges = [];
    for (const [a, b] of plan.edges) {
      if (!nodes[a] || !nodes[b]) { badEdges.push([a, b]); continue; }
      link(a, b, secFor(Math.hypot(nodes[a].x - nodes[b].x, nodes[a].y - nodes[b].y)));
    }
    for (const s of plan.stairs || []) link(s.from, s.to, s.seconds, s.via);

    // Shortest paths: Dijkstra from each source on demand, cached.
    const cache = {};
    function tree(src) {
      if (cache[src]) return cache[src];
      const dist = {}, prev = {}, done = new Set();
      for (const id in nodes) dist[id] = Infinity;
      dist[src] = 0;
      for (;;) {
        let u = null, best = Infinity;
        for (const id in dist) if (!done.has(id) && dist[id] < best) { best = dist[id]; u = id; }
        if (u === null) break;
        done.add(u);
        for (const e of nodes[u].adj) {
          const nd = dist[u] + e.sec;
          if (nd < dist[e.to]) { dist[e.to] = nd; prev[e.to] = { from: u, edge: e }; }
        }
      }
      return (cache[src] = { dist, prev });
    }
    // Route as timed points: [{l, x, y, s}] where s is seconds from departure.
    function route(a, b) {
      if (a === b) return { sec: 0, pts: [{ l: nodes[a].level, x: nodes[a].x, y: nodes[a].y, s: 0 }] };
      const { dist, prev } = tree(a);
      if (!isFinite(dist[b])) return null;
      const hops = [];
      for (let v = b; v !== a; v = prev[v].from) hops.push(prev[v]);
      hops.reverse();
      const pts = [{ l: nodes[a].level, x: nodes[a].x, y: nodes[a].y, s: 0 }];
      let s = 0;
      for (const h of hops) {
        const to = nodes[h.edge.to];
        if (h.edge.via) {
          const [v1, v2] = h.edge.via;
          pts.push({ l: v1[0], x: v1[1], y: v1[2], s: s + h.edge.sec / 2 });
          pts.push({ l: v2[0], x: v2[1], y: v2[2], s: s + h.edge.sec / 2 });
        }
        s += h.edge.sec;
        pts.push({ l: to.level, x: to.x, y: to.y, s });
      }
      return { sec: s, pts };
    }

    // Static check: every walkable edge crosses rooms only through a doorway or opening.
    function wallCrossings() {
      const problems = [];
      const seen = new Set();
      for (const [a, b] of plan.edges) {
        const A = nodes[a], B = nodes[b];
        if (!A || !B || seen.has(a + '|' + b)) continue;
        seen.add(a + '|' + b);
        const len = Math.hypot(B.x - A.x, B.y - A.y);
        const n = Math.max(2, Math.ceil(len / 0.2));
        let prevRoom = roomAt(A.level, A.x, A.y), px = A.x, py = A.y;
        for (let i = 1; i <= n; i++) {
          const x = A.x + (B.x - A.x) * i / n, y = A.y + (B.y - A.y) * i / n;
          const r = roomAt(A.level, x, y);
          if (r !== prevRoom) {
            const cx = (x + px) / 2, cy = (y + py) / 2;
            const door = (plan.doorways || []).find(d => d.level === A.level && d.rooms.includes(r) && d.rooms.includes(prevRoom) &&
              Math.hypot(cx - d.at[0], cy - d.at[1]) <= d.width / 2 + 0.6);
            if (!door) problems.push({ edge: [a, b], from: prevRoom, to: r, at: [+cx.toFixed(1), +cy.toFixed(1)] });
          }
          prevRoom = r; px = x; py = y;
        }
      }
      return problems;
    }

    return { raw: plan, unitM, zones, zoneIndex, rooms, nodes, places: plan.places, exits: plan.exits, route, zoneAt, roomAt, wallCrossings, badEdges };
  }

  // ---------------------------------------------------------------- agenda (painted interval map)
  class Agenda {
    constructor() { this.items = []; }
    // Paint a block over whatever is there; the newer block wins where they overlap.
    paint(c) {
      if (!(c.t1 > c.t0)) return;
      const out = [];
      for (const it of this.items) {
        if (it.t1 <= c.t0 || it.t0 >= c.t1) { out.push(it); continue; }
        if (it.t0 < c.t0) out.push(Object.assign({}, it, { t1: c.t0 }));
        if (it.t1 > c.t1) out.push(Object.assign({}, it, { t0: c.t1 }));
      }
      out.push(c);
      out.sort((a, b) => a.t0 - b.t0);
      this.items = out;
    }
    at(t) {
      const a = this.items;
      let lo = 0, hi = a.length - 1;
      while (lo <= hi) {
        const mid = (lo + hi) >> 1;
        if (a[mid].t1 <= t) lo = mid + 1; else if (a[mid].t0 > t) hi = mid - 1; else return a[mid];
      }
      return null;
    }
    gaps(from, to) {
      const g = [];
      let t = from;
      for (const it of this.items) {
        if (it.t0 > t + 1e-6) g.push([t, Math.min(it.t0, to)]);
        t = Math.max(t, it.t1);
        if (t >= to) break;
      }
      if (t < to - 1e-6) g.push([t, to]);
      return g.filter(([a, b]) => b - a > 1e-6);
    }
  }

  // ---------------------------------------------------------------- generator
  function generate(household, plan, options) {
    const started = (typeof performance !== 'undefined' ? performance : Date).now();
    const H = household;
    const seed = (options && options.seed) || H.seed || 'seed';
    const P = buildPlan(plan, H.walkingSpeed || 1);
    const R = key => makeRng(seed + '|' + key);
    const warnings = [];
    const opts = Object.assign({}, H.options || {}, (options && options.overrides) || {});

    // --- people
    const people = [];
    for (const o of H.occupants) people.push(Object.assign({}, o));
    for (const g of H.guests || []) {
      for (let i = 0; i < g.count; i++) {
        people.push({
          id: 'guest' + (i + 1), name: 'Guest ' + (i + 1), initial: String(i + 1), role: 'guest', presence: 'visitor',
          color: (g.colors && g.colors[i % g.colors.length]) || '#B8687E', group: g
        });
      }
    }
    people.forEach((p, i) => { p.idx = i; p.agenda = new Agenda(); p.commits = []; });
    const byId = Object.fromEntries(people.map(p => [p.id, p]));
    const residents = people.filter(p => p.presence === 'resident');
    const adults = people.filter(p => p.role.startsWith('adult'));
    const children = people.filter(p => p.role === 'child');
    const infants = people.filter(p => p.role === 'infant');
    const caregivers = people.filter(p => p.role === 'caregiver');
    const guests = people.filter(p => p.role === 'guest');
    const responsible = adults.concat(caregivers);
    if (residents.length > 6) warnings.push('More than 6 residents; the brief caps a household at 6.');
    if (guests.length > 4) warnings.push('More than 4 guests at once; the brief caps guests at 4.');

    const commit = (p, t0, t1, f, prio) => { if (p && t1 > t0) p.commits.push(Object.assign({ t0, t1, prio, state: 'active' }, f)); };
    const place = (name, act, label, extra) => Object.assign({ place: name, act, label }, extra || {});
    const away = (label, act, extra) => Object.assign({ away: label, act }, extra || {});
    const days = H.days || {};
    const dayCfg = d => days[DAY_KEYS[d]] || {};
    const afterLate = d => d > 0 && (dayCfg(d - 1).hosting || dayCfg(d - 1).lateNight);

    // ---------------------------------------------------- infant facts (needed first: they set the early carer's wake)
    const infantFacts = {};
    for (const inf of infants) {
      const f = { wake: [], bed: [], naps: [], nightWakes: [] };
      for (let d = 0; d < 7; d++) {
        const rng = R(inf.id + '|day|' + d);
        f.wake[d] = d * DAY + jitter(rng, isWeekend(d) ? inf.wake.weekend : inf.wake.weekday);
        f.bed[d] = d * DAY + nightTime(jitter(rng, isWeekend(d) ? inf.sleep.weekend : inf.sleep.weekday));
        f.naps[d] = (inf.naps || []).map(n => { const s = d * DAY + jitter(rng, n.at); return { s, e: s + span(rng, n.minutes) }; });
      }
      // Night wakes for the night before Monday (n = -1) through Sunday night.
      const nw = inf.nightWakes;
      for (let n = -1; n < 7 && nw; n++) {
        const rng = R(inf.id + '|night|' + n);
        const lo = (n + 1) * DAY + hm(nw.between[0]) - DAY, hi = (n + 1) * DAY + hm(nw.between[1]);
        const count = span(rng, nw.count);
        const times = [];
        for (let i = 0; i < 20 && times.length < count; i++) {
          const t = lo + rng.int(0, hi - lo);
          if (times.every(x => Math.abs(x - t) > 90)) times.push(t);
        }
        times.sort((a, b) => a - b);
        for (const t of times) {
          const e = t + span(rng, nw.minutes);
          if (t > 2 && e < WEEK - 1) f.nightWakes.push({ s: t, e });
        }
      }
      infantFacts[inf.id] = f;
    }
    const earlyCarerOf = (inf, d) => {
      const ec = inf.earlyCarer || {};
      return byId[(d === 5 && ec.sat) || (d === 6 && ec.sun) || (d < 5 && ec.weekday) || ''] || null;
    };

    // ---------------------------------------------------- wake and sleep
    const wakeAt = {}, bedAt = {};
    for (const p of residents.filter(p => p.role !== 'infant')) {
      wakeAt[p.id] = []; bedAt[p.id] = [];
      for (let d = 0; d < 7; d++) {
        const rng = R(p.id + '|sleep|' + d);
        let w = d * DAY + jitter(rng, isWeekend(d) ? p.wake.weekend : p.wake.weekday);
        const nextWeekend = d === 4 || d === 5;
        let b = d * DAY + nightTime(jitter(rng, nextWeekend ? p.sleep.weekend : p.sleep.weekday));
        const dc = dayCfg(d);
        if (p.role === 'child' && dc.kidSleep) b = d * DAY + nightTime(jitter(rng, dc.kidSleep));
        if (p.role.startsWith('adult')) {
          if (dc.hosting && dc.bedShift) b += dc.bedShift;
          if (dc.lateNight && dc.lateNight[p.id]) b = d * DAY + nightTime(jitter(rng, dc.lateNight[p.id]));
          if (afterLate(d)) w += ((H.exceptions || {}).wakeShiftAfterLateNight || {})[isWeekend(d) ? 'weekend' : 'weekday'] || 0;
        }
        for (const inf of infants) if (earlyCarerOf(inf, d) === p) w = infantFacts[inf.id].wake[d] - 2;
        wakeAt[p.id][d] = w; bedAt[p.id][d] = b;
      }
    }

    // ---------------------------------------------------- 1. commitments
    for (const p of residents.filter(p => p.role !== 'infant')) {
      const bedPlace = p.bed;
      const rngN = R(p.id + '|nights');
      for (let d = 0; d <= 7; d++) {
        const from = d === 0 ? 0 : bedAt[p.id][d - 1];
        const to = d === 7 ? WEEK : wakeAt[p.id][d];
        commit(p, from, Math.min(to, WEEK), place(bedPlace, 'sleep', 'Asleep', { state: 'asleep' }), 1);
        // Night bathroom trip.
        if (p.nightBathroomChance && rngN.chance(p.nightBathroomChance) && to - from > 240) {
          const t = from + 60 + rngN.int(0, to - from - 150);
          commit(p, t, t + 4, place(p.role === 'child' ? 'bath2.wc' : 'pbath.wc', 'ready', 'Bathroom at night'), 7);
        }
      }
      if (p.role.startsWith('adult')) {
        for (let d = 0; d < 7; d++) commit(p, bedAt[p.id][d] - 10, bedAt[p.id][d], place('pbath.vanity', 'ready', 'Getting ready for bed', { busy: true }), 2);
      }
    }

    // Adults: anchors (work), morning paths, weekend mornings.
    for (const p of adults) {
      for (let d = 0; d < 7; d++) {
        const rng = R(p.id + '|day|' + d);
        const dk = DAY_KEYS[d];
        const w = wakeAt[p.id][d];
        const isEarly = infants.some(inf => earlyCarerOf(inf, d) === p);
        const work = (p.anchors || []).filter(a => a.days.includes(dk));
        if (work.length) {
          for (const a of work) {
            const cfg = Object.assign({}, a, (a.byDay || {})[dk] || {});
            const dep = d * DAY + jitter(rng, cfg.depart), ret = d * DAY + jitter(rng, cfg.return);
            // Morning path: weighted archetype, then free time until departure.
            if (p.morningPaths) {
              const path = rng.weighted(p.morningPaths, x => x.weight);
              let t = w;
              for (const [pl, lo, hi, act, label] of path.steps) {
                const e = Math.min(t + rng.int(lo, hi), dep - 4);
                commit(p, t, e, place(pl, act, label, { busy: true, path: path.id }), 2);
                t = e;
              }
            }
            commit(p, dep - 3, dep, place('entry.bench', 'ready', 'Heading out', { busy: true }), 4);
            commit(p, dep, ret, away(cfg.label, 'away', { exit: cfg.exit, takeInfant: cfg.infant === 'never' ? false : true }), 4);
            commit(p, ret, ret + 2, place('entry.bench', 'free', 'Home'), 4);
            if (p.forgetChance && rng.chance(p.forgetChance)) {
              const f = dep + rng.int(5, 10);
              commit(p, f, f + 2, place('office.desk', 'ready', 'Back for something forgotten', { busy: true }), 5);
              commit(p, f + 2, f + 3, place('entry.bench', 'ready', 'Heading out again', { busy: true }), 5);
            }
          }
        } else if (!isWeekend(d) && isEarly && p.morningPaths) {
          const path = rng.weighted(p.morningPaths, x => x.weight);
          let t = w;
          for (const [pl, lo, hi, act, label] of path.steps) { const e = t + rng.int(lo, hi); commit(p, t, e, place(pl, act, label, { path: path.id }), 2); t = e; }
        } else if (isWeekend(d)) {
          if (isEarly) commit(p, w, w + rng.int(15, 22), place('primary.chair', 'care', 'Feeding the baby'), 2);
          else commit(p, w, w + rng.int(10, 16), place('pbath.shower', 'ready', 'Shower', { busy: true }), 2);
        }
      }
    }

    // Children: school anchors, escorts, evenings.
    const kidHome = {}; // child id -> day -> minute they are back home (school days)
    for (const c of children) {
      kidHome[c.id] = [];
      for (let d = 0; d < 7; d++) {
        const rng = R(c.id + '|day|' + d);
        const dk = DAY_KEYS[d];
        const w = wakeAt[c.id][d], bed = bedAt[c.id][d];
        const school = (c.anchors || []).find(a => a.days.includes(dk));
        if (school) {
          const dep = d * DAY + jitter(rng, school.depart);
          const after = school.after && school.after.byDay && school.after.byDay[dk];
          const ret = d * DAY + jitter(rng, after ? after.return : school.return);
          const waker = byId[c.wokenBy];
          if (waker) commit(waker, w - 2, w + 1, place('kid.bedside', 'care', 'Waking the kid'), 6);
          const path = rng.weighted(c.morningPaths || [{ steps: [], weight: 1 }], x => x.weight);
          let t = w;
          for (const [pl, lo, hi, act, label] of path.steps) { const e = Math.min(t + rng.int(lo, hi), dep - 4); commit(c, t, e, place(pl, act, label), 2); t = e; }
          commit(c, dep - 4, dep, place('entry.bench', 'ready', 'Shoes and bag'), 4);
          const afterFrom = after ? d * DAY + hm(school.after.from) : ret;
          commit(c, dep, afterFrom, away(school.label, 'away', { exit: school.exit }), 4);
          if (after) commit(c, afterFrom, ret, away(after.label, 'activity', { exit: school.exit }), 4);
          commit(c, ret, ret + 2, place('entry.bench', 'free', 'Home'), 4);
          kidHome[c.id][d] = ret;
          const esc = byId[school.escort];
          if (esc) {
            const drop = span(rng, school.escortMinutes), pick = span(rng, school.escortMinutes);
            if (waker === esc) commit(esc, w + 1, dep - 2, place('kitchen.cook', 'meal', 'Making breakfast'), 3);
            commit(esc, dep - 2, dep, place('entry.bench', 'ready', 'Heading out'), 4);
            commit(esc, dep, dep + drop, away('School drop-off', 'activity', { exit: school.exit, takeInfant: true }), 4);
            commit(esc, ret - pick - 2, ret - pick, place('entry.bench', 'ready', 'Heading out'), 4);
            commit(esc, ret - pick, ret, away((after ? after.label : school.label) + ' pick-up', 'activity', { exit: school.exit, takeInfant: true }), 4);
            commit(esc, ret, ret + 2, place('entry.bench', 'free', 'Home'), 4);
          }
        }
        // Evening: movie night, or bath; then a story in bed.
        const ev = c.evening || { bath: [15, 20], story: [12, 18] };
        const story = span(rng, ev.story);
        const movie = dayCfg(d).movieNight;
        if (movie && movie.who.includes(c.id)) {
          commit(c, bed - story - 8, bed - story, place('bath2.basin', 'ready', 'Brushing teeth'), 3);
        } else {
          const bath = span(rng, ev.bath);
          commit(c, bed - story - bath, bed - story, place('bath2.tub', 'ready', 'Bath'), 3);
        }
        commit(c, bed - story, bed, place('kid.bed', 'free', 'Story in bed'), 3);
        const teller = rng.weighted(adults, () => 1);
        const t2 = teller.commits.some(k => k.away && k.t0 < bed && k.t1 > bed - story) ? adults.find(a => a !== teller) : teller;
        if (t2) commit(t2, bed - story, bed, place('kid.bedside', 'care', 'Bedtime story'), 3);
      }
    }

    // Movie night.
    for (let d = 0; d < 7; d++) {
      const mv = dayCfg(d).movieNight;
      if (!mv) continue;
      const rng = R('movie|' + d);
      const s = d * DAY + jitter(rng, mv.at), e = d * DAY + jitter(rng, mv.until);
      for (const id of mv.who) commit(byId[id], s, byId[id] && byId[id].role === 'child' ? Math.min(e, bedAt[id][d] - 25) : e, place(mv.place, 'free', 'Movie night'), 3);
    }

    // Errands for home adults.
    for (const p of adults.filter(a => a.errands)) {
      const er = p.errands;
      for (let d = 0; d < 5; d++) {
        const rng = R(p.id + '|errands|' + d);
        const pickN = rng.weighted(er.perDay.map((w, i) => ({ w, i })), x => x.w).i;
        const taken = p.commits.filter(k => k.away && k.t1 > d * DAY && k.t0 < (d + 1) * DAY).map(k => [k.t0 - 20, k.t1 + 20]);
        for (let i = 0; i < pickN; i++) {
          for (let tries = 0; tries < 12; tries++) {
            const len = span(rng, er.minutes);
            const s = d * DAY + hm(er.between[0]) + rng.int(0, Math.max(0, hm(er.between[1]) - hm(er.between[0]) - len));
            const e = s + len;
            if (taken.some(([a, b]) => s < b && e > a)) continue;
            taken.push([s - 20, e + 20]);
            commit(p, s, e, away(er.label, 'activity', { exit: er.exit || 'front', takeInfant: rng.chance(er.infantChance) ? 'want' : false }), 4);
            break;
          }
        }
      }
    }

    // Meals.
    const meals = H.meals || {};
    const outing = [];
    for (let d = 0; d < 7; d++) {
      const rng = R('household|' + d);
      const dc = dayCfg(d);
      const family = residents.filter(p => p.role !== 'infant');
      // Weekend: family breakfast after the last one is up; an outing; lunch at home if there is no outing then.
      if (isWeekend(d)) {
        const bf = meals.weekendBreakfast;
        let bfEnd = d * DAY + 9 * 60;
        if (bf) {
          const last = Math.max(...family.map(p => wakeAt[p.id][d]));
          const s = last + span(rng, bf.afterLastWake), e = s + span(rng, bf.minutes);
          for (const p of family) commit(p, s, e, place(bf.place, 'meal', 'Family breakfast'), 3);
          bfEnd = e;
        }
        const oc = (H.outings || {})[DAY_KEYS[d]];
        if (oc && rng.chance(oc.chance)) {
          let s = Math.max(d * DAY + jitter(rng, oc.at), bfEnd + 15);
          const e = s + span(rng, oc.minutes);
          outing[d] = [s, e];
          for (const p of family) {
            commit(p, s - 4, s, place('entry.bench', 'ready', 'Getting everyone out'), 5);
            commit(p, s, e, away(oc.label, 'activity', { exit: oc.exit, takeInfant: true }), 5);
            commit(p, e, e + 2, place('entry.bench', 'free', 'Home'), 5);
          }
        }
        const lu = meals.weekendLunch;
        if (lu) {
          const s = d * DAY + jitter(rng, lu.at), e = s + span(rng, lu.minutes);
          if (!(outing[d] && s < outing[d][1] && e > outing[d][0])) for (const p of family) commit(p, s, e, place(lu.place, 'meal', 'Lunch'), 3);
        }
      }
      // Dinner (hosting days have a social dinner instead).
      if (meals.dinner && !dc.hosting) {
        let s = d * DAY + jitter(rng, isWeekend(d) ? meals.dinner.weekend : meals.dinner.weekday);
        for (const c of children) if (kidHome[c.id][d]) s = Math.max(s, kidHome[c.id][d] + 10);
        const e = s + span(rng, meals.dinner.minutes);
        for (const p of family) {
          const outAt = p.commits.filter(k => k.away && k.t0 < e - 10 && k.t1 > s);
          if (!outAt.length) commit(p, s, e, place(meals.dinner.place, 'meal', 'Dinner'), 3);
          else {
            const back = Math.max(...outAt.map(k => k.t1)) + 3;
            if (back < e - 8) commit(p, back, e, place(meals.dinner.place, 'meal', 'Dinner (late)'), 3);
          }
        }
      }
    }

    // Guests and hosting.
    const socialWindow = [];
    for (const g of H.guests || []) {
      const d = DAY_KEYS.indexOf(g.day);
      if (d < 0) continue;
      const rng = R('guests|' + d);
      const gs = guests.filter(p => p.group === g);
      const arrivals = gs.map(() => d * DAY + jitter(rng, g.arrive)).sort((a, b) => a - b);
      const leaves = gs.map(() => d * DAY + nightTime(jitter(rng, g.leave))).sort((a, b) => a - b);
      gs.forEach((p, i) => {
        const a = arrivals[i], l = leaves[i];
        commit(p, 0, a, away('Not here', 'away', { hidden: true }), 4);
        commit(p, a, a + 3, place('entry.bench', 'social', 'Arriving'), 4);
        commit(p, l - 3, l, place('entry.bench', 'social', 'Saying goodbye'), 4);
        commit(p, l, WEEK, away('Gone home', 'away', { hidden: true }), 4);
      });
      socialWindow[d] = [arrivals[0] - 15, leaves[leaves.length - 1]];
      const hosts = (g.hosts || []).map(id => byId[id]).filter(Boolean);
      const cook = byId[dayCfg(d).cookFor];
      if (cook) {
        const home = Math.max(...cook.commits.filter(k => k.away && k.t0 < arrivals[0] && k.t1 > d * DAY + 12 * 60).map(k => k.t1), d * DAY + 16 * 60);
        commit(cook, home + 8, arrivals[0] - 4, place('kitchen.cook', 'meal', 'Cooking for guests'), 3);
      }
      if (hosts[0]) commit(hosts[0], arrivals[0] - 2, arrivals[0] + 3, place('entry.bench', 'social', 'Welcoming guests'), 4);
      if (g.dinner) {
        const s = arrivals[0] + span(rng, g.dinner.after), e = s + span(rng, g.dinner.minutes);
        const atTable = hosts.concat(gs).concat(children.filter(c => bedAt[c.id][d] > s + 30));
        if (opts.nannyStaysThursday) atTable.push(...caregivers);
        for (const p of atTable) commit(p, s, p.role === 'child' ? Math.min(e, bedAt[p.id][d] - 30) : e, place(g.dinner.place, 'social', 'Dinner with guests'), 4);
      }
    }
    const lateWindow = [];
    for (let d = 0; d < 7; d++) {
      if (!dayCfg(d).lateNight) continue;
      const kidBed = Math.max(...children.map(c => bedAt[c.id][d]), d * DAY + 21 * 60);
      lateWindow[d] = [kidBed, d * DAY + DAY + 4 * 60];
    }

    // Night wakes: the night carer gets up to the chair in their own zone.
    for (const inf of infants) {
      const nw = inf.nightWakes;
      const carer = nw && byId[nw.carer];
      if (!carer) continue;
      for (const w of infantFacts[inf.id].nightWakes) commit(carer, w.s + 1, w.e - 2, place(nw.place, 'care', 'Night feed'), 7);
    }

    // Paint everyone except caregivers (their leaving time depends on who is home).
    const paintAll = list => { for (const p of list) { p.commits.sort((a, b) => a.prio - b.prio || a.t0 - b.t0); for (const c of p.commits) p.agenda.paint(c); p.commits = []; } };
    paintAll(people.filter(p => p.role !== 'caregiver'));

    const awayAt = (p, t) => { const b = p.agenda.at(t + 0.5); return !!(b && b.away); };
    for (const n of caregivers) {
      let lastLeave = 0;
      for (let d = 0; d < 7; d++) {
        const dk = DAY_KEYS[d];
        if (!n.days.includes(dk)) continue;
        const rng = R(n.id + '|day|' + d);
        const cfg = Object.assign({}, n, (n.byDay || {})[dk] || {});
        const arr = d * DAY + jitter(rng, cfg.arrive);
        let leave = d * DAY + jitter(rng, dayCfg(d).hosting && opts.nannyStaysThursday && n.thursdayStay ? n.thursdayStay.leave : cfg.leave);
        // Never leave the charges without a resident adult at home: wait for one to be back.
        for (let guard = 0; guard < 60; guard++) {
          const someone = adults.some(a => !awayAt(a, leave) && !awayAt(a, leave - 3) && !awayAt(a, leave + 5));
          if (someone) break;
          leave += 5;
        }
        commit(n, lastLeave, arr, away('Off duty', 'away', { hidden: true, exit: cfg.exit }), 4);
        commit(n, arr, arr + 2, place('entry.bench', 'care', 'Arriving'), 4);
        commit(n, leave - 2, leave, place('entry.bench', 'care', 'Heading home'), 4);
        lastLeave = leave;
      }
      commit(n, lastLeave, WEEK, away('Off duty', 'away', { hidden: true }), 4);
    }
    paintAll(caregivers);

    // ---------------------------------------------------- 2. custody of dependents
    const custody = {}; // infant id -> { holderAt: Int16Array, phase: Int8Array, transitions }
    for (const inf of infants) {
      const F = infantFacts[inf.id];
      const phase = new Int8Array(WEEK).fill(1); // 0 awake, 1 night sleep, 2 nap, 3 night wake
      for (let d = 0; d < 7; d++) {
        phase.fill(0, F.wake[d], Math.min(F.bed[d], WEEK));
        for (const n of F.naps[d]) phase.fill(2, n.s, n.e);
      }
      for (const w of F.nightWakes) phase.fill(3, w.s, w.e);
      const carers = (inf.dependsOn || []).map(id => byId[id]).filter(Boolean);
      const nightCarer = inf.nightWakes && byId[inf.nightWakes.carer];
      const rng = R(inf.id + '|custody');

      const blockAt = (p, m) => p.agenda.at(m + 0.5);
      const homeAt = (p, m) => !awayAt(p, m);
      const freeAt = (p, m) => { const b = blockAt(p, m); return !b || (!b.away && b.state !== 'asleep' && !b.busy); };
      const leavingSoon = p => m => { for (let k = 1; k <= 4; k++) { const b = blockAt(p, m + k); if (b && b.away && !b.takeInfant) return true; } return false; };
      const available = (p, m) => freeAt(p, m) && freeAt(p, m - 2) && !leavingSoon(p)(m);
      const homeFor = (p, m) => { let k = 0; while (k < 12 && homeAt(p, m - k)) k++; return k; };
      const outWith = [];
      for (const p of carers) for (const b of p.agenda.items) if (b.away && b.takeInfant === 'want') outWith.push({ p, s: b.t0 - 3, e: b.t1 });

      const holderAt = new Int16Array(WEEK).fill(-1);
      const transitions = [];
      let holder = null, since = 0, swapAfter = span(rng, inf.weekendSwapMinutes || [90, 120]);
      for (let m = 0; m < WEEK; m++) {
        const ph = phase[m];
        const d = Math.floor(m / DAY), tod = m % DAY;
        let want = holder;
        if (ph === 3 && nightCarer) want = nightCarer;
        else if (ph === 1 || ph === 2) {
          const leaving = q => homeAt(q, m) && !homeAt(q, m + 3) && blockAt(q, m + 3) && blockAt(q, m + 3).takeInfant;
          const stays = responsible.some(q => q !== holder && homeAt(q, m) && homeAt(q, m + 5));
          if (holder && !homeAt(holder, m)) want = holder;                         // asleep in the car seat
          else if (!stays) {
            if (holder && homeAt(holder, m) && !homeAt(holder, m + 5)) want = holder;
            else want = carers.find(q => leaving(q)) || (holder && homeFor(holder, m) < 6 ? holder : null);
          } else want = holder && homeFor(holder, m) < 6 ? holder : null;
        } else {
          const prevPh = m > 0 ? phase[m - 1] : 1;
          const early = earlyCarerOf(inf, d);
          const out = outWith.find(o => m >= o.s && m < o.e && phase[Math.max(0, o.s)] === 0 && phase[Math.min(WEEK - 1, o.s + 3)] === 0);
          if (holder && !homeAt(holder, m)) want = holder;                         // out together
          else if (holder && homeAt(holder, m) && !homeAt(holder, m - 2)) want = holder; // just walked in
          else if (prevPh === 1 && early && !holder) want = early;                 // morning wake
          else if (out) want = out.p;
          else {
            const avail = carers.filter(p => available(p, m));
            const pro = avail.find(p => p.role === 'caregiver');
            const goingWith = holder && homeAt(holder, m) && blockAt(holder, m + 3) && blockAt(holder, m + 3).away && blockAt(holder, m + 3).takeInfant === true;
            if (goingWith) want = holder;
            else if (pro) want = pro;
            else if (holder && available(holder, m)) {
              want = holder;
              if (isWeekend(d) && tod > 7.5 * 60 && tod < 18.5 * 60 && m - since > swapAfter) {
                const other = avail.find(p => p !== holder && p.role.startsWith('adult'));
                if (other) { want = other; swapAfter = span(rng, inf.weekendSwapMinutes || [90, 120]); }
              }
            } else want = avail[0] || (holder && homeAt(holder, m) ? holder : responsible.find(q => homeAt(q, m) && freeAt(q, m))) || holder;
          }
        }
        if (want !== holder) { transitions.push({ m, from: holder, to: want, phase: ph, prevPhase: m > 0 ? phase[m - 1] : 1 }); holder = want; since = m; }
        holderAt[m] = holder ? holder.idx : -1;
      }

      // Hand-overs become commitments: walk to the crib, or meet the other carer.
      const cribFor = ph => (ph === 2 ? inf.napPlace : inf.nightPlace);
      for (const tr of transitions) {
        const { m, from, to } = tr;
        if (!from && to) {
          if (homeAt(to, m)) commit(to, m - 1.5, m + 1, place(cribFor(tr.prevPhase === 0 ? tr.phase : tr.prevPhase), 'care', 'Picking up the baby'), 8);
        } else if (from && !to) {
          const settle = tr.phase === 2 ? 8 : (tr.prevPhase === 3 ? 2 : (tr.prevPhase === 0 ? 12 : 3));
          const s = Math.max(m - settle, m - homeFor(from, m) + 1);
          commit(from, s, m, place(cribFor(tr.phase), 'care', tr.phase === 2 ? 'Putting the baby down for a nap' : 'Putting the baby to bed'), 8);
        } else if (from && to) {
          if (!homeAt(from, m) || !homeAt(to, m)) continue;
          const fb = blockAt(from, m);
          const departing = q => { const b = blockAt(q, m + 3); return b && b.away; };
          if (fb && fb.place && fb.t1 > m + 1 && !departing(from) && !departing(to)) {
            commit(to, m - 2, m + 1, place(fb.place, 'care', 'Taking the baby'), 8);
          } else {
            const meet = departing(from) || departing(to) ? 'entry.bench' : 'kitchen.island';
            commit(from, m - 2, m, place(meet, 'care', 'Handing over the baby'), 8);
            commit(to, m - 2, m + 1, place(meet, 'care', 'Taking the baby'), 8);
          }
        }
      }
      custody[inf.id] = { holderAt, phase, transitions };
    }
    paintAll(people.filter(p => p.role !== 'infant'));

    // ---------------------------------------------------- 3. fillers
    const fillers = H.fillers || {};
    const holdsAt = (p, m) => infants.some(inf => custody[inf.id] && custody[inf.id].holderAt[Math.max(0, Math.min(WEEK - 1, Math.floor(m)))] === p.idx);
    const inWin = (win, t) => { const d = Math.floor(t / DAY); for (const dd of [d, d - 1]) { const w = win[dd]; if (w && t >= w[0] && t < w[1]) return true; } return false; };
    function modeFor(p, t) {
      const d = Math.floor(t / DAY), tod = t % DAY, holding = holdsAt(p, t);
      const social = inWin(socialWindow, t), late = inWin(lateWindow, t);
      if (p.role === 'guest') return ['guest', 'social'];
      if (p.role === 'caregiver') return ['caregiver', social ? 'social' : holding ? 'withInfant' : 'idle'];
      if (p.role === 'child') return ['child', social ? 'social' : isWeekend(d) ? 'weekend' : 'afternoon'];
      if (holding) return ['adult', 'withInfant'];
      if (social) return ['adult', 'social'];
      if (late) return ['adult', 'late'];
      if (isWeekend(d)) return ['adult', tod < 17 * 60 ? 'weekend' : 'evening'];
      return ['adult', tod < 12 * 60 ? 'morning' : tod < 17 * 60 ? 'day' : 'evening'];
    }
    function nextBreak(p, t) {
      // Mode boundaries: noon, 17:00, custody changes, social and late windows.
      let best = Infinity;
      const d = Math.floor(t / DAY);
      for (const b of [d * DAY + 12 * 60, d * DAY + 17 * 60, (d + 1) * DAY]) if (b > t + 1e-6) best = Math.min(best, b);
      for (const win of [socialWindow, lateWindow]) for (const w of win) if (w) for (const b of w) if (b > t + 1e-6) best = Math.min(best, b);
      const startHold = holdsAt(p, t);
      for (let m = Math.ceil(t + 1e-6); m < Math.min(best, WEEK); m++) if (holdsAt(p, m) !== startHold) { best = m; break; }
      return best;
    }
    for (const p of people) {
      if (p.role === 'infant') continue;
      const rng = R(p.id + '|fill');
      for (const [g0, g1] of p.agenda.gaps(0, WEEK)) {
        let t = g0;
        let prev = p.agenda.at(g0 - 0.01);
        let prevPlace = prev && prev.place;
        const recent = [];
        while (t < g1 - 1e-6) {
          const [lib, mode] = modeFor(p, t);
          const set = (fillers[lib] && fillers[lib][mode]) || (fillers.adult && fillers.adult.evening) || [];
          const limit = Math.min(g1, nextBreak(p, t));
          // Prefer fillers allowed at this hour that were not just done; relax in that order.
          const tod = t % DAY;
          const inHours = f => !f[6] || (tod >= hm(f[6].split('-')[0]) && tod < hm(f[6].split('-')[1]));
          const tiers = [
            set.filter(f => inHours(f) && !recent.includes(f[4]) && f[0] !== prevPlace),
            set.filter(f => inHours(f) && f[0] !== prevPlace),
            set.filter(f => f[0] !== prevPlace && !f[6])
          ];
          const options = tiers.find(o => o.length) || set;
          const f = options.length ? rng.weighted(options, x => x[5]) : null;
          if (!f) { p.agenda.paint({ t0: t, t1: limit, place: 'living.sofa', act: 'free', label: 'Free time', state: 'active' }); t = limit; continue; }
          let end = Math.min(t + rng.int(f[1], f[2]), limit);
          if (limit - end < 4) end = limit;
          if (end - t < 1.5 && prev && prev.place && !prev.away && prev.t1 === t && prev.act !== 'sleep') {
            p.agenda.paint(Object.assign({}, prev, { t0: prev.t0, t1: end })); // too short: stay put
          } else {
            p.agenda.paint({ t0: t, t1: end, place: f[0], act: f[3], label: f[4], state: 'active', filler: true });
          }
          prev = p.agenda.at(end - 0.01); prevPlace = f[0]; t = end;
          recent.push(f[4]); if (recent.length > 2) recent.shift();
        }
      }
    }

    // Dependents' own agenda, from custody.
    for (const inf of infants) {
      const { holderAt, phase } = custody[inf.id];
      let s = 0;
      for (let m = 1; m <= WEEK; m++) {
        if (m < WEEK && holderAt[m] === holderAt[s] && phase[m] === phase[s]) continue;
        const h = holderAt[s], ph = phase[s];
        const asleep = ph === 1 || ph === 2;
        if (h >= 0) {
          const carrier = people[h];
          const label = ph === 3 ? 'Night feed' : asleep ? 'Asleep, carried' : 'With ' + carrier.name;
          inf.agenda.paint({ t0: s, t1: m, with: carrier.id, state: asleep ? 'asleep' : 'active', act: asleep ? 'sleep' : 'care', label });
        } else {
          inf.agenda.paint({ t0: s, t1: m, place: ph === 2 ? inf.napPlace : inf.nightPlace, state: 'asleep', act: 'sleep', label: ph === 2 ? 'Nap' : 'Asleep' });
        }
        s = m;
      }
    }

    // ---------------------------------------------------- 4. path planner
    const bookings = {};
    const routeFailures = [];
    function bookSeat(placeName, t0, t1, p) {
      const seats = P.places[placeName];
      if (!seats || !seats.length) { routeFailures.push({ who: p.id, place: placeName, t: t0, reason: 'unknown place' }); return null; }
      if (seats.length === 1) return seats[0];
      for (let k = 0; k < seats.length; k++) {
        const n = seats[(k + (p.role === 'guest' ? 3 : 0)) % seats.length];
        const b = bookings[n] || (bookings[n] = []);
        if (!b.some(([a, z]) => t0 < z && t1 > a)) { b.push([t0, t1]); return n; }
      }
      return seats[p.idx % seats.length];
    }
    const segments = {};
    for (const p of people) {
      const segs = [];
      if (p.role === 'infant') {
        for (const b of p.agenda.items) {
          if (b.with) segs.push({ k: 'with', t0: b.t0, t1: b.t1, carrier: b.with, state: b.state, act: b.act, label: b.label });
          else segs.push({ k: 'dwell', t0: b.t0, t1: b.t1, node: P.places[b.place][0], state: b.state, act: b.act, label: b.label });
        }
        segments[p.id] = segs;
        continue;
      }
      let cur = null; // {node} or {exit}
      for (const b of p.agenda.items) {
        const len = b.t1 - b.t0;
        if (b.away) {
          if (cur && cur.node) {
            const ex = (P.exits[b.exit || 'front'] || P.exits.front).node;
            const r = P.route(cur.node, ex);
            if (!r) routeFailures.push({ who: p.id, from: cur.node, to: ex, t: b.t0 });
            const tt = r ? Math.min(r.sec / 60, len * 0.9) : 0;
            if (r && tt > 0) segs.push({ k: 'move', t0: b.t0, t1: b.t0 + tt, pts: r.pts, sec: r.sec, state: 'transit', act: b.act, label: 'Heading out' });
            segs.push({ k: 'away', t0: b.t0 + tt, t1: b.t1, label: b.away, act: b.act, hidden: !!b.hidden });
          } else segs.push({ k: 'away', t0: b.t0, t1: b.t1, label: b.away, act: b.act, hidden: !!b.hidden });
          cur = { exit: b.exit || 'front' };
          continue;
        }
        const node = bookSeat(b.place, b.t0, b.t1, p);
        if (!node) { cur = cur || null; continue; }
        const from = cur ? (cur.node || (P.exits[cur.exit] || P.exits.front).node) : node;
        if (from !== node) {
          const r = P.route(from, node);
          if (!r) { routeFailures.push({ who: p.id, from, to: node, t: b.t0 }); segs.push({ k: 'dwell', t0: b.t0, t1: b.t1, node, state: b.state, act: b.act, label: b.label }); }
          else {
            const tt = Math.min(r.sec / 60, len * 0.9);
            segs.push({ k: 'move', t0: b.t0, t1: b.t0 + tt, pts: r.pts, sec: r.sec, state: 'transit', act: b.act, label: b.label });
            segs.push({ k: 'dwell', t0: b.t0 + tt, t1: b.t1, node, state: b.state, act: b.act, label: b.label });
          }
        } else segs.push({ k: 'dwell', t0: b.t0, t1: b.t1, node, state: b.state, act: b.act, label: b.label });
        cur = { node };
      }
      segments[p.id] = segs;
    }

    // ---------------------------------------------------- 5. presence timeline + events
    const tracks = {};
    const nodeZone = id => P.nodes[id].zone;
    for (const p of people) {
      if (p.role === 'infant') continue;
      const tr = [];
      const push = (t, zone, state) => { const l = tr[tr.length - 1]; if (l && l.zone === zone && l.state === state) return; if (l && Math.abs(l.t - t) < 1e-9) tr.pop(); tr.push({ t, zone, state }); };
      for (const s of segments[p.id]) {
        if (s.k === 'away') push(s.t0, -1, 'away');
        else if (s.k === 'dwell') push(s.t0, nodeZone(s.node), s.state);
        else if (s.k === 'move') {
          const scale = (s.t1 - s.t0) / Math.max(1e-9, s.sec / 60);
          for (let i = 0; i < s.pts.length - 1; i++) {
            const a = s.pts[i], b = s.pts[i + 1];
            if (a.l !== b.l) continue;
            const len = Math.hypot(b.x - a.x, b.y - a.y), n = Math.max(1, Math.ceil(len / 0.5));
            for (let k = 0; k < n; k++) {
              const f = k / n;
              const t = s.t0 + (a.s + (b.s - a.s) * f) / 60 * scale;
              push(t, P.zoneAt(a.l, a.x + (b.x - a.x) * f, a.y + (b.y - a.y) * f), 'transit');
            }
          }
        }
      }
      tracks[p.id] = tr;
    }
    const valueAt = (tr, t) => { let lo = 0, hi = tr.length - 1, r = tr[0]; while (lo <= hi) { const mid = (lo + hi) >> 1; if (tr[mid].t <= t) { r = tr[mid]; lo = mid + 1; } else hi = mid - 1; } return r; };
    for (const inf of infants) {
      const tr = [];
      const push = (t, zone, state) => { const l = tr[tr.length - 1]; if (l && l.zone === zone && l.state === state) return; if (l && Math.abs(l.t - t) < 1e-9) tr.pop(); tr.push({ t, zone, state }); };
      const map = (seg, st) => st === 'away' ? 'away' : st === 'transit' ? 'transit' : seg.state;
      for (const s of segments[inf.id]) {
        if (s.k === 'dwell') { push(s.t0, nodeZone(s.node), s.state); continue; }
        const ct = tracks[s.carrier];
        const v = valueAt(ct, s.t0);
        push(s.t0, v.zone, map(s, v.state));
        for (const e of ct) if (e.t > s.t0 && e.t < s.t1) push(e.t, e.zone, map(s, e.state));
      }
      tracks[inf.id] = tr;
    }

    const zoneId = i => (i >= 0 ? P.zones[i].id : null);
    const events = [];
    const weekStart = H.weekStart || '2026-11-02';
    for (const p of people) {
      const tr = tracks[p.id];
      let prev = null;
      const ev = (t, type, zone, state) => events.push({ minute: t, t: isoAt(weekStart, t), occupant: p.id, zone: zoneId(zone), type, state });
      for (const cur of tr) {
        if (!prev) { prev = cur; continue; }
        if (prev.zone !== cur.zone) {
          if (prev.zone === -1) { ev(cur.t, 'arrive', cur.zone, cur.state); ev(cur.t, 'enter', cur.zone, cur.state); }
          else if (cur.zone === -1) { ev(cur.t, 'leave', prev.zone, 'transit'); ev(cur.t, 'depart', prev.zone, 'away'); }
          else { ev(cur.t, 'leave', prev.zone, cur.state); ev(cur.t, 'enter', cur.zone, cur.state); }
        }
        if (cur.zone !== -1 && prev.state === 'asleep' && cur.state !== 'asleep') ev(cur.t, 'wake', cur.zone, cur.state);
        if (cur.zone !== -1 && prev.state !== 'asleep' && cur.state === 'asleep') ev(cur.t, 'sleep', cur.zone, cur.state);
        prev = cur;
      }
    }
    events.sort((a, b) => a.minute - b.minute || a.occupant.localeCompare(b.occupant));

    const presence = {};
    for (const p of people) {
      const zone = new Int16Array(WEEK), state = new Uint8Array(WEEK);
      const tr = tracks[p.id];
      let i = 0;
      for (let m = 0; m < WEEK; m++) {
        const t = m + 0.5;
        while (i + 1 < tr.length && tr[i + 1].t <= t) i++;
        zone[m] = tr[i] ? tr[i].zone : -1;
        state[m] = tr[i] ? STATE_CODE[tr[i].state] : 0;
      }
      presence[p.id] = { zone, state };
    }

    const ms = (typeof performance !== 'undefined' ? performance : Date).now() - started;
    return {
      seed, weekStart, people, byId, plan: P, segments, tracks, presence, events, custody,
      agendas: Object.fromEntries(people.map(p => [p.id, p.agenda.items])),
      routeFailures, warnings, ms, overrides: options && options.overrides,
      meta: { name: H.name, socialWindow, lateWindow }
    };
  }

  // ---------------------------------------------------------------- checks (the brief's "always true")
  function runChecks(week, household, plan) {
    const P = week.plan, out = [];
    const people = week.people;
    const add = (id, label, ok, detail) => out.push({ id, label, ok, detail });

    // 1. One place at a time: every agenda covers the week with no gaps or overlaps.
    let overlap = 0, gap = 0;
    for (const p of people) {
      const items = week.agendas[p.id];
      let t = 0;
      for (const it of items) { if (it.t0 < t - 1e-6) overlap++; if (it.t0 > t + 1e-6) gap++; t = it.t1; }
      if (t < WEEK - 1e-6) gap++;
    }
    add('one-place', 'No one is in two places at once', overlap === 0 && gap === 0,
      overlap + gap === 0 ? `${people.length} people, every minute of the week accounted for` : `${overlap} overlaps, ${gap} gaps`);

    // 2. Infant never alone.
    const responsible = people.filter(p => p.role.startsWith('adult') || p.role === 'caregiver');
    let alone = 0, firstAlone = null;
    for (const inf of people.filter(p => p.role === 'infant')) {
      const { holderAt } = week.custody[inf.id];
      for (let m = 0; m < WEEK; m++) {
        const h = holderAt[m];
        let ok;
        if (h >= 0) ok = week.presence[people[h].id].state[m] !== 2;
        else ok = responsible.some(q => week.presence[q.id].zone[m] !== -1);
        if (!ok) { alone++; if (firstAlone === null) firstAlone = m; }
      }
    }
    add('infant', 'The infant is never alone', alone === 0,
      alone === 0 ? 'Always held by an awake adult, or asleep with an adult at home' : `${alone} minutes alone, first at ${dayClock(firstAlone)}`);

    // 3. Nanny never present on weekends.
    let weekendNanny = 0;
    for (const n of people.filter(p => p.role === 'caregiver')) for (let m = 5 * DAY; m < WEEK; m++) if (week.presence[n.id].zone[m] !== -1) weekendNanny++;
    add('nanny', 'The nanny is never here at the weekend', weekendNanny === 0, weekendNanny === 0 ? 'Away all of Saturday and Sunday' : `${weekendNanny} minutes on site at the weekend`);

    // 4. Kid never home without an adult.
    let kidAlone = 0;
    for (const c of people.filter(p => p.role === 'child')) for (let m = 0; m < WEEK; m++) {
      if (week.presence[c.id].zone[m] === -1) continue;
      if (!responsible.some(q => week.presence[q.id].zone[m] !== -1)) kidAlone++;
    }
    add('kid', 'The kid is never home without an adult', kidAlone === 0, kidAlone === 0 ? 'An adult is home whenever the kid is' : `${kidAlone} minutes`);

    // 5. Independent sides of the primary bedroom.
    const zA = P.zoneIndex['primary-a'], zB = P.zoneIndex['primary-b'];
    let episodes = 0;
    if (zA !== undefined && zB !== undefined) {
      let inEp = false;
      for (let m = 0; m < WEEK; m++) {
        let aSleep = false, bSleep = false, aAwake = false, bAwake = false;
        for (const p of people) {
          const z = week.presence[p.id].zone[m], s = week.presence[p.id].state[m];
          if (p.role === 'infant') continue;
          if (z === zA) { if (s === 2) aSleep = true; else aAwake = true; }
          if (z === zB) { if (s === 2) bSleep = true; else bAwake = true; }
        }
        const split = (aSleep && bAwake && !aAwake) || (bSleep && aAwake && !bAwake);
        if (split && !inEp) episodes++;
        inEp = split;
      }
    }
    add('zones', 'Both sides of the primary bed sleep and wake on their own', episodes > 0, `${episodes} times one side was up while the other slept`);

    // 6. Every trip reachable; 7. no edge passes through a wall.
    add('paths', 'Every trip has a route through the doorways', week.routeFailures.length === 0,
      week.routeFailures.length === 0 ? `${countTrips(week)} trips routed` : `${week.routeFailures.length} trips without a route`);
    const walls = P.wallCrossings();
    add('walls', 'No path walks through a wall', walls.length === 0 && P.badEdges.length === 0,
      walls.length === 0 ? `${plan.edges.length} hallway links checked against ${plan.doorways.length} doorways` : walls.slice(0, 3).map(w => `${w.edge.join(' → ')} crosses ${w.from}/${w.to}`).join('; '));

    // 8. Same seed, same week.
    const again = generate(household, plan, { seed: week.seed, overrides: week.overrides });
    const same = fingerprint(again.events) === fingerprint(week.events);
    add('seed', 'Same seed, same week', same, same ? `Seed “${week.seed}” replayed: ${week.events.length.toLocaleString()} events match` : 'Replay differed');

    // 9. Speed.
    add('speed', 'Generated in under a second', week.ms < 1000, `${Math.round(week.ms)} ms for ${people.length} people`);
    return out;
  }
  function countTrips(week) { let n = 0; for (const id in week.segments) for (const s of week.segments[id]) if (s.k === 'move') n++; return n; }
  function fingerprint(events) { let h = 2166136261 >>> 0; for (const e of events) { const s = e.t + e.occupant + e.zone + e.type + e.state; for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); } } return h >>> 0; }
  function dayClock(m) { return DAY_NAMES[Math.floor(m / DAY)].slice(0, 3) + ' ' + clock(m); }

  // ---------------------------------------------------------------- export
  function exportEvents(week, household, plan) {
    return {
      household: household.name, plan: plan.name, seed: week.seed, weekStart: week.weekStart,
      resolution: 'events are exact to the second; presence is sampled per minute',
      zones: week.plan.zones.map(z => ({ id: z.id, name: z.name, room: z.room, level: z.level, lighting: z.lighting })),
      occupants: week.people.map(p => ({ id: p.id, name: p.name, role: p.role, presence: p.presence })),
      events: week.events.map(({ t, occupant, zone, type, state }) => ({ t, occupant, zone, type, state }))
    };
  }

  const api = { generate, runChecks, exportEvents, buildPlan, makeRng, clock, dayClock, isoAt, DAY, WEEK, DAY_KEYS, DAY_NAMES, STATE_CODE };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.RhythmEngine = api;
})(typeof self !== 'undefined' ? self : this);
