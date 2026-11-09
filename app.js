/* Rhythm Simulator views: floor plan playback, calendar, scrubber, controls. Nothing here computes behaviour;
   everything is read from the week the engine generated. */
(async function () {
  'use strict';
  const E = window.RhythmEngine;
  const { DAY, WEEK, DAY_NAMES } = E;
  const NS = 'http://www.w3.org/2000/svg';
  const $ = id => document.getElementById(id);
  const svg = (tag, attrs, parent) => {
    const n = document.createElementNS(NS, tag);
    for (const k in attrs || {}) n.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(n);
    return n;
  };
  const css = name => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const ACTS = ['sleep', 'ready', 'meal', 'away', 'activity', 'social', 'free', 'care'];
  const SPEEDS = [[1, '1 min/s'], [10, '10 min/s'], [60, '1 h/s'], [144, '1 day/10 s']];
  const MILESTONES = new Set(['wake', 'sleep', 'depart', 'arrive']);
  const TRAIL_MINUTES = 4;

  // ------------------------------------------------------------ load
  let H, PLAN;
  try {
    [H, PLAN] = await Promise.all([fetch('household.json').then(r => r.json()), fetch('plan.json').then(r => r.json())]);
  } catch (err) {
    $('subtitle').textContent = 'Could not load household.json and plan.json. Serve this folder over http (for example: python3 -m http.server).';
    return;
  }

  const store = {
    get(k, d) { try { const v = localStorage.getItem('rhythm.' + k); return v === null ? d : JSON.parse(v); } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem('rhythm.' + k, JSON.stringify(v)); } catch (e) { /* storage unavailable */ } }
  };

  const ui = {
    t: 6 * 60 + 25, playing: false, speed: store.get('speed', 10),
    trails: store.get('trails', true), heat: store.get('rooms', 'occupancy') === 'heatmap' ? 'week' : 'off', drawing: false, cal: store.get('cal', 'grid'), rooms: store.get('rooms', 'occupancy'), acuity: null,
    seed: H.seed, history: [], overrides: {}, focus: null, occupant: store.get('occupant', 'home')
  };
  let week, checks, layout, P, LIGHT;
  const segIdx = {};

  // ------------------------------------------------------------ generate
  function regenerate(seed) {
    ui.seed = seed;
    week = E.generate(H, PLAN, { seed, overrides: ui.overrides });
    P = week.plan;
    LIGHT = window.RhythmLighting.build(PLAN, P, H);
    if (ui.acuity === null) ui.acuity = LIGHT.defaultAcuity;
    if (ui.floor === undefined) ui.floor = store.get('floor', LIGHT.defaultFloor);
    renderLogic();
    checks = E.runChecks(week, H, PLAN);
    for (const k in segIdx) delete segIdx[k];
    if (!ui.history.includes(seed)) { ui.history.unshift(seed); ui.history = ui.history.slice(0, 6); }
    $('seed').value = seed;
    $('subtitle').textContent = `${PLAN.name.split(',')[0]} · ${week.people.filter(p => p.presence === 'resident').length} residents, nanny, ${week.people.filter(p => p.role === 'guest').length} Thursday guests`;
    $('footnote').textContent = `Seed “${seed}” · ${week.events.length.toLocaleString()} events · generated in ${Math.round(week.ms)} ms`;
    $('maxPeople').textContent = week.people.length;
    buildPeopleLayer();
    renderHistory();
    renderChecks();
    syncOccupant();
    skyDrawn = null;
    buildCalendarRows();
    drawCalendar();
    drawScrubber();
    if (ui.heat !== 'off') drawHeat();
    frame(true);
  }

  // ------------------------------------------------------------ positions
  function segAt(id, t) {
    const segs = week.segments[id];
    let i = segIdx[id] || 0;
    if (!segs[i] || t < segs[i].t0 || t >= segs[i].t1) {
      let lo = 0, hi = segs.length - 1; i = 0;
      while (lo <= hi) { const m = (lo + hi) >> 1; if (segs[m].t1 <= t) lo = m + 1; else if (segs[m].t0 > t) hi = m - 1; else { i = m; break; } }
      if (t >= WEEK) i = segs.length - 1;
      segIdx[id] = i;
    }
    return segs[i];
  }
  function posOf(id, t) {
    const s = segAt(id, Math.min(t, WEEK - 1e-6));
    if (!s) return null;
    if (s.k === 'dwell') { const n = P.nodes[s.node]; return { l: n.level, x: n.x, y: n.y, state: s.state, seg: s }; }
    if (s.k === 'away') return { away: true, label: s.label, hidden: s.hidden, seg: s };
    if (s.k === 'move') {
      const sec = Math.max(0, Math.min(1, (t - s.t0) / (s.t1 - s.t0))) * s.sec;
      const pts = s.pts;
      for (let i = 0; i < pts.length - 1; i++) {
        const a = pts[i], b = pts[i + 1];
        if (sec <= b.s || i === pts.length - 2) {
          if (a.l !== b.l || b.s === a.s) return { l: b.l, x: b.x, y: b.y, state: 'transit', seg: s };
          const f = Math.max(0, Math.min(1, (sec - a.s) / (b.s - a.s)));
          return { l: a.l, x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f, state: 'transit', seg: s };
        }
      }
    }
    if (s.k === 'with') {
      const c = posOf(s.carrier, t);
      if (!c) return null;
      if (c.away) return { away: true, label: c.label, with: s.carrier, seg: s };
      return { l: c.l, x: c.x + 0.8, y: c.y + 0.6, state: s.state === 'asleep' ? 'asleep' : c.state, carried: true, seg: s };
    }
    return null;
  }

  // ------------------------------------------------------------ plan drawing
  const planSvg = $('plan');
  let gZones = {}, gHeatLv = {}, lightEls = {}, gPeople, gTrails, gUnder = [], peopleEls = {};
  function chooseLayout() {
    const w = planSvg.parentElement.clientWidth;
    return w < 640 ? { stacked: true, off: { 1: [0, 0], 2: [0, 45] }, vb: [-3, -6, 62, 90] }
                   : { stacked: false, off: { 1: [0, 0], 2: [60, 0] }, vb: [-3, -6.5, 119, 45.5] };
  }
  const centroid = poly => {
    let a = 0, cx = 0, cy = 0;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const f = poly[j][0] * poly[i][1] - poly[i][0] * poly[j][1];
      a += f; cx += (poly[j][0] + poly[i][0]) * f; cy += (poly[j][1] + poly[i][1]) * f;
    }
    return [cx / (3 * a), cy / (3 * a)];
  };
  const poly = pts => pts.map(p => p.join(',')).join(' ');

  function buildPlan() {
    layout = chooseLayout();
    planSvg.innerHTML = '';
    planSvg.setAttribute('viewBox', layout.vb.join(' '));
    const defs = svg('defs', {}, planSvg);
    const hatch = svg('pattern', { id: 'stairHatch', width: 0.6, height: 0.6, patternUnits: 'userSpaceOnUse', patternTransform: 'rotate(0)' }, defs);
    svg('line', { x1: 0, y1: 0, x2: 0.6, y2: 0, stroke: 'currentColor', 'stroke-width': 0.08 }, hatch);
    gZones = {}; gHeatLv = {}; lightEls = {}; gUnder = [];
    for (const lv of PLAN.levels) {
      const [ox, oy] = layout.off[lv.id];
      const g = svg('g', { transform: `translate(${ox} ${oy})` }, planSvg);
      g.style.color = 'var(--hair)';
      // Architect's drawing underlay, aligned by its pixel origin and scale.
      const u = lv.underlay;
      const clip = svg('clipPath', { id: 'clip' + lv.id }, defs);
      svg('rect', { x: -1, y: -1, width: 55, height: lv.id === 1 ? 38 : 26 }, clip);
      const img = svg('image', {
        href: u.src, x: -u.originPx[0] / u.pxPerUnit[0], y: -u.originPx[1] / u.pxPerUnit[1],
        width: u.sizePx[0] / u.pxPerUnit[0], height: u.sizePx[1] / u.pxPerUnit[1], preserveAspectRatio: 'none',
        'clip-path': `url(#clip${lv.id})`, opacity: 0.55
      }, g);
      img.style.display = ui.drawing ? '' : 'none';
      gUnder.push(img);

      svg('text', { x: 0, y: -4, class: 'sheetlabel' }, g).textContent = lv.name;
      svg('text', { x: 0, y: -2.7, class: 'sheetsub' }, g).textContent = `Sheet ${lv.sheet} · 53′ × 24′`;

      const rooms = PLAN.rooms.filter(r => r.level === lv.id);
      const fills = svg('g', { class: 'fills' }, g);
      for (const r of rooms) if (r.type !== 'exterior') svg('polygon', { points: poly(r.polygon), class: 'roomfill' }, fills);
      // Zone tints (one per zone, so both sides of the primary bed light separately).
      for (const z of P.zones.filter(z => z.level === lv.id)) {
        gZones[z.index] = svg('polygon', { points: poly(z.polygon), class: 'zone', fill: 'var(--lamp)', 'fill-opacity': 0 }, g);
      }
      // Lighting: one circle per zone, clipped to the zone; radius = intensity, fill = colour temperature.
      const gLight = svg('g', { class: 'lights' }, g);
      for (const z of P.zones.filter(z => z.level === lv.id)) {
        const lz = LIGHT.zones[z.index];
        const clip = svg('clipPath', { id: 'zclip' + z.index }, defs);
        svg('polygon', { points: poly(z.polygon) }, clip);
        const zg = svg('g', { 'clip-path': `url(#zclip${z.index})` }, gLight);
        const circle = svg('circle', { cx: lz.cx, cy: lz.cy, r: 0, class: 'light', 'fill-opacity': 0.55 }, zg);
        const text = svg('text', { x: lz.cx, y: lz.cy + 0.22, class: 'lightval' }, gLight);
        lightEls[z.index] = { circle, text, R: lz.radius };
      }
      // Heatmap glow sits under the walls and furniture, clipped to the rooms.
      const hclip = svg('clipPath', { id: 'heatClip' + lv.id }, defs);
      for (const r of rooms) svg('polygon', { points: poly(r.polygon) }, hclip);
      gHeatLv[lv.id] = svg('g', { class: 'heat', 'clip-path': `url(#heatClip${lv.id})` }, g);
      for (const v of PLAN.voids || []) if (v.level === lv.id) {
        svg('polygon', { points: poly(v.polygon), class: 'void' }, g);
        const [a, b] = [v.polygon[0], v.polygon[2]];
        svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'void' }, g);
        svg('line', { x1: b[0], y1: a[1], x2: a[0], y2: b[1], class: 'void' }, g);
      }
      for (const f of PLAN.furniture || []) if (f.level === lv.id) {
        if (f.kind === 'rect') svg('rect', { x: f.x, y: f.y, width: f.w, height: f.h, class: 'furn', rx: f.label === 'bed' ? 0.3 : 0.1 }, g);
        else if (f.kind === 'circle') svg('circle', { cx: f.cx, cy: f.cy, r: f.r, class: 'furn' }, g);
        else if (f.kind === 'path') svg('path', { d: f.d, class: 'furn' }, g);
        if (f.label === 'stair') for (let y = f.y + 0.9; y < f.y + f.h; y += 0.9) svg('line', { x1: f.x, y1: y, x2: f.x + f.w, y2: y, class: 'furn' }, g);
      }
      const st1 = rooms.find(r => r.id === 'stair1');
      if (st1) { const [x0, y0] = st1.polygon[0], [x1, y1] = st1.polygon[2]; for (let y = y0 + 0.9; y < y1; y += 0.9) svg('line', { x1: x0, y1: y, x2: x1, y2: y, class: 'furn' }, g); }

      // Walls: room outlines with door gaps cut out by a mask (so nothing paints over the heatmap), plus jambs.
      const wallMask = svg('mask', { id: 'walls' + lv.id, maskUnits: 'userSpaceOnUse', x: -3, y: -3, width: 62, height: 42 }, defs);
      svg('rect', { x: -3, y: -3, width: 62, height: 42, fill: '#fff' }, wallMask);
      const walls = svg('g', { mask: `url(#walls${lv.id})` }, g);
      for (const r of rooms) svg('polygon', { points: poly(r.polygon), class: r.type === 'exterior' ? 'pergola' : 'wall' }, walls);
      svg('rect', { x: 0, y: 0, width: 53, height: 24, class: 'outline' }, walls);
      for (const d of PLAN.doorways.filter(d => d.level === lv.id)) {
        const [x, y] = d.at, h = d.width / 2;
        const isOpen = d.kind === 'opening' || d.kind === 'stair';
        const [x1, y1, x2, y2] = d.axis === 'h' ? [x - h, y, x + h, y] : [x, y - h, x, y + h];
        svg('line', { x1, y1, x2, y2, stroke: '#000', 'stroke-width': 0.9 }, wallMask);
        if (d.closable) svg('line', { x1, y1, x2, y2, class: 'doordash' }, g);
        if (!isOpen) {
          const j = 0.45;
          if (d.axis === 'h') { svg('line', { x1: x1, y1: y - j, x2: x1, y2: y + j, class: 'jamb' }, g); svg('line', { x1: x2, y1: y - j, x2: x2, y2: y + j, class: 'jamb' }, g); }
          else { svg('line', { x1: x - j, y1: y1, x2: x + j, y2: y1, class: 'jamb' }, g); svg('line', { x1: x - j, y1: y2, x2: x + j, y2: y2, class: 'jamb' }, g); }
        }
      }
      // Labels.
      for (const r of rooms) {
        const [cx, cy] = r.labelAt || centroid(r.polygon), turn = r.labelRotate ? { transform: `rotate(${r.labelRotate} ${cx} ${cy})` } : {};
        svg('text', Object.assign({ x: cx, y: cy, class: 'rlabel' }, turn), g).textContent = r.name;
        if (r.number) svg('text', Object.assign({ x: cx, y: cy + 0.85, class: 'rnum' }, turn), g).textContent = r.number;
      }
      if (lv.id === 2) {
        svg('text', { x: 43.4, y: 16.6, class: 'rnum' }, g).textContent = 'side A';
        svg('text', { x: 43.4, y: 19.6, class: 'rnum' }, g).textContent = 'side B';
      }
      if (lv.id === 1) {
        svg('text', { x: 31.8, y: -1.0, class: 'exitlabel', 'text-anchor': 'middle' }, g).textContent = 'Front door';
        svg('text', { x: 53.9, y: 11.2, class: 'exitlabel' }, g).textContent = 'Side';
      }
      if (lv.id === 2 && !layout.stacked) {
        // Scale bar in the empty space under the second floor.
        const y = 29;
        svg('line', { x1: 0, y1: y, x2: 10, y2: y, class: 'dim' }, g);
        for (const x of [0, 5, 10]) { svg('line', { x1: x, y1: y - 0.4, x2: x, y2: y + 0.4, class: 'dim' }, g); svg('text', { x, y: y + 1.5, class: 'dimtext' }, g).textContent = x + (x === 10 ? ' ft' : ''); }
        svg('text', { x: 14, y: y + 0.3, class: 'sheetsub' }, g).textContent = 'Walking 1 m/s · stair 14 s';
      }
    }
    gTrails = svg('g', { class: 'trails' }, planSvg);
    gPeople = svg('g', { class: 'people' }, planSvg);
    if (week) { buildPeopleLayer(); if (ui.heat !== 'off') drawHeat(); }
  }

  function buildPeopleLayer() {
    if (!gPeople) return;
    gPeople.innerHTML = ''; gTrails.innerHTML = ''; peopleEls = {};
    // Infant drawn last so it sits on top of the carrier.
    const order = week.people.slice().sort((a, b) => (a.role === 'infant') - (b.role === 'infant'));
    for (const p of order) {
      const r = p.role === 'infant' ? 0.68 : 1.08;
      const g = svg('g', { class: 'person', 'data-id': p.id }, gPeople);
      const title = svg('title', {}, g);
      const body = svg('g', { class: 'body' }, g);
      svg('circle', { r, fill: p.color, class: 'ring' }, body);
      const tx = svg('text', { 'font-size': p.role === 'infant' ? 0.8 : 1.15 }, body);
      tx.style.fill = onColor(p.color);
      tx.textContent = p.initial;
      const moon = svg('path', { d: 'M0.55,-1.55 a0.62,0.62 0 1,0 0.7,0.85 a0.5,0.5 0 1,1 -0.7,-0.85z', class: 'moon' }, g);
      const trail = [0, 1, 2, 3].map(k => svg('polyline', { class: 'trail', stroke: markColor(p.color), 'stroke-width': p.role === 'infant' ? 0.25 : 0.42, 'stroke-opacity': [0.55, 0.36, 0.2, 0.1][k] }, gTrails));
      peopleEls[p.id] = { g, title, moon, trail, p };
    }
  }

  // Colour helpers for the sky-derived people palette.
  const rgbOf = c => { const h = c.trim(); if (h[0] === '#') return [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16)); return h.match(/\d+/g).slice(0, 3).map(Number); };
  const lumOf = rgb => { const [r, g, b] = rgb.map(v => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }); return 0.2126 * r + 0.7152 * g + 0.0722 * b; };
  const contrastOf = (a, b) => { const [x, y] = [lumOf(a), lumOf(b)].sort((u, v) => v - u); return (x + 0.05) / (y + 0.05); };
  // Initials: white or ink, whichever reads better on the dot.
  const onColor = c => contrastOf(rgbOf(c), [255, 255, 255]) >= contrastOf(rgbOf(c), rgbOf('#16213D')) ? '#FFFFFF' : '#16213D';
  // Thin marks (trails, calendar lanes): a colour too close to the sheet is pulled toward the ink so it stays visible.
  function markColor(c) {
    const rgb = rgbOf(c), sheet = rgbOf(getComputedStyle(document.documentElement).getPropertyValue('--sheet'));
    if (contrastOf(rgb, sheet) >= 2) return c;
    const ink = rgbOf(getComputedStyle(document.documentElement).getPropertyValue('--ink'));
    return `rgb(${rgb.map((v, i) => Math.round(v + (ink[i] - v) * 0.45)).join(',')})`;
  }

  function toScreen(pos) { const [ox, oy] = layout.off[pos.l]; return [pos.x + ox, pos.y + oy]; }

  function drawPeople(t) {
    for (const id in peopleEls) {
      const el = peopleEls[id];
      const pos = posOf(id, t);
      if (!pos || pos.away) { el.g.style.display = 'none'; el.trail.forEach(l => l.setAttribute('points', '')); continue; }
      el.g.style.display = '';
      const [x, y] = toScreen(pos);
      el.g.setAttribute('transform', `translate(${x.toFixed(2)} ${y.toFixed(2)})`);
      el.g.classList.toggle('asleep', pos.state === 'asleep');
      el.g.classList.toggle('focus', ui.focus === id);
      el.moon.style.display = pos.state === 'asleep' ? '' : 'none';
      el.title.textContent = `${el.p.name}: ${labelFor(id, pos)}`;
      // Trail: the last few minutes, split into four fading pieces; breaks across levels.
      if (ui.trails && el.p.role !== 'infant') {
        const N = 32, dt = TRAIL_MINUTES / N;
        const chunks = [[], [], [], []];
        let prevL = pos.l;
        for (let k = 0; k <= N; k++) {
          const q = posOf(id, Math.max(0, t - k * dt));
          const c = Math.min(3, Math.floor(k / (N / 4)));
          if (!q || q.away || q.l !== prevL) break;
          const [qx, qy] = toScreen(q);
          chunks[c].push(qx.toFixed(2) + ',' + qy.toFixed(2));
          if (c > 0 && chunks[c].length === 1 && chunks[c - 1].length) chunks[c - 1].push(qx.toFixed(2) + ',' + qy.toFixed(2));
        }
        el.trail.forEach((l, i) => l.setAttribute('points', chunks[i].length > 1 ? chunks[i].join(' ') : ''));
      } else el.trail.forEach(l => l.setAttribute('points', ''));
    }
  }

  function labelFor(id, pos) {
    const s = pos.seg;
    if (!s) return '';
    if (s.k === 'move') return 'Walking · ' + s.label;
    return s.label || '';
  }

  // Room tint by how many people are in each zone right now (awake: warm, asleep only: cool).
  function drawZones(t) {
    const m = Math.min(WEEK - 1, Math.floor(t));
    const awake = {}, asleep = {};
    for (const p of week.people) {
      const pr = week.presence[p.id];
      const z = pr.zone[m];
      if (z < 0) continue;
      if (pr.state[m] === 2) asleep[z] = (asleep[z] || 0) + 1; else awake[z] = (awake[z] || 0) + 1;
    }
    const lighting = ui.rooms === 'lighting' && ui.heat === 'off';
    drawLights(lighting ? t : null);
    for (const z in gZones) {
      const el = gZones[z];
      if (ui.heat !== 'off' || lighting) { el.setAttribute('fill-opacity', 0); continue; }
      const a = awake[z] || 0, s = asleep[z] || 0;
      if (a) { el.setAttribute('fill', 'var(--lamp)'); el.setAttribute('fill-opacity', Math.min(0.42, 0.14 + 0.08 * (a - 1))); }
      else if (s) { el.setAttribute('fill', 'var(--moon)'); el.setAttribute('fill-opacity', 0.16); }
      else el.setAttribute('fill-opacity', 0);
    }
  }

  let lightNow = null;
  function drawLights(t) {
    lightNow = t === null ? null : LIGHT.at(week, t, ui.acuity, ui.floor);
    for (const z in lightEls) {
      const el = lightEls[z], o = lightNow && lightNow[z];
      if (!o || o.intensity < 0.005) { el.circle.setAttribute('r', 0); el.text.textContent = ''; continue; }
      el.circle.setAttribute('r', (o.intensity * el.R).toFixed(2));
      el.circle.setAttribute('fill', `rgb(${o.rgb.join(',')})`);
      el.text.textContent = Math.round(o.intensity * 100) + '%';
    }
  }
  // Zone names repeat across floors (both halves of the stair): add the floor when they do.
  const zname = z => LIGHT.zones.filter(o => o.name === z.name).length > 1 ? `${z.name} (${z.level === 1 ? 'first' : 'second'} floor)` : z.name;
  function renderLights() {
    const panel = $('lightsPanel');
    panel.hidden = !lightNow;
    if (!lightNow) return;
    const lit = lightNow.filter(o => o.intensity >= 0.005).sort((a, b) => b.intensity - a.intensity);
    const html = lit.length ? lit.map(o => `<li><span class="bulb" style="background:rgb(${o.rgb.join(',')})"></span><span><span class="z">${esc(zname(o.zone))}</span>${o.zone.private ? '<span class="pv">Private</span>' : ''}<span class="why">${o.rule} · ${esc(o.reason)}</span></span><span class="val">${Math.round(o.intensity * 100)}%<br>${Math.round(o.kelvin / 50) * 50} K</span></li>`).join('')
      : '<li><span></span><span class="why">Every zone is dark.</span><span></span></li>';
    const el = $('lights');
    if (el._html !== html) { el.innerHTML = html; el._html = html; }
  }
  function renderLogic() {
    const byLevel = [1, 2].map(l => LIGHT.pairs.filter(pr => LIGHT.zones[pr.a].level === l));
    $('losPairs').innerHTML = byLevel.map((prs, i) => `<li class="eyebrow" style="margin-top:6px">${i ? 'Second floor and stairwell' : 'First floor'}</li>` +
      prs.map(pr => `<li>${esc(zname(LIGHT.zones[pr.a]))} ↔ ${esc(zname(LIGHT.zones[pr.b]))} <span class="via">· ${pr.via}</span></li>`).join('')).join('');
    const who = id => (H.occupants.find(o => o.id === id) || { name: id }).name;
    $('rankList').innerHTML = LIGHT.zones.filter(z => LIGHT.ranking[z.id]).map(z =>
      `<li><b>${esc(zname(z))}</b><span>${LIGHT.ranking[z.id].map(t => esc(t.map(who).join(' = '))).join(' → ')} → everyone else</span></li>`).join('');
    $('zoneChips').innerHTML = LIGHT.zones.filter(z => !['mech'].includes(z.id)).map(z => `<span class="${z.private ? 'private' : ''}">${esc(zname(z))}</span>`).join('');
  }

  // Heatmap: a glowing density field of where people spent awake time (and walked), over the day or the week.
  // Time is deposited at real positions on a fine grid, blurred into soft blobs, then mapped light blue -> dark blue.
  const HEAT = { res: 4, x0: -1, y0: -1, w: 56, h: 38 };
  const HEAT_STOPS = [[0, [214, 236, 255]], [0.3, [132, 189, 240]], [0.6, [52, 112, 210]], [0.85, [20, 60, 150]], [1, [8, 30, 92]]];
  function heatColor(v) {
    for (let i = 1; i < HEAT_STOPS.length; i++) {
      const [b, cb] = HEAT_STOPS[i];
      if (v <= b) { const [a, ca] = HEAT_STOPS[i - 1]; const f = (v - a) / (b - a); return ca.map((c, k) => Math.round(c + (cb[k] - c) * f)); }
    }
    return HEAT_STOPS[HEAT_STOPS.length - 1][1];
  }
  function blur(src, W, Hh, sigma) {
    const r = Math.ceil(sigma * 3), k = [];
    let sum = 0;
    for (let i = -r; i <= r; i++) { const v = Math.exp(-(i * i) / (2 * sigma * sigma)); k.push(v); sum += v; }
    for (let i = 0; i < k.length; i++) k[i] /= sum;
    const tmp = new Float32Array(W * Hh), out = new Float32Array(W * Hh);
    for (let y = 0; y < Hh; y++) for (let x = 0; x < W; x++) {
      let a = 0; for (let i = -r; i <= r; i++) { const xx = x + i; if (xx >= 0 && xx < W) a += src[y * W + xx] * k[i + r]; } tmp[y * W + x] = a;
    }
    for (let y = 0; y < Hh; y++) for (let x = 0; x < W; x++) {
      let a = 0; for (let i = -r; i <= r; i++) { const yy = y + i; if (yy >= 0 && yy < Hh) a += tmp[yy * W + x] * k[i + r]; } out[y * W + x] = a;
    }
    return out;
  }
  function heatLegend(range) {
    const el = $('heatLegend');
    el.hidden = ui.heat === 'off';
    $('heatRange').textContent = range;
  }
  function darkSheet() {
    const m = css('--sheet').match(/[0-9a-f]{2}/gi);
    return m ? m.slice(0, 3).reduce((a, h) => a + parseInt(h, 16), 0) / 3 < 100 : false;
  }
  function drawHeat() {
    for (const id in gHeatLv) gHeatLv[id].innerHTML = '';
    if (ui.heat === 'off') { heatLegend(''); return; }
    const [from, to] = [0, WEEK];
    const W = HEAT.w * HEAT.res, Hh = HEAT.h * HEAT.res;
    const grids = {};
    for (const lv of PLAN.levels) grids[lv.id] = new Float32Array(W * Hh);
    const deposit = (l, x, y, wgt) => {
      const g = grids[l]; if (!g) return;
      const gx = Math.round((x - HEAT.x0) * HEAT.res), gy = Math.round((y - HEAT.y0) * HEAT.res);
      if (gx >= 0 && gx < W && gy >= 0 && gy < Hh) g[gy * W + gx] += wgt;
    };
    for (const p of week.people) {
      for (const s of week.segments[p.id]) {
        const a = Math.max(s.t0, from), b = Math.min(s.t1, to);
        if (b <= a || s.state === 'asleep') continue;
        if (s.k === 'dwell') { const n = P.nodes[s.node]; deposit(n.level, n.x, n.y, b - a); }
        else if (s.k === 'with') {
          // A carried infant adds to wherever the carrier was, sampled each minute.
          for (let m = a; m < b; m += 1) { const q = posOf(s.carrier, m); if (q && !q.away) deposit(q.l, q.x, q.y, Math.min(1, b - m)); }
        } else if (s.k === 'move') {
          // Walking leaves a faint trace along the route, so corridors glow a little.
          const pts = s.pts;
          for (let i = 0; i < pts.length - 1; i++) {
            const u = pts[i], v = pts[i + 1];
            if (u.l !== v.l) continue;
            const len = Math.hypot(v.x - u.x, v.y - u.y), n = Math.max(1, Math.ceil(len / 0.5));
            for (let k = 0; k < n; k++) deposit(u.l, u.x + (v.x - u.x) * k / n, u.y + (v.y - u.y) * k / n, 0.6);
          }
        }
      }
    }
    // Two blurs: a tight core and a wide halo, so busy spots read as glowing blobs.
    const fields = {};
    let max = 0;
    for (const l in grids) {
      const core = blur(grids[l], W, Hh, 1.5 * HEAT.res), halo = blur(grids[l], W, Hh, 4 * HEAT.res);
      const f = new Float32Array(W * Hh);
      for (let i = 0; i < f.length; i++) { f[i] = core[i] + 0.5 * halo[i]; if (f[i] > max) max = f[i]; }
      fields[l] = f;
    }
    for (const lv of PLAN.levels) {
      const f = fields[lv.id];
      const cv = document.createElement('canvas'); cv.width = W; cv.height = Hh;
      const ctx = cv.getContext('2d'), img = ctx.createImageData(W, Hh);
      for (let i = 0; i < f.length; i++) {
        const v = Math.pow(f[i] / (max || 1), 0.45);
        if (v < 0.04) continue;
        const [r, g, b] = heatColor(v);
        img.data[i * 4] = r; img.data[i * 4 + 1] = g; img.data[i * 4 + 2] = b;
        img.data[i * 4 + 3] = Math.round(255 * Math.min(0.92, Math.pow((v - 0.04) / 0.96, 0.7) * 1.05));
      }
      ctx.putImageData(img, 0, 0);
      // On a dark sheet, dark blue would read as empty: give the rooms a pale floor so darker still means more.
      if (darkSheet()) svg('rect', { x: HEAT.x0, y: HEAT.y0, width: HEAT.w, height: HEAT.h, fill: 'rgb(226, 236, 246)', opacity: 0.9 }, gHeatLv[lv.id]);
      svg('image', { href: cv.toDataURL(), x: HEAT.x0, y: HEAT.y0, width: HEAT.w, height: HEAT.h, preserveAspectRatio: 'none' }, gHeatLv[lv.id]);
    }
    heatLegend('Whole week');
  }

  // ------------------------------------------------------------ side panels
  function zoneName(z) { return z >= 0 ? P.zones[z].name : ''; }
  function renderSide(t) {
    const m = Math.min(WEEK - 1, Math.floor(t));
    const who = $('who');
    const rows = [];
    const awayGroups = {};
    for (const p of week.people) {
      const pos = posOf(p.id, t);
      if (!pos) continue;
      if (pos.away) {
        if (pos.hidden) continue;
        const label = pos.label || 'Away';
        (awayGroups[label] = awayGroups[label] || []).push(p);
      }
      if (pos.away && pos.hidden) continue;
      const pr = week.presence[p.id];
      const where = pos.away ? pos.label : zoneName(pr.zone[m]) || zoneName(P.zoneAt(pos.l, pos.x, pos.y));
      const what = pos.away ? (pos.with ? 'With ' + week.byId[pos.with].name : 'Away') : labelFor(p.id, pos);
      const cls = pos.away ? 'away' : pos.state === 'asleep' ? 'asleep' : '';
      rows.push(`<li data-id="${p.id}" class="${cls}"><span class="dot" style="background:${p.color}"></span><span style="min-width:0"><span class="name">${p.name}</span><div class="what">${esc(what)}</div></span><span class="where">${pos.state === 'asleep' ? '☾ ' : ''}${esc(where)}</span></li>`);
    }
    const html = rows.join('');
    if (who._html !== html) { who.innerHTML = html; who._html = html; }
    const groups = Object.entries(awayGroups);
    const trayHtml = groups.length
      ? groups.map(([label, ps]) => `<div class="place">${ps.map(p => `<span class="chip" style="background:${p.color};color:${onColor(p.color)}" title="${p.name}">${p.initial}</span>`).join('')}<b>${esc(label)}</b></div>`).join('')
      : '<p class="empty">Everyone is home.</p>';
    const tray = $('tray');
    if (tray._html !== trayHtml) { tray.innerHTML = trayHtml; tray._html = trayHtml; }
  }
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

  function renderChecks() {
    const failed = checks.filter(c => !c.ok).length, sum = $('checksSum');
    sum.textContent = failed ? `${failed} of ${checks.length} failing` : `All ${checks.length} pass`;
    sum.className = 'checksum ' + (failed ? 'bad' : 'ok');
    if (failed) $('checksWrap').open = true;
    $('checks').innerHTML = checks.map(c => `<li class="${c.ok ? 'ok' : 'bad'}"><span class="mark" aria-label="${c.ok ? 'passes' : 'fails'}">${c.ok ? '✓' : '✕'}</span><span>${esc(c.label)}<small>${esc(c.detail)}</small></span></li>`).join('');
  }
  function renderHistory() {
    $('history').innerHTML = ui.history.map(s => `<button type="button" data-seed="${esc(s)}" aria-current="${s === ui.seed}">${esc(s)}</button>`).join('');
  }

  // ------------------------------------------------------------ scrubber
  const scrub = $('scrub');
  let scrubImage = null;
  function drawScrubber() {
    const dpr = window.devicePixelRatio || 1;
    const w = scrub.clientWidth, h = scrub.clientHeight;
    scrub.width = w * dpr; scrub.height = h * dpr;
    const ctx = scrub.getContext('2d');
    ctx.scale(dpr, dpr);
    ctx.clearRect(0, 0, w, h);
    const top = 16, bottom = h - 2, ph = bottom - top;
    const n = week.people.length;
    const step = 10;
    const x = m => (m / WEEK) * w;
    const awake = [], asleep = [];
    for (let m = 0; m < WEEK; m += step) {
      let a = 0, s = 0;
      for (const p of week.people) { const pr = week.presence[p.id]; if (pr.zone[m] >= 0) { if (pr.state[m] === 2) s++; else a++; } }
      awake.push(a); asleep.push(s);
    }
    ctx.fillStyle = css('--rule');
    for (let d = 0; d < 7; d++) if (d % 2) ctx.fillRect(x(d * DAY), top, x(DAY), ph);
    const area = (vals, base, color) => {
      ctx.beginPath(); ctx.moveTo(0, bottom);
      vals.forEach((v, i) => { const yy = bottom - ((v + (base ? base[i] : 0)) / n) * ph; ctx.lineTo(x(i * step), yy); ctx.lineTo(x((i + 1) * step), yy); });
      for (let i = vals.length - 1; i >= 0; i--) { const yy = bottom - ((base ? base[i] : 0) / n) * ph; ctx.lineTo(x((i + 1) * step), yy); ctx.lineTo(x(i * step), yy); }
      ctx.closePath(); ctx.fillStyle = color; ctx.fill();
    };
    ctx.globalAlpha = 0.85; area(asleep, null, css('--moon'));
    ctx.globalAlpha = 0.9; area(awake, asleep, css('--lamp'));
    ctx.globalAlpha = 1;
    ctx.fillStyle = css('--ink'); ctx.font = `600 11px ${css('--font-ui')}`;
    for (let d = 0; d < 7; d++) {
      ctx.fillText(DAY_NAMES[d].slice(0, 3).toUpperCase(), x(d * DAY) + 5, 11);
      ctx.fillStyle = css('--hair'); ctx.fillRect(Math.round(x(d * DAY)), 0, 1, h); ctx.fillStyle = css('--ink');
    }
    scrubImage = scrub.width && scrub.height ? ctx.getImageData(0, 0, scrub.width, scrub.height) : null;
  }
  function drawScrubHead(t) {
    if (!scrubImage) return;
    const ctx = scrub.getContext('2d');
    const dpr = window.devicePixelRatio || 1;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.putImageData(scrubImage, 0, 0);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    const w = scrub.clientWidth, h = scrub.clientHeight;
    const xx = (t / WEEK) * w;
    ctx.fillStyle = css('--ink');
    ctx.fillRect(xx - 1, 0, 2, h);
    ctx.beginPath(); ctx.moveTo(xx - 5, 0); ctx.lineTo(xx + 5, 0); ctx.lineTo(xx, 6); ctx.fill();
  }
  let dragging = false;
  const scrubTo = e => { const r = scrub.getBoundingClientRect(); setTime(Math.max(0, Math.min(1, (e.clientX - r.left) / r.width)) * WEEK); };
  scrub.addEventListener('pointerdown', e => { dragging = true; scrub.setPointerCapture(e.pointerId); scrubTo(e); });
  scrub.addEventListener('pointermove', e => { if (dragging) scrubTo(e); });
  scrub.addEventListener('pointerup', () => { dragging = false; });

  // ------------------------------------------------------------ calendar
  let calRows = [];
  function buildCalendarRows() {
    calRows = [];
    const merge = blocks => {
      const out = [];
      for (const b of blocks) {
        const l = out[out.length - 1];
        // Same kind of activity back to back reads as one block; keep the labels for the tooltip.
        if (l && l.act === b.act && Math.abs(l.t1 - b.t0) < 1e-6) { l.t1 = b.t1; if (!l.labels.includes(b.label)) l.labels.push(b.label); }
        else out.push(Object.assign({ labels: [b.label] }, b));
      }
      return out;
    };
    for (const p of week.people.filter(p => p.role !== 'guest')) {
      const blocks = week.agendas[p.id].filter(b => !b.hidden).map(b => ({ t0: b.t0, t1: b.t1, act: b.act || (b.away ? 'away' : 'free'), label: b.away || b.label }));
      calRows.push({ id: p.id, name: p.name, initial: p.initial, color: p.color, blocks: merge(blocks) });
    }
    const guests = week.people.filter(p => p.role === 'guest');
    if (guests.length) {
      const blocks = [];
      let start = null, peak = 0;
      for (let m = 0; m <= WEEK; m++) {
        const n = m < WEEK ? guests.filter(g => week.presence[g.id].zone[m] >= 0).length : 0;
        if (n && start === null) { start = m; peak = n; }
        if (n) peak = Math.max(peak, n);
        if (!n && start !== null) { blocks.push({ t0: start, t1: m, act: 'social', label: `${peak} guests` }); start = null; }
      }
      calRows.push({ id: 'guests', name: 'Guests', initial: 'G', color: guests[0].color, blocks });
    }
  }
  const blockLabel = b => (b.labels && b.labels.length > 1 ? b.labels.slice(0, 4).join(', ') + (b.labels.length > 4 ? '…' : '') : b.label);
  const calSvg = $('calendar');
  let calGeom = null;
  function drawCalendar() {
    calSvg.innerHTML = '';
    calSvg.setAttribute('shape-rendering', 'crispEdges');
    const W = Math.max(640, calSvg.parentElement.clientWidth);
    const lanes = calRows.length;
    if (ui.cal === 'grid') {
      const left = 38, top = 36, hourH = 15, H24 = 24 * hourH;
      const colW = (W - left - 4) / 7, laneW = colW / lanes;
      calSvg.setAttribute('width', W); calSvg.setAttribute('height', top + H24 + 6);
      calGeom = { mode: 'grid', left, top, hourH, colW };
      for (let h = 0; h <= 24; h += 3) {
        svg('line', { x1: left, x2: W - 4, y1: top + h * hourH, y2: top + h * hourH, stroke: css('--rule'), 'stroke-width': 1 }, calSvg);
        if (h < 24) svg('text', { x: left - 6, y: top + h * hourH + 4, 'text-anchor': 'end', class: 'num' }, calSvg).textContent = String(h).padStart(2, '0');
      }
      for (let d = 0; d < 7; d++) {
        const x0 = left + d * colW;
        svg('text', { x: x0 + 3, y: 13, class: 'dayname' }, calSvg).textContent = DAY_NAMES[d].slice(0, 3).toUpperCase();
        calRows.forEach((r, i) => {
          const t = svg('text', { x: x0 + i * laneW + laneW / 2, y: 29, 'text-anchor': 'middle' }, calSvg);
          t.textContent = r.initial; t.style.fill = markColor(r.color); t.style.fontWeight = 700;
        });
        svg('line', { x1: x0, x2: x0, y1: 18, y2: top + H24, stroke: css('--hair'), 'stroke-width': 1 }, calSvg);
        calRows.forEach((r, i) => {
          for (const b of r.blocks) {
            const s = Math.max(b.t0, d * DAY), e = Math.min(b.t1, (d + 1) * DAY);
            if (e <= s) continue;
            const y = top + ((s - d * DAY) / 60) * hourH, hgt = Math.max(0.8, ((e - s) / 60) * hourH);
            const bx = x0 + i * laneW + 1.5, bw = laneW - 3;
            const g = svg('g', {}, calSvg);
            svg('title', {}, g).textContent = `${r.name} · ${blockLabel(b)} · ${E.clock(b.t0)}–${E.clock(b.t1)}`;
            svg('rect', { x: bx, y, width: bw, height: hgt, fill: `var(--act-${b.act})` }, g);
            svg('rect', { x: bx, y, width: Math.min(2.5, bw), height: hgt, fill: markColor(r.color) }, g);
          }
        });
      }
      calGeom.head = svg('g', {}, calSvg);
    } else {
      const left = 74, top = 22, rowH = 11, gap = 10;
      const groupH = lanes * rowH + gap;
      const plotW = W - left - 6;
      calSvg.setAttribute('width', W); calSvg.setAttribute('height', top + 7 * groupH + 4);
      calGeom = { mode: 'lanes', left, top, rowH, groupH, plotW };
      for (let h = 0; h <= 24; h += 3) {
        const x = left + (h / 24) * plotW;
        svg('line', { x1: x, x2: x, y1: top - 4, y2: top + 7 * groupH - gap, stroke: css('--rule'), 'stroke-width': 1 }, calSvg);
        if (h < 24) svg('text', { x: x + 2, y: top - 8, class: 'num' }, calSvg).textContent = String(h).padStart(2, '0') + ':00';
      }
      for (let d = 0; d < 7; d++) {
        const y0 = top + d * groupH;
        svg('text', { x: 0, y: y0 + rowH * 1.4, class: 'dayname' }, calSvg).textContent = DAY_NAMES[d].slice(0, 3).toUpperCase();
        calRows.forEach((r, i) => {
          const t = svg('text', { x: left - 8, y: y0 + i * rowH + rowH - 2, 'text-anchor': 'end' }, calSvg);
          t.textContent = r.initial; t.style.fill = markColor(r.color); t.style.fontWeight = 700; t.style.fontSize = '10px';
          for (const b of r.blocks) {
            const s = Math.max(b.t0, d * DAY), e = Math.min(b.t1, (d + 1) * DAY);
            if (e <= s) continue;
            const x = left + ((s - d * DAY) / DAY) * plotW, w = Math.max(0.8, ((e - s) / DAY) * plotW);
            const y = y0 + i * rowH;
            const g = svg('g', {}, calSvg);
            svg('title', {}, g).textContent = `${r.name} · ${blockLabel(b)} · ${E.clock(b.t0)}–${E.clock(b.t1)}`;
            svg('rect', { x, y: y + 0.5, width: w, height: rowH - 1.5, fill: `var(--act-${b.act})` }, g);
            svg('rect', { x, y: y + rowH - 2.5, width: w, height: 1.5, fill: markColor(r.color) }, g);
          }
        });
      }
      calGeom.head = svg('g', {}, calSvg);
    }
    drawCalHead(ui.t);
  }
  function drawCalHead(t) {
    if (!calGeom) return;
    const g = calGeom.head;
    g.innerHTML = '';
    const d = Math.min(6, Math.floor(t / DAY)), tod = t - d * DAY;
    const ink = css('--ink');
    if (calGeom.mode === 'grid') {
      const { left, top, hourH, colW } = calGeom;
      const y = top + (tod / 60) * hourH, x0 = left + d * colW;
      svg('rect', { x: x0, y: 18, width: colW, height: 24 * hourH + top - 18, fill: 'none', stroke: ink, 'stroke-width': 1.2 }, g);
      svg('line', { x1: x0 - 4, x2: x0 + colW, y1: y, y2: y, stroke: ink, 'stroke-width': 2 }, g);
      svg('circle', { cx: x0 - 4, cy: y, r: 3.5, fill: ink }, g);
    } else {
      const { left, top, groupH, plotW, rowH } = calGeom;
      const x = left + (tod / DAY) * plotW, y0 = top + d * groupH;
      svg('line', { x1: x, x2: x, y1: y0 - 3, y2: y0 + calRows.length * rowH + 2, stroke: ink, 'stroke-width': 2 }, g);
      svg('circle', { cx: x, cy: y0 - 3, r: 3.5, fill: ink }, g);
    }
  }
  calSvg.addEventListener('click', e => {
    if (!calGeom) return;
    const r = calSvg.getBoundingClientRect();
    const x = e.clientX - r.left, y = e.clientY - r.top;
    if (calGeom.mode === 'grid') {
      const { left, top, hourH, colW } = calGeom;
      const d = Math.floor((x - left) / colW);
      if (d < 0 || d > 6 || y < top) return;
      setTime(d * DAY + Math.max(0, Math.min(DAY - 1, ((y - top) / hourH) * 60)));
    } else {
      const { left, top, groupH, plotW } = calGeom;
      const d = Math.floor((y - top) / groupH);
      if (d < 0 || d > 6 || x < left) return;
      setTime(d * DAY + Math.max(0, Math.min(DAY - 1, ((x - left) / plotW) * DAY)));
    }
  });

  // ------------------------------------------------------------ sky card
  // The card takes the colour of the sky over the house at the playhead, like the companion app.
  const LOC = PLAN.location || { lat: 41.9, lon: -74.1, utcOffsetHours: -5, label: '' };
  const RAD = Math.PI / 180;
  function sunElevation(minute) {
    const [Y, M, D] = (H.weekStart || '2026-11-02').split('-').map(Number);
    const d = (Date.UTC(Y, M - 1, D) + (minute - LOC.utcOffsetHours * 60) * 60000) / 86400000 - 10957.5;
    const g = (357.529 + 0.98560028 * d) * RAD, q = 280.459 + 0.98564736 * d;
    const L = (q + 1.915 * Math.sin(g) + 0.02 * Math.sin(2 * g)) * RAD, ob = (23.439 - 0.00000036 * d) * RAD;
    const ra = Math.atan2(Math.cos(ob) * Math.sin(L), Math.cos(L)), dec = Math.asin(Math.sin(ob) * Math.sin(L));
    const gmst = (((18.697374558 + 24.06570982441908 * d) % 24) + 24) % 24;
    const ha = (gmst * 15 + LOC.lon) * RAD - ra, lat = LOC.lat * RAD;
    return Math.asin(Math.sin(lat) * Math.sin(dec) + Math.cos(lat) * Math.cos(dec) * Math.cos(ha)) / RAD;
  }
  const SKY = [[-18, '#0B1E3F'], [-12, '#1D4174'], [-7, '#32609A'], [-3, '#6F93B6'], [-0.8, '#E9A86A'], [2, '#F0954A'], [6, '#F4B272'], [12, '#D8D3C1'], [22, '#B4CBDC'], [40, '#9DBFDA']];
  const hex = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  function skyColor(e) {
    if (e <= SKY[0][0]) return hex(SKY[0][1]);
    for (let i = 1; i < SKY.length; i++) if (e <= SKY[i][0]) {
      const f = (e - SKY[i - 1][0]) / (SKY[i][0] - SKY[i - 1][0]), a = hex(SKY[i - 1][1]), b = hex(SKY[i][1]);
      return a.map((c, k) => Math.round(c + (b[k] - c) * f));
    }
    return hex(SKY[SKY.length - 1][1]);
  }
  const phaseOf = e => e < -18 ? 'Night' : e < -12 ? 'Astronomical twilight' : e < -6 ? 'Nautical twilight' : e < -0.833 ? 'Civil twilight' : e < 6 ? 'Golden hour' : 'Daylight';
  const yOf = e => 100 * (1 - (Math.max(-50, Math.min(40, e)) + 50) / 90);
  const skyCache = {};
  function skyDay(d) {
    const key = ui.seed + '|' + d;
    if (skyCache[key]) return skyCache[key];
    const base = d * DAY, pts = [];
    let rise = null, set = null, prev = sunElevation(base);
    for (let m = 0; m <= DAY; m += 5) {
      const e = sunElevation(base + m);
      pts.push([m, yOf(e)]);
      if (m > 0 && prev < -0.833 && e >= -0.833) rise = m - 5 + 5 * (-0.833 - prev) / (e - prev);
      if (m > 0 && prev >= -0.833 && e < -0.833) set = m - 5 + 5 * (prev + 0.833) / (prev - e);
      prev = e;
    }
    // Household day: first long-sleeper up, last one down (residents only, the infant excluded).
    let wake = null, sleep = null;
    for (const p of week.people.filter(p => p.presence === 'resident' && p.role !== 'infant')) {
      const evs = week.events.filter(e => e.occupant === p.id && (e.type === 'wake' || e.type === 'sleep'));
      for (let i = 0; i < evs.length; i++) {
        const e = evs[i], next = evs[i + 1], before = evs[i - 1];
        if (e.type === 'wake' && e.minute > base + 180 && e.minute < base + 780 && (!before || e.minute - before.minute > 120)) { wake = wake === null ? e.minute : Math.min(wake, e.minute); break; }
      }
      for (let i = 0; i < evs.length; i++) {
        const e = evs[i], next = evs[i + 1];
        if (e.type === 'sleep' && e.minute > base + 1080 && e.minute < base + DAY + 180 && (!next || next.minute - e.minute > 120)) { sleep = sleep === null ? e.minute : Math.max(sleep, e.minute); break; }
      }
    }
    return (skyCache[key] = { pts, rise, set, wake: wake === null ? null : wake - base, sleep: sleep === null ? null : sleep - base });
  }
  let skyDrawn = null, skyRGB = '';
  function drawSkyCurve(d) {
    const info = skyDay(d);
    const c = $('sunCurve');
    c.innerHTML = '';
    const hy = yOf(0);
    const line = info.pts.map(([x, y]) => x + ',' + y.toFixed(2)).join(' ');
    const ns = { 'vector-effect': 'non-scaling-stroke', fill: 'none', stroke: 'currentColor' };
    const clip = svg('clipPath', { id: 'aboveHorizon' }, svg('defs', {}, c));
    svg('rect', { x: 0, y: -5, width: 1440, height: hy + 5 }, clip);
    svg('polygon', { points: `0,${hy} ${line} 1440,${hy}`, fill: 'currentColor', 'fill-opacity': 0.14, 'clip-path': 'url(#aboveHorizon)' }, c);
    svg('line', Object.assign({ x1: 0, x2: 1440, y1: hy, y2: hy, 'stroke-opacity': 0.45, 'stroke-width': 1 }, ns), c);
    svg('polyline', Object.assign({ points: line, 'stroke-opacity': 0.45, 'stroke-width': 1.5 }, ns), c);
    svg('polyline', Object.assign({ points: line, 'stroke-width': 2.5, 'clip-path': 'url(#aboveHorizon)' }, ns), c);
    const sched = occupantSchedule(d);
    for (const [k, id, label] of [['wake', 'markWake', 'Wake'], ['sleep', 'markSleep', 'Sleep']]) {
      const v = sched ? sched[k] : info[k], el = $(id);
      if (v === null || v === undefined) { el.hidden = true; continue; }
      const x = Math.min(1440, v);
      svg('line', Object.assign({ x1: x, x2: x, y1: 0, y2: 155, 'stroke-opacity': 0.7, 'stroke-width': 1, 'stroke-dasharray': '3 3' }, ns), c);
      el.hidden = false; el.style.left = (x / 14.4) + '%';
      el.textContent = label; el.title = (k === 'wake' ? 'Wake: ' : 'Lights off: ') + E.clock(v);
    }
    drawLightStrip(d);
    const fmt = m => m === null ? '–' : E.clock(m);
    $('rRise').textContent = fmt(info.rise); $('rSet').textContent = fmt(info.set);
    const dl = info.rise !== null && info.set !== null ? Math.round(info.set - info.rise) : null;
    $('rLight').textContent = dl === null ? '–' : `${Math.floor(dl / 60)}h ${String(dl % 60).padStart(2, '0')}m`;
    const [Y, M, D] = (H.weekStart || '2026-11-02').split('-').map(Number);
    $('rDate').textContent = new Date(Date.UTC(Y, M - 1, D + d)).toLocaleDateString('en-US', { weekday: 'short', month: 'short', day: 'numeric', timeZone: 'UTC' });
    $('dayPrev').disabled = d === 0; $('dayNext').disabled = d === 6;
    $('rLoc').textContent = LOC.label || PLAN.name;
    skyDrawn = skyKey(d);
  }
  const skyKey = d => [ui.seed, d, ui.occupant].join('|');
  const hmToMin = t => { const [h, m] = t.split(':').map(Number); return h * 60 + m; };
  function occupantSchedule(d) {
    if (!LIGHT.prefs) return null;
    const dayType = d >= 5 ? 'weekend' : 'weekday';
    const owner = ui.occupant === 'home' ? LIGHT.prefs.shared : LIGHT.prefs.people[ui.occupant];
    if (!owner) return { wake: null, sleep: null };
    const sc = owner.schedule[dayType];
    return { wake: hmToMin(sc.wake), sleep: hmToMin(sc.sleep) };
  }
  // CCT and intensity preview: column height is brightness, column colour is colour temperature.
  function sizeCanvas(cv) {
    const dpr = window.devicePixelRatio || 1, w = Math.round(cv.clientWidth * dpr), h = Math.round(cv.clientHeight * dpr);
    if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
    return [w, h];
  }
  function drawLightStrip(d) {
    const cv = $('lightStrip'), [w, h] = sizeCanvas(cv);
    if (!w || !h || !LIGHT.prefs) return;
    const ctx = cv.getContext('2d');
    ctx.clearRect(0, 0, w, h);
    const who = ui.occupant === 'home' || !LIGHT.prefs.people[ui.occupant] ? 'home' : ui.occupant;
    for (let x = 0; x < w; x++) {
      const v = LIGHT.previewAt(week, who, d * DAY + ((x + 0.5) / w) * 1440 | 0, ui.floor);
      const y = Math.round(h * (1 - v.intensity));
      if (y >= h) continue;
      ctx.fillStyle = `rgb(${LIGHT.kelvinToRgb(v.kelvin).join(',')})`;
      ctx.fillRect(x, y, 1, h - y);
    }
  }
  // Occupant dropdown, matching the other app.
  function occupantList() {
    const nameOf = id => (H.occupants.find(o => o.id === id) || {}).name;
    return [{ id: 'home', name: 'Whole home' }].concat(H.occupants.map(o => ({ id: o.id, name: nameOf(o.id), initial: o.initial, color: o.color })));
  }
  const restingFocus = () => ui.occupant === 'home' ? null : ui.occupant;
  function syncOccupant() {
    const list = occupantList();
    if (!list.some(o => o.id === ui.occupant)) ui.occupant = 'home';
    const sel = $('occupant');
    sel.innerHTML = list.map(o => `<option value="${o.id}">${esc(o.name)}</option>`).join('');
    sel.value = ui.occupant;
    const cur = list.find(o => o.id === ui.occupant), av = $('whoAvatar');
    $('whoName').textContent = cur.name;
    av.textContent = cur.id === 'home' ? '⌂' : cur.initial;
    av.style.background = cur.id === 'home' ? '#5F6470' : cur.color;
    av.style.color = cur.id === 'home' ? '#FFFFFF' : onColor(cur.color);
    ui.focus = restingFocus();
    planSvg.toggleAttribute('data-focus', !!ui.focus);
  }
  function updateSky(t) {
    const d = Math.min(6, Math.floor(t / DAY)), tod = t - d * DAY;
    if (skyDrawn !== skyKey(d)) drawSkyCurve(d);
    const e = sunElevation(t);
    const rgb = skyColor(e), key = rgb.join(',');
    if (key !== skyRGB) {
      skyRGB = key;
      const lum = (0.2126 * rgb[0] + 0.7152 * rgb[1] + 0.0722 * rgb[2]) / 255;
      const sky = $('sky');
      sky.style.setProperty('--sky-bg', `rgb(${key})`);
      sky.style.setProperty('--sky-fg', lum > 0.55 ? '#14203A' : '#FFFFFF');
    }
    $('rPhase').textContent = `${phaseOf(e)} · Sun ${Math.round(e) < 0 ? '−' + Math.abs(Math.round(e)) : Math.round(e)}°`;
    const dot = $('sunDot');
    dot.style.left = (tod / 14.4) + '%';
    dot.style.top = yOf(e) + '%';
    const drop = $('sunDrop');
    drop.style.left = (tod / 14.4) + '%';
    drop.style.top = yOf(e) + '%';
    const r = $('sunRange');
    if (document.activeElement !== r) r.value = Math.round(tod);
    r.setAttribute('aria-valuetext', `${DAY_NAMES[d]} ${E.clock(t)}, ${phaseOf(e).toLowerCase()}`);
  }

  // ------------------------------------------------------------ playback
  // Side column: grows quickly when it needs room, and only shrinks once it has been shorter for a few seconds.
  const SIDE_HOLD = 3000, SIDE_GROW = '.45s', SIDE_SHRINK = '2s';
  let sideSamples = [], sideHeight = 0;
  function easeSide(now) {
    const natural = $('sideInner').offsetHeight;
    if (!natural) return;
    sideSamples.push([now, natural]);
    while (sideSamples[0][0] < now - SIDE_HOLD) sideSamples.shift();
    const want = Math.max(...sideSamples.map(x => x[1]));
    if (want === sideHeight) return;
    const side = $('side');
    side.style.transitionDuration = !sideHeight ? '0s' : want > sideHeight ? SIDE_GROW : SIDE_SHRINK;
    side.style.height = want + 'px';
    sideHeight = want;
  }
  let lastSide = 0, lastTs = null;
  function frame(force) {
    const t = ui.t;
    const d = Math.min(6, Math.floor(t / DAY));
    $('rTime').textContent = E.clock(t);
    updateSky(t);
    drawPeople(t);
    drawZones(t);
    drawScrubHead(t);
    const now = performance.now();
    if (force || now - lastSide > 120) { renderSide(t); renderLights(); drawCalHead(t); lastSide = now; easeSide(now); }
  }
  function tick(ts) {
    if (ui.playing) {
      if (lastTs !== null) {
        ui.t += ((ts - lastTs) / 1000) * ui.speed;
        if (ui.t >= WEEK - 1e-3) { ui.t = WEEK - 1e-3; setPlaying(false); }
      }
      lastTs = ts;
      frame(false);
    } else lastTs = null;
    requestAnimationFrame(tick);
  }
  function setTime(t) { ui.t = Math.max(0, Math.min(WEEK - 1e-3, t)); frame(true); }
  // The sun is the slider: moving it changes the time within the day on screen.
  {
    const r = $('sunRange'), wrap = $('sunWrap');
    r.addEventListener('pointerdown', () => { setPlaying(false); wrap.classList.add('dragging'); });
    window.addEventListener('pointerup', () => wrap.classList.remove('dragging'));
    r.addEventListener('input', () => {
      const d = Math.min(6, Math.floor(ui.t / DAY));
      setTime(d * DAY + Number(r.value));
    });
  }
  function setPlaying(on) {
    ui.playing = on;
    $('play').setAttribute('aria-label', on ? 'Pause' : 'Play');
    $('playIcon').setAttribute('d', on ? 'M2.5 1.5h3.2v11H2.5zM8.3 1.5h3.2v11H8.3z' : 'M3 1.5v11l9-5.5z');
    if (on && ui.t >= WEEK - 1) ui.t = 0;
  }

  let toastTimer = null;
  function toast(msg) {
    const el = $('toast');
    el.textContent = msg; el.classList.add('on');
    clearTimeout(toastTimer); toastTimer = setTimeout(() => el.classList.remove('on'), 2600);
  }
  const VERB = { wake: 'wakes up', sleep: 'falls asleep', depart: 'leaves', arrive: 'arrives home' };
  function nextEvent() {
    const ev = week.events.find(e => e.minute > ui.t + 0.02 && MILESTONES.has(e.type) && !(week.byId[e.occupant].role === 'guest' && e.type === 'depart' && false));
    if (!ev) { toast('No more events this week'); return; }
    setTime(ev.minute + 0.01);
    const p = week.byId[ev.occupant];
    const zone = ev.zone ? P.zones[P.zoneIndex[ev.zone]].name : '';
    toast(`${E.dayClock(ev.minute)} · ${p.name} ${VERB[ev.type]}${zone ? ' · ' + zone : ''}`);
  }

  // ------------------------------------------------------------ files
  async function saveFile(filename, text) {
    try {
      const dl = window.claude && window.claude.use ? await window.claude.use('downloads') : null;
      if (dl) { await dl.save({ filename, data: text }); toast('Saved ' + filename); return; }
    } catch (err) {
      if (err && err.code === 'declined') return;
    }
    const a = document.createElement('a');
    a.href = URL.createObjectURL(new Blob([text], { type: 'application/json' }));
    a.download = filename;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  }

  // ------------------------------------------------------------ controls
  $('speed').innerHTML = SPEEDS.map(([v, l]) => `<button type="button" data-v="${v}" aria-pressed="${v === ui.speed}">${l}</button>`).join('');
  $('speed').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    ui.speed = +b.dataset.v; store.set('speed', ui.speed);
    [...$('speed').children].forEach(x => x.setAttribute('aria-pressed', x === b));
  });
  $('days').innerHTML = DAY_NAMES.map((n, i) => `<button type="button" data-d="${i}" aria-pressed="false">${n.slice(0, 3)}</button>`).join('');
  $('days').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    setTime(+b.dataset.d * DAY + (ui.t % DAY));
  });
  $('play').addEventListener('click', () => setPlaying(!ui.playing));
  $('nextEvent').addEventListener('click', nextEvent);
  $('tTrails').checked = ui.trails;
  $('tTrails').addEventListener('change', e => { ui.trails = e.target.checked; store.set('trails', ui.trails); frame(true); });
  $('tDrawing').addEventListener('change', e => { ui.drawing = e.target.checked; planSvg.classList.toggle('drawing', ui.drawing); gUnder.forEach(i => { i.style.display = ui.drawing ? '' : 'none'; }); });
  const syncRooms = () => [...$('rooms').children].forEach(x => x.setAttribute('aria-pressed', x.dataset.v === ui.rooms));
  syncRooms();
  $('rooms').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    ui.rooms = b.dataset.v; store.set('rooms', ui.rooms); ui.heat = ui.rooms === 'heatmap' ? 'week' : 'off'; syncRooms(); drawHeat(); frame(true);
  });
  const syncFloor = () => document.querySelectorAll('#floorSeg button').forEach(b => b.setAttribute('aria-pressed', String(+b.dataset.v === ui.floor)));
  $('floorSeg').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    ui.floor = +b.dataset.v; store.set('floor', ui.floor); syncFloor(); skyDrawn = null; frame(true);
  });
  $('acuity').addEventListener('input', e => {
    ui.acuity = +e.target.value / 100;
    $('acuityVal').textContent = `Acuity ${e.target.value}%`;
    frame(true);
  });
  [...$('calMode').children].forEach(x => x.setAttribute('aria-pressed', x.dataset.v === ui.cal));
  $('calMode').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    ui.cal = b.dataset.v; store.set('cal', ui.cal);
    [...$('calMode').children].forEach(x => x.setAttribute('aria-pressed', x === b));
    drawCalendar();
  });
  $('acts').innerHTML = ACTS.map(a => `<span><i class="sw" style="background:var(--act-${a})"></i>${(H.activityTypes || {})[a] || a}</span>`).join('');

  const WORDS = ['maple', 'slate', 'heron', 'ember', 'cedar', 'harbor', 'linden', 'quartz', 'fern', 'orchard', 'river', 'basalt', 'meadow', 'willow', 'copper', 'aspen'];
  $('newWeek').addEventListener('click', () => {
    const r = Math.random;
    regenerate(WORDS[Math.floor(r() * WORDS.length)] + '-' + (100 + Math.floor(r() * 900)));
  });
  $('seed').addEventListener('keydown', e => { if (e.key === 'Enter' && e.target.value.trim()) regenerate(e.target.value.trim()); });
  $('seed').addEventListener('change', e => { if (e.target.value.trim() && e.target.value.trim() !== ui.seed) regenerate(e.target.value.trim()); });
  $('history').addEventListener('click', e => { const b = e.target.closest('button'); if (b) regenerate(b.dataset.seed); });
  $('who').addEventListener('mouseover', e => { const li = e.target.closest('li'); ui.focus = li ? li.dataset.id : null; planSvg.toggleAttribute('data-focus', !!ui.focus); frame(true); });
  $('who').addEventListener('mouseleave', () => { ui.focus = restingFocus(); planSvg.toggleAttribute('data-focus', !!ui.focus); frame(true); });

  $('exportEvents').addEventListener('click', () => saveFile(`events-${ui.seed}.json`, JSON.stringify(E.exportEvents(week, H, PLAN), null, 1)));
  $('exportHousehold').addEventListener('click', () => saveFile('household.json', JSON.stringify(H, null, 2)));
  $('loadHousehold').addEventListener('change', async e => {
    const f = e.target.files[0]; if (!f) return;
    try {
      const next = JSON.parse(await f.text());
      if (!Array.isArray(next.occupants)) throw new Error('No occupants list');
      const prev = H; H = next;
      try { regenerate(H.seed || ui.seed); toast(`Loaded ${f.name}: ${H.occupants.length} occupants`); }
      catch (err) { H = prev; regenerate(ui.seed); toast(`${f.name} could not run: ${err.message}`); }
    } catch (err) { toast(`${f.name} is not a household file: ${err.message}`); }
    e.target.value = '';
  });
  $('tNanny').checked = !!(H.options && H.options.nannyStaysThursday);
  $('tNanny').addEventListener('change', e => { ui.overrides.nannyStaysThursday = e.target.checked; regenerate(ui.seed); });

  document.addEventListener('keydown', e => {
    if (e.target.closest('input, textarea, select')) return;
    if (e.key === ' ') { e.preventDefault(); setPlaying(!ui.playing); }
    else if (e.key === 'ArrowRight') setTime(ui.t + (e.shiftKey ? 60 : 15));
    else if (e.key === 'ArrowLeft') setTime(ui.t - (e.shiftKey ? 60 : 15));
    else if (e.key === 'n' || e.key === 'N') nextEvent();
    else if (e.key >= '1' && e.key <= '7') setTime((+e.key - 1) * DAY + (ui.t % DAY));
  });


  // ------------------------------------------------------------ import from the other app
  // Import an export from the other app: nearest listed date of each day type to this week.
  function fromExport(X) {
    if (X.schema !== 'lunul.lighting-export' || !Array.isArray(X.occupants) || !X.sharedZones || !X.sharedZones[0]) throw new Error('not a lighting export');
    const ref = new Date((H.weekStart || '2026-11-02') + 'T12:00:00Z').getTime() + 3 * 864e5;
    const nearest = type => {
      let best = -1, gap = Infinity;
      X.dates.forEach((d, i) => { const g = Math.abs(new Date(d.date + 'T12:00:00Z').getTime() - ref); if (d.dayType === type && g < gap) { gap = g; best = i; } });
      return best;
    };
    const wd = nearest('weekday'), we = nearest('weekend');
    const entry = o => {
      const day = i => ({ b: o.lighting[i].brightnessPercent, k: o.lighting[i].colorK });
      const sc = t => ({ wake: t.wake, sleep: t.lightsOff, windDown: t.windDownStart });
      return { weekday: day(wd), weekend: day(we), schedule: { weekday: sc(o.schedule.weekdays), weekend: sc(o.schedule.weekends) } };
    };
    const old = H.lighting.preferences || { people: {} };
    const people = {}, skipped = [];
    const idFor = o => /parent a/i.test(o.name) ? 'parentA' : /parent b/i.test(o.name) ? 'parentB' : o.type === 'infant' ? 'infant' : /kid|child/i.test(o.name) ? 'kid' : null;
    for (const o of X.occupants) {
      const id = idFor(o);
      if (!id) { skipped.push(o.name); continue; }
      people[id] = Object.assign(entry(o), { rooms: (old.people[id] || {}).rooms || [] });
      const person = H.occupants.find(p => p.id === id);
      if (person) person.name = o.name;
    }
    return { next: Object.assign({}, old, { source: { generated: X.generated, weekday: X.dates[wd].date, weekend: X.dates[we].date }, palette: (X.colorPalette || []).map(c => [c.k, c.hex]), shared: entry(X.sharedZones[0]), people: Object.assign({}, old.people, people) }), skipped };
  }
  $('prefsImport').addEventListener('click', () => $('prefsFile').click());
  $('prefsFile').addEventListener('change', async e => {
    const f = e.target.files[0]; if (!f) return;
    try {
      const { next, skipped } = fromExport(JSON.parse(await f.text()));
      H.lighting.preferences = next;
      regenerate(ui.seed);
      frame(true);
      toast(`Imported ${f.name}${skipped.length ? `; not matched: ${skipped.join(', ')}` : ''}`);
    } catch (err) { toast(`${f.name} could not be imported: ${err.message}`); }
    e.target.value = '';
  });
  $('occupant').addEventListener('change', e => { ui.occupant = e.target.value; store.set('occupant', ui.occupant); syncOccupant(); frame(true); });
  $('dayPrev').addEventListener('click', () => setTime(ui.t - DAY));
  $('dayNext').addEventListener('click', () => setTime(ui.t + DAY));

  let resizeTimer = null, lastStacked = null;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      const stacked = chooseLayout().stacked;
      if (stacked !== lastStacked) { lastStacked = stacked; buildPlan(); }
      drawScrubber(); drawCalendar(); skyDrawn = null; frame(true);
    }, 120);
  });
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { drawScrubber(); drawCalendar(); drawHeat(); frame(true); });

  P = E.buildPlan(PLAN, H.walkingSpeed || 1);
  LIGHT = window.RhythmLighting.build(PLAN, P, H);
  buildPlan();
  lastStacked = layout.stacked;
  regenerate(ui.seed);
  syncFloor();
  $('acuity').value = Math.round(ui.acuity * 100);
  $('acuityVal').textContent = `Acuity ${Math.round(ui.acuity * 100)}%`;
  requestAnimationFrame(tick);
})();
