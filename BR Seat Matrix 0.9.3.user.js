// ==UserScript==
// @name         BR Seat Matrix 0.9.3
// @namespace    local.railway.seatmatrix
// @version      0.9.3
// @description  Find trains by route, or pick a train; seats + payable fares for every station pair (rate-limit aware, live rescan); plan split tickets and jump straight to buying them
// @match        https://eticket.railway.gov.bd/*
// @grant        none
// ==/UserScript==

(() => {
  'use strict';

const API = 'https://railspaapi.shohoz.com/v1.0/web';
  const SEAT_CLASS = 'AC_B'; // the site sends this in its own search call; the response still lists every class
  const BATCH = 3, STAGGER_MS = 50, BATCH_PAUSE_MS = 150, RETRIES = 2, RETRY_WAIT_MS = 1000;
  const MAX_SEG = 15;        // confirm before scanning a segment longer than this
  const CACHE_TTL_MS = 2 * 60 * 1000;   // seat counts older than this are re-fetched (no-service pairs never expire)
  const RETRIES_429 = 6;               // per request, each retry waits for the shared rate-limit pause
  const BACKOFF_BASE_S = 5, BACKOFF_MAX_S = 60;   // 5, 10, 20, 40, 60, 60 ... unless the server sends Retry-After
  const PACE_FLOOR_MS = 500, PACE_CEIL_MS = 1500;   // pause between requests after a 429: starts at the floor, doubles up to the ceiling
  const TAIL_ROUNDS = 3, TAIL_WAIT_S = 20, TICK_MS = 1000;   // automatic retry rounds for failed pairs
  const MON = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
  const JWT = /^eyJ[\w-]+\.[\w-]+\.[\w-]+$/;

// fare extras: the API's vat_amount covers the 15% AC-class VAT; berth classes also get a
  // bedroll charge added at booking (set BERTH_FEE = 0 if the site stops charging it).
  const BERTH_CLASSES = new Set(['AC_B', 'F_BERTH']);
  const BERTH_FEE = 50;

const sleep = ms => new Promise(r => setTimeout(r, ms));
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const toDMY = iso => { const [y, m, d] = iso.split('-'); return `${d}-${MON[+m - 1]}-${y}`; };
  const addDays = (iso, n) => {
    const d = new Date(iso + 'T00:00:00Z');
    d.setUTCDate(d.getUTCDate() + n);
    return d.toISOString().slice(0, 10);
  };
  const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

function urlParam(name) {
    return new URLSearchParams(location.search).get(name) || '';
  }

function defaultDate() {
    const doj = urlParam('doj');
    const m = /(\d{1,2})-([A-Za-z]{3})-(\d{4})/.exec(doj);
    if (m) {
      const mi = MON.findIndex(x => x.toLowerCase() === m[2].toLowerCase()) + 1;
      if (mi) return `${m[3]}-${String(mi).padStart(2, '0')}-${m[1].padStart(2, '0')}`;
    }
    return new Date().toISOString().slice(0, 10);
  }

// How many midnights the train has crossed by the time it leaves each stop (0 = same day as the first stop).
  function dayOffsets(routes) {
    let day = 0, last = -1;
    return routes.map(r => {
      for (const key of ['arrival_time', 'departure_time']) {
        const m = /(\d{1,2}):(\d{2})\s*(am|pm)/i.exec(r[key] || '');
        if (!m) continue;
        let h = (+m[1]) % 12;
        if (/pm/i.test(m[3])) h += 12;
        const mins = h * 60 + (+m[2]);
        if (last >= 0 && mins < last) day++;
        last = mins;
      }
      return day;
    });
  }

// ---- auth: read what the site already stored; nothing leaves except calls to the railway API ----
  const clean = v => {
    if (v == null) return null;
    let s = String(v).trim();
    try { const j = JSON.parse(s); if (typeof j === 'string') s = j; } catch {}
    return s.replace(/^"|"$/g, '') || null;
  };

// ---- login state, worked out locally from the stored token: no request is ever sent to find out ----
  let REJECTED = null;                                  // a token string the server has answered 401 to
  const hhmm = ms => new Date(ms).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
  const fmtLeft = ms => { const m = Math.max(0, Math.round(ms / 60000)); return m >= 60 ? `${Math.floor(m / 60)}h ${m % 60}m` : `${m}m`; };
  function jwtExp(token) {
    try {
      const p = token.split('.')[1].replace(/-/g, '+').replace(/_/g, '/');
      const o = JSON.parse(atob(p + '='.repeat((4 - p.length % 4) % 4)));
      return typeof o.exp === 'number' ? o.exp * 1000 : null;
    } catch { return null; }
  }
  function loginState() {
    const a = getAuth();
    if (!a.token) return { state: 'out', text: 'Not logged in. Log in on this site first.' };
    if (!a.key || !a.id) return { state: 'out', text: 'Login values incomplete (device key/id missing). Reload the page.' };
    if (a.token === REJECTED) return { state: 'rejected', text: 'The server rejected this session. Log out and back in on the site.' };
    const exp = jwtExp(a.token);
    if (exp == null) return { state: 'in', text: 'Logged in (session end unknown)' };
    const left = exp - Date.now();
    if (left < 30000) return { state: 'expired', text: `Session expired at ${hhmm(exp)}. Log in again.` };
    return { state: left < 15 * 60000 ? 'soon' : 'in', text: `Logged in · session ends ${hhmm(exp)} (${fmtLeft(left)} left)` };
  }
  function getAuth() {
    let token = null, key = null, id = null;
    const names = [];
    for (const store of [localStorage, sessionStorage]) {
      for (let i = 0; i < store.length; i++) {
        const k = store.key(i);
        if (k.startsWith('bsm:')) continue;       // never parse our own cache blobs
        names.push(k);
        const v = clean(store.getItem(k));
        if (!v) continue;
        if (JWT.test(v) && (!token || /token/i.test(k))) token = v;
        if (!key && /device.?key|ssdk/i.test(k)) key = v;
        if (!id && /device.?id|uudid/i.test(k)) id = v;
      }
    }
    return { token, key, id, names };
  }

// ---- rate-limit gate: one shared pause for every in-flight request ----
  const GATE = { until: 0, streak: 0, hits: 0, cuts: 0, msg: '' };   // cuts = hits that came after real progress (these measure the limit)
  const PACE = { batch: BATCH, pause: BATCH_PAUSE_MS };   // slows down after a 429 for the rest of the page session
  const HITS = [];                                         // recent rate-limit hits: { ts, after, waitS }
  let reqSinceHit = 0;
  try { const h = JSON.parse(localStorage.getItem('bsm:ratelimit') || '[]'); if (Array.isArray(h)) HITS.push(...h.slice(-10)); } catch {}

  async function waitGate() {
    while (Date.now() < GATE.until) {
      const left = Math.ceil((GATE.until - Date.now()) / 1000);
      setStatus(`${GATE.msg} Waiting ${left}s before continuing…`);
      await sleep(Math.min(1000, Math.max(10, GATE.until - Date.now())));
    }
  }

  function noteRateLimit(r) {
    const now = Date.now();
    if (now < GATE.until) return;                 // another request in the same wave already set the pause
    GATE.streak++; GATE.hits++;
    const ra = parseFloat(r.headers && r.headers.get ? r.headers.get('retry-after') : '');
    const backoff = Math.min(BACKOFF_MAX_S, BACKOFF_BASE_S * 2 ** Math.min(GATE.streak - 1, 4));
    const waitS = Number.isFinite(ra) && ra > 0 ? Math.min(ra, 300) : backoff;
    GATE.until = now + waitS * 1000;
    GATE.msg = `Rate limit hit after ${reqSinceHit} requests.`;
    if (reqSinceHit > 0) {
      GATE.cuts++;
      HITS.push({ ts: now, after: reqSinceHit, waitS });
      while (HITS.length > 10) HITS.shift();
      try { localStorage.setItem('bsm:ratelimit', JSON.stringify(HITS)); } catch {}
    }
    PACE.batch = 1;
    if (reqSinceHit > 0 || PACE.pause < PACE_FLOOR_MS) {   // slow down only if we were cut off after real progress; a hit straight after a pause means the penalty window is still open
      PACE.pause = Math.min(PACE_CEIL_MS, Math.max(PACE_FLOOR_MS, PACE.pause * 2));
    }
    console.info(`[BR Seat Matrix] 429 after ${reqSinceHit} requests; pausing ${waitS}s; new pace: ${PACE.batch} at a time, ${PACE.pause}ms apart.`);
    reqSinceHit = 0;
  }

  async function api(path, body) {
    let retried401 = false;
    for (let n = 0, n429 = 0; ; ) {
      await waitGate();
      const ls = loginState();
      if (ls.state !== 'in' && ls.state !== 'soon') throw Object.assign(new Error(ls.text), { status: 401, noRequest: true });
      const a = getAuth();
      if (!a.token || !a.key || !a.id) {
        throw new Error('Could not find login values (log in first). Storage key names seen: ' + a.names.join(', '));
      }
      const headers = {
        accept: 'application/json',
        authorization: 'Bearer ' + a.token,
        'x-device-id': a.id,
        'x-device-key': a.key,
        'x-requested-with': 'XMLHttpRequest',
      };
      if (body) headers['content-type'] = 'application/json';
      const r = await fetch(API + path, { method: body ? 'POST' : 'GET', headers, body, credentials: 'include' });
      if (r.status === 429) {
        noteRateLimit(r);
        if (++n429 > RETRIES_429) throw Object.assign(new Error('HTTP 429'), { status: 429, body: 'rate limited' });
        continue;
      }
      if (r.status >= 502 && r.status <= 504 && n < RETRIES) { n++; await sleep(RETRY_WAIT_MS); continue; }
      if (r.status === 401) {
        const now = getAuth().token;
        if (!retried401 && now && now !== a.token) { retried401 = true; continue; }   // the site rotated the token: retry once with the new one
        REJECTED = a.token;
        try { refreshLogin(); } catch {}
        throw Object.assign(new Error('The server rejected your session (401). Log out and back in on the site, then retry.'), { status: 401 });
      }
      if (!r.ok) {
        const text = (await r.text().catch(() => '')).slice(0, 200);
        throw Object.assign(new Error('HTTP ' + r.status), { status: r.status, body: text });
      }
      GATE.streak = 0; reqSinceHit++;
      return r.json();
    }
  }

const searchPath = (from, to, dmy) =>
    `/bookings/search-trips-v2?from_city=${encodeURIComponent(from)}&to_city=${encodeURIComponent(to)}` +
    `&date_of_journey=${encodeURIComponent(dmy)}&seat_class=${SEAT_CLASS}`;

const trainNoOf = trip => { const m = /\((\d+)\)/.exec(String(trip || '')); return m ? m[1] : null; };

// Normalise seat_types of any train object. pay = fare + VAT + berth fee (what you'd actually be charged).
  function typesOf(t) {
    return (t.seat_types || []).map(s => {
      const online = +s.seat_counts?.online || 0, offline = +s.seat_counts?.offline || 0;
      const base = s.fare != null ? +s.fare : null;
      const vat = s.vat_amount != null ? +s.vat_amount : 0;
      const pay = base != null ? base + vat + (BERTH_CLASSES.has(s.type) ? BERTH_FEE : 0) : null;
      return { name: s.type || '?', online, offline, total: online + offline, fare: base, vat, pay };
    });
  }

// Pull our train out of a search result.
  function pickTrain(res, trainNo) {
    const t = (res?.data?.trains || []).find(x => trainNoOf(x.trip_number) === trainNo);
    if (!t) return null;
    const types = typesOf(t);
    return {
      departs: t.departure_date_time || '',
      types,
      online: types.reduce((a, x) => a + x.online, 0),
      offline: types.reduce((a, x) => a + x.offline, 0),
      total: types.reduce((a, x) => a + x.total, 0),
    };
  }

// ---- pair cache (sessionStorage, keyed by train + date; :t3 = adds timestamps; seat counts expire, no-service pairs don't) ----
  const cacheKey = () => `bsm:${R.train}:${R.date}:t3`;
  function loadPairs() {
    try {
      const arr = JSON.parse(sessionStorage.getItem(cacheKey()) || '[]');
      if (Array.isArray(arr)) return new Map(arr.filter(([k, v]) => v && !v.error && (v.missing || (v.ts && Date.now() - v.ts <= CACHE_TTL_MS))));
    } catch {}
    return new Map();
  }
  function savePairs() {
    try { sessionStorage.setItem(cacheKey(), JSON.stringify([...R.mat])); } catch {}
  }

// ---- last-scan snapshot (localStorage: survives reloads; exactly one, the most recent) ----
  function saveLastScan(fi, ti) {
    try {
      localStorage.setItem('bsm:lastscan', JSON.stringify({
        ts: Date.now(),
        train: R.train, date: R.date, name: R.name,
        stops: R.stops, offs: R.offs, fi, ti,
        mat: [...R.mat].filter(([, v]) => v && !v.error && !v.missing),
      }));
    } catch {}
  }

// ---- ticket plan (localStorage: bsm:plan) — the split-ticket cart ----
  let PLAN = null;   // { train, date, name, riskFirst, tickets: [{i,j,cls,seats,pay,from,to,doj,bought}] }
  function loadPlan() {
    try { PLAN = JSON.parse(localStorage.getItem('bsm:plan')); } catch {}
    if (!PLAN || !Array.isArray(PLAN.tickets)) PLAN = null;
  }
  function savePlan() {
    try { if (PLAN) localStorage.setItem('bsm:plan', JSON.stringify(PLAN)); else localStorage.removeItem('bsm:plan'); } catch {}
  }
  function isPlanned(i, j, cls) {
    if (!PLAN || PLAN.train !== R?.train || PLAN.date !== R?.date) return false;
    return PLAN.tickets.some(t => t.i === i && t.j === j && t.cls === cls);
  }

function togglePlan(i, j, cls) {
    const pair = R.mat?.get(`${i},${j}`);
    const type = pair?.types.find(t => t.name === cls);
    if (!type) { setStatus('That block has no live data to plan from.'); return; }
    if (PLAN && (PLAN.train !== R.train || PLAN.date !== R.date)) {
      const unbought = PLAN.tickets.filter(t => !t.bought).length;
      if (unbought && !confirm(`The current plan is for ${PLAN.name || PLAN.train} and has ${unbought} unbought ticket(s). Replace it with a new plan for this scan?`)) return;
      PLAN = null;
    }
    if (!PLAN) {
      PLAN = { train: R.train, date: R.date, name: R.name, riskFirst: true, tickets: [] };
    }
    const at = PLAN.tickets.findIndex(t => t.i === i && t.j === j && t.cls === cls);
    if (at >= 0) {
      PLAN.tickets.splice(at, 1);
      setStatus(`Removed ${R.stops[i]} → ${R.stops[j]} (${cls}) from the plan.`);
    } else {
      PLAN.tickets.push({
        i, j, cls,
        seats: type.total, pay: type.pay,
        from: R.stops[i], to: R.stops[j],
        doj: toDMY(addDays(R.date, R.offs[i])),   // per-leg date: overnight-safe
        bought: false,
      });
      setStatus(`Added ${R.stops[i]} → ${R.stops[j]} (${cls}, ${type.total} seats, ${type.pay != null ? type.pay + ' TK' : 'price ?'}) to the plan.`);
    }
    if (!PLAN.tickets.length) PLAN = null;
    savePlan();
    renderMatrix(+$('from').value, +$('to').value);
    renderPlan();
  }

// refresh planned seats/prices after a rescan (plan survives, numbers update)
  function refreshPlanFromMat() {
    if (!PLAN || PLAN.train !== R?.train || PLAN.date !== R?.date) return;
    for (const t of PLAN.tickets) {
      const type = R.mat?.get(`${t.i},${t.j}`)?.types.find(x => x.name === t.cls);
      if (type) { t.seats = type.total; t.pay = type.pay; }
    }
    savePlan();
  }

// ---- booking deep link: the site's own search page + our autopilot params ----
  // doj must be DMY (e.g. 27-Oct-2026); train/class are optional (train lets the autopilot pick the card).
  function bookingHref(from, to, dmy, train, cls) {
    const u = new URL(location.origin + '/booking/train/search');
    u.searchParams.set('fromcity', from);
    u.searchParams.set('tocity', to);
    u.searchParams.set('doj', dmy);
    if (cls) u.searchParams.set('class', cls);
    u.searchParams.set('bsm_autosearch', '1');
    if (train) u.searchParams.set('bsm_train', train);
    return u.href;
  }

function buyNext() {
    loadPlan();
    if (!PLAN?.tickets?.length) { setStatus('Plan is empty: scan a matrix, then click class blocks to add tickets.'); return; }
    const unbought = PLAN.tickets.filter(t => !t.bought);
    if (!unbought.length) { setStatus('All tickets in the plan are already marked bought. 🎉'); return; }
    const next = (PLAN.riskFirst ? [...unbought].sort((a, b) => a.seats - b.seats) : unbought)[0];
    window.open(bookingHref(next.from, next.to, next.doj, PLAN.train, next.cls), '_blank');   // new tab: panel + checklist stay visible here
    setStatus(`Opened ticket ${PLAN.tickets.length - unbought.length + 1}/${PLAN.tickets.length}: ${next.from} → ${next.to} (${next.cls}, ${next.seats} seats, ${next.doj}). Pick seats and pay there; come back and mark it done.`);
  }

// ---- UI ----
  const root = document.createElement('div');
  root.style.cssText = 'all:initial';
  root.innerHTML = `
  <style>
    #bsm-open { position:fixed;right:16px;bottom:16px;z-index:99999;font:600 13px system-ui,sans-serif;
      padding:8px 12px;border-radius:8px;border:0;background:#e08a3c;color:#111;cursor:grab;touch-action:none }
    #bsm-open:active { cursor:grabbing }
    #bsm-panel, #bsm-panel button, #bsm-panel select, #bsm-panel input { font:13px system-ui,sans-serif }
    #bsm-panel button, #bsm-panel select, #bsm-panel input { color:#eee }
    #bsm-panel { position:fixed;z-index:99998;color:#eee;background:#1b1b1d;border:1px solid #444;border-radius:10px;
      display:none;flex-direction:column;overflow:auto;resize:both;padding:0;
      min-width:420px;min-height:300px;max-width:98vw;max-height:92vh }
    .bsm-dragbar { cursor:grab;user-select:none;touch-action:none;text-align:center;padding:7px 12px;
      background:#232326;border-bottom:1px solid #333;border-radius:10px 10px 0 0;font-weight:600;letter-spacing:.04em;color:#e08a3c }
    .bsm-dragbar:active { cursor:grabbing }
    .bsm-body { display:flex;flex-direction:column;padding:12px;min-height:0;flex:1 }
    .bsm-hdr { display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin-bottom:8px }
    .bsm-mode { background:#2b2b2e;color:#bbb;border:1px solid #444;border-radius:6px;padding:4px 10px;cursor:pointer }
    .bsm-mode.on { background:#e08a3c;color:#111;border-color:#e08a3c;font-weight:600 }
    .bsm-panel button { background:#2b2b2e;border:1px solid #444;border-radius:6px;padding:4px 10px;cursor:pointer }
    .bsm-panel button:hover { border-color:#e08a3c }
    .bsm-panel button:disabled { opacity:.5;cursor:default }
    #bsm-panel label { display:flex;gap:6px;align-items:center;color:#bbb }
    #bsm-panel input { background:#2b2b2e;border:1px solid #444;border-radius:6px;padding:4px 8px }
    .bsm-swap { font-size:15px;padding:4px 12px !important }
    .bsm-note { opacity:.7;margin-bottom:4px;font-size:12px }
    .bsm-status { opacity:.85;margin:4px 0;white-space:pre-wrap;min-height:18px }
    .bsm-login { margin:4px 0;font-size:12px }
    .bsm-login[data-state="in"] { color:#4ADE80 } .bsm-login[data-state="soon"] { color:#FBBF24 }
    .bsm-login[data-state="out"], .bsm-login[data-state="expired"], .bsm-login[data-state="rejected"] { color:#F87171 }
    #bsm-open[data-login]::after { content:'';position:absolute;top:-3px;right:-3px;width:10px;height:10px;border-radius:50%;border:2px solid #1b1b1d;background:#F87171 }
    #bsm-open[data-login="in"]::after { background:#4ADE80 } #bsm-open[data-login="soon"]::after { background:#FBBF24 }
    .bsm-matwrap { overflow:auto;flex:1 1 auto;min-height:120px;border:1px solid #444;border-radius:8px }
    .bsm-mat { border-collapse:collapse;font-size:12px;white-space:nowrap }
    .bsm-mat th, .bsm-mat td { border:1px solid #333;padding:5px 8px;text-align:center;vertical-align:top }
    .bsm-mat thead th { position:sticky;top:0;background:#232326;z-index:2 }
    .bsm-mat tbody th { position:sticky;left:0;background:#232326;z-index:1;text-align:right }
    .bsm-cls { display:flex;flex-direction:column;gap:2px;align-items:center;min-width:96px;padding:2px 0;cursor:pointer }
    .bsm-cls:hover { outline:1px dashed #e08a3c }
    .bsm-cls.bsm-planned { outline:2px solid #e08a3c;border-radius:6px }
    .bsm-cls + .bsm-cls { border-top:1px dashed #3a3a3d;margin-top:6px;padding-top:6px }
    .bsm-name { font-size:11px;font-weight:600;letter-spacing:.03em;color:#A5B4FC;text-transform:uppercase }
    .bsm-count { font-size:16px;font-weight:700 }
    .bsm-c-red { color:#F87171 } .bsm-c-amber { color:#FBBF24 } .bsm-c-green { color:#4ADE80 }
    .bsm-units { font-size:11px;font-weight:400;color:#9CA3AF }
    .bsm-fare { font-size:12px;color:#D1D5DB }
    .bsm-x { color:#4B5563 } .bsm-dim { color:#555 }
    .bsm-legend { opacity:.7;font-size:11px;margin-top:6px }
    .bsm-card { border:1px solid #3a3a3d;border-radius:8px;padding:8px 10px;margin-bottom:8px;cursor:pointer;background:#232326 }
    .bsm-card:hover { border-color:#e08a3c }
    .bsm-card b { font-size:14px }
    .bsm-card .bsm-sub { opacity:.75;font-size:11px;margin:2px 0 6px }
    .bsm-chips { display:flex;gap:6px;flex-wrap:wrap }
    .bsm-chip { border:1px solid #3a3a3d;border-radius:6px;padding:3px 8px;font-size:11px;background:#1b1b1d }
    .bsm-cardtop { display:flex;gap:10px;align-items:flex-start;justify-content:space-between }
    .bsm-card .bsm-sub { margin-bottom:6px }
    .bsm-buy { background:#e08a3c !important;color:#111 !important;border:1px solid #e08a3c !important;
      border-radius:6px;padding:5px 12px !important;font-weight:600 !important;font-size:12px !important;
      cursor:pointer;white-space:nowrap }
    .bsm-buy:hover { background:#f0a05c !important;border-color:#f0a05c !important }
    .bsm-buychip { cursor:pointer;font-family:inherit;color:#eee;background:#1b1b1d !important;
      border:1px solid #3a3a3d !important;padding:3px 8px !important;font-size:11px !important;text-align:left }
    .bsm-buychip:hover { border-color:#e08a3c !important;background:#26262a !important }
    .bsm-planbar { border:1px solid #3a3a3d;border-radius:8px;margin-top:8px;padding:8px 10px;background:#232326 }
    .bsm-plhdr { display:flex;gap:8px;align-items:center;justify-content:space-between;margin-bottom:6px;font-weight:600 }
    .bsm-plrow { display:flex;gap:8px;align-items:center;justify-content:space-between;padding:4px 6px;border-radius:6px;cursor:pointer;font-size:12px }
    .bsm-plrow:hover { background:#1b1b1d }
    .bsm-plrow.bsm-bought { opacity:.45;text-decoration:line-through }
    .bsm-plfoot { display:flex;gap:8px;align-items:center;margin-top:6px }
    .bsm-scroll::-webkit-scrollbar { width:14px;height:14px }
    .bsm-scroll::-webkit-scrollbar-track { background:#232326;border-radius:8px }
    .bsm-scroll::-webkit-scrollbar-thumb { background:#e08a3c;border-radius:8px;border:3px solid #1b1b1d }
    .bsm-scroll::-webkit-scrollbar-thumb:hover { background:#f0a05c }
    .bsm-scroll::-webkit-scrollbar-corner { background:#1b1b1d }
  </style>
  <button id="bsm-open">Seat Matrix</button>
  <div id="bsm-panel">
    <div id="bsm-dragbar" class="bsm-dragbar">⋯ BR Seat Matrix v0.9.3 ⋯</div>
    <div class="bsm-body">
      <div class="bsm-hdr">
        <button id="bsm-mode-train" class="bsm-mode on">By train</button>
        <button id="bsm-mode-route" class="bsm-mode">By route</button>
        <label>Date <input id="bsm-date" type="date"></label>
      </div>
      <div class="bsm-hdr" id="bsm-row-train">
        <label>Train no. <input id="bsm-train" size="5" placeholder="770" style="width:70px"></label>
        <button id="bsm-load">Load route</button>
        <label>From <select id="bsm-from" disabled><option>load route first</option></select></label>
        <label>To <select id="bsm-to" disabled><option>load route first</option></select></label>
        <button id="bsm-scan">Scan matrix</button>
        <button id="bsm-rescan" title="Ignore cached seat counts and fetch every pair again">Rescan live</button>
        <button id="bsm-last" title="Recall the most recent scan without any API calls">Last scan</button>
      </div>
      <div class="bsm-hdr" id="bsm-row-route" style="display:none">
        <label>From <input id="bsm-rfrom" placeholder="Dhaka" style="width:130px"></label>
        <button id="bsm-swap" class="bsm-swap" title="Swap From and To">⇄</button>
        <label>To <input id="bsm-rto" placeholder="Tarakandi" style="width:130px"></label>
        <button id="bsm-find">Find trains</button>
      </div>
      <div class="bsm-note">By route: Date = the day you leave your From station. By train: Date = the day the train leaves its first station. Midnight crossings are handled automatically either way.</div>
      <div id="bsm-login" class="bsm-login"></div>
      <div id="bsm-status" class="bsm-status"></div>
      <div id="bsm-matwrap" class="bsm-scroll"><div id="bsm-out"></div></div>
      <div id="bsm-planbar" class="bsm-planbar bsm-scroll" style="display:none">
        <div class="bsm-plhdr"><span id="bsm-pltitle">Ticket plan</span>
          <span>
            <button id="bsm-risk" title="Sort Buy next by fewest seats first (scarcest leg first)">Risk-first: on</button>
            <button id="bsm-clearplan">Clear</button>
          </span>
        </div>
        <div id="bsm-planlist"></div>
        <div class="bsm-plfoot">
          <button id="bsm-buy" style="background:#e08a3c;color:#111;font-weight:600;border-color:#e08a3c">Buy next</button>
          <span id="bsm-plantotal" style="font-size:12px;opacity:.85"></span>
        </div>
      </div>
    </div>
  </div>`;
  document.body.appendChild(root);
  const $ = id => root.querySelector('#bsm-' + id);
  const setStatus = t => { $('status').textContent = t; };
  let lastLoginKey = '';
  function refreshLogin() {
    const ls = loginState();
    const k = ls.state + '|' + ls.text;
    if (k === lastLoginKey) return;                 // nothing changed: leave the page alone
    lastLoginKey = k;
    $('login').textContent = '● ' + ls.text;
    $('login').dataset.state = ls.state;
    $('open').dataset.login = ls.state;
  }
  setTimeout(refreshLogin, 0);
  setInterval(refreshLogin, 500);                 // cheap local read of a few storage keys; catches same-tab login/logout within half a second
  window.addEventListener('focus', refreshLogin);
  window.addEventListener('storage', refreshLogin);
  document.addEventListener('visibilitychange', refreshLogin);
  const setBusy = b => { for (const id of ['scan', 'rescan', 'load', 'last']) $(id).disabled = b; };

let R = null;           // { train, date, name, stops, offs, mat }
  let searched = null;    // { from, to, date } from By-route mode

// ---- generic drag helper: pointer events, clamped to viewport, click-vs-drag separation ----
  function makeDraggable(el, handle, onEnd) {
    let sx = 0, sy = 0, ox = 0, oy = 0, moved = false;
    handle.addEventListener('pointerdown', e => {
      if (e.button !== 0) return;
      sx = e.clientX; sy = e.clientY;
      const r = el.getBoundingClientRect();
      ox = r.left; oy = r.top;
      moved = false;
      handle.setPointerCapture(e.pointerId);
      const move = ev => {
        const dx = ev.clientX - sx, dy = ev.clientY - sy;
        if (Math.abs(dx) > 3 || Math.abs(dy) > 3) moved = true;
        if (!moved) return;
        el.style.left = clamp(ox + dx, 0, innerWidth - 60) + 'px';
        el.style.top = clamp(oy + dy, 0, innerHeight - 40) + 'px';
        el.style.right = 'auto'; el.style.bottom = 'auto';
      };
      const up = () => {
        handle.removeEventListener('pointermove', move);
        handle.removeEventListener('pointerup', up);
        if (moved && onEnd) onEnd();
      };
      handle.addEventListener('pointermove', move);
      handle.addEventListener('pointerup', up);
      e.preventDefault();
    });
    return () => moved;   // caller can check whether the pointer interaction was a drag
  }

const btnWasDragged = makeDraggable($('open'), $('open'), () => {
    try { const r = $('open').getBoundingClientRect(); localStorage.setItem('bsm:btnpos', JSON.stringify({ x: r.left, y: r.top })); } catch {}
  });

// restore button position (default: bottom-right)
  try {
    const p = JSON.parse(localStorage.getItem('bsm:btnpos'));
    if (p && isFinite(p.x) && isFinite(p.y)) {
      const b = $('open');
      b.style.left = clamp(p.x, 0, innerWidth - 100) + 'px';
      b.style.top = clamp(p.y, 0, innerHeight - 40) + 'px';
      b.style.right = 'auto'; b.style.bottom = 'auto';
    }
  } catch {}

// ---- panel box (position + size), persisted ----
  const panel = $('panel');
  function defaultBox() {
    const w = clamp(900, 420, innerWidth - 24), h = clamp(600, 300, innerHeight - 48);
    return { x: clamp(innerWidth - w - 16, 8, innerWidth - 100), y: clamp(innerHeight - h - 16, 8, innerHeight - 100), w, h };
  }
  function applyBox(b) {
    panel.style.left = b.x + 'px'; panel.style.top = b.y + 'px';
    panel.style.width = b.w + 'px'; panel.style.height = b.h + 'px';
    panel.style.right = 'auto'; panel.style.bottom = 'auto';
  }
  function savePanelBox() {
    if (panel.style.display === 'none') return;
    const r = panel.getBoundingClientRect();
    if (r.width < 50) return;
    try { localStorage.setItem('bsm:panelbox', JSON.stringify({ x: r.left, y: r.top, w: r.width, h: r.height })); } catch {}
  }
  makeDraggable(panel, $('dragbar'), savePanelBox);
  try { new ResizeObserver(() => savePanelBox()).observe(panel); } catch {}  // resize: both grip + window-driven resizes
  let panelBoxApplied = false;

// re-clamp if the window shrinks
  addEventListener('resize', () => {
    const r = panel.getBoundingClientRect();
    if (panel.style.display !== 'none' && r.width > 50) {
      panel.style.left = clamp(r.left, 0, Math.max(0, innerWidth - 100)) + 'px';
      panel.style.top = clamp(r.top, 0, Math.max(0, innerHeight - 60)) + 'px';
    }
    const b = $('open').getBoundingClientRect();
    if (b.width) {
      const o = $('open');
      o.style.left = clamp(b.left, 0, innerWidth - 100) + 'px';
      o.style.top = clamp(b.top, 0, innerHeight - 40) + 'px';
      if (b.left > innerWidth - 40 || b.top > innerHeight - 30) { o.style.right = '16px'; o.style.bottom = '16px'; o.style.left = o.style.top = 'auto'; }
    }
  });

// ---- panel open/close, mode switching ----
  $('open').onclick = () => {
    refreshLogin();
    if (btnWasDragged()) return;                 // a drag just happened; don't toggle
    if (!panelBoxApplied) {
      panelBoxApplied = true;
      let box = null;
      try { box = JSON.parse(localStorage.getItem('bsm:panelbox')); } catch {}
      applyBox(box && isFinite(box.x) ? box : defaultBox());
    }
    panel.style.display = panel.style.display === 'flex' ? 'none' : 'flex';
    if (panel.style.display === 'flex') {
      if (!$('date').value) $('date').value = defaultDate();
      if (!$('rfrom').value) $('rfrom').value = urlParam('fromcity');
      if (!$('rto').value) $('rto').value = urlParam('tocity');
      renderPlan();                              // plan bar comes back with the panel
    } else {
      savePanelBox();
    }
  };

function showMode(m) {
    const train = m === 'train';
    $('row-train').style.display = train ? 'flex' : 'none';
    $('row-route').style.display = train ? 'none' : 'flex';
    $('mode-train').classList.toggle('on', train);
    $('mode-route').classList.toggle('on', !train);
  }
  $('mode-train').onclick = () => showMode('train');
  $('mode-route').onclick = () => showMode('route');

$('swap').onclick = () => {
    const a = $('rfrom').value;
    $('rfrom').value = $('rto').value;
    $('rto').value = a;
  };

const reset = () => {
    R = null; $('out').innerHTML = ''; CARDS = null;
    for (const id of ['from', 'to']) { $(id).disabled = true; $(id).innerHTML = '<option>load route first</option>'; }
  };
  $('train').oninput = reset;
  $('date').onchange = reset;

// ---- By train mode ----
  async function loadRoute() {
    const train = $('train').value.trim(), date = $('date').value;
    if (!train || !date) throw new Error('Enter a train number and a date.');
    setStatus('Loading route…');
    const rd = await api('/train-routes', JSON.stringify({ model: train, departure_date_time: date }));
    if (!rd?.data?.routes?.length) throw new Error('No route found for train ' + train + ' on that date.');
    const stops = rd.data.routes.map(r => r.city);
    R = { train, date, name: rd.data.train_name || ('Train ' + train), stops, offs: dayOffsets(rd.data.routes), mat: null };
    fillSelects(0, stops.length - 1);
    return R;
  }

function fillSelects(fi, ti) {
    const opts = R.stops.map((s, i) => `<option value="${i}">${esc(s)}</option>`).join('');
    $('from').innerHTML = opts; $('from').value = String(fi);
    $('to').innerHTML = opts; $('to').value = String(ti);
    $('from').disabled = $('to').disabled = false;
  }

function tierOf(n) { return n === 0 ? 'red' : (n <= 2 ? 'amber' : 'green'); }

function blockHTML(t, i, j) {
    const planned = isPlanned(i, j, t.name) ? ' bsm-planned' : '';
    return `<div class="bsm-cls${planned}" data-i="${i}" data-j="${j}" data-cls="${esc(t.name)}" title="Click to add/remove from the ticket plan">
      <div class="bsm-name">${esc(t.name)}</div>
      <div class="bsm-count bsm-c-${tierOf(t.total)}">${t.total} <span class="bsm-units">Seats</span></div>
      <div class="bsm-fare">${t.pay != null ? esc(t.pay) + ' TK' : '—'}</div>
      ${t.vat > 0 ? `<div class="bsm-units">incl. ${esc(t.vat)} VAT</div>` : ''}
    </div>`;
  }

function cellHTML(i, j) {
    if (j <= i) return '<span class="bsm-x">✕</span>';
    const p = R.mat && R.mat.get(`${i},${j}`);
    if (!p) return '<span class="bsm-dim">…</span>';
    if (p.error) return `<span class="bsm-dim" title="${esc(p.error)}">?</span>`;
    if (p.missing) return '<span class="bsm-x">✕</span>';
    return p.types.length ? p.types.map(t => blockHTML(t, i, j)).join('') : '<span class="bsm-x">✕</span>';
  }

function renderMatrix(fi, ti) {
    const { stops } = R;
    let h = '<table class="bsm-mat"><thead><tr><th>From ↓</th>' +
      stops.slice(fi, ti + 1).map(s => `<th>${esc(s)}</th>`).join('') + '</tr></thead><tbody>';
    for (let i = fi; i < ti; i++) {
      h += `<tr><th>${esc(stops[i])}</th>`;
      for (let j = fi; j <= ti; j++) h += `<td>${cellHTML(i, j)}</td>`;
      h += '</tr>';
    }
    h += '</tbody></table>';
    h += `<div class="bsm-legend">Numbers = total seats (online + counter). 🔴 0 · 🟠 1–2 · 🟢 3+. TK = payable fare incl. VAT${BERTH_FEE ? ` + ৳${BERTH_FEE} berth charge (AC_B/F_BERTH)` : ''}. ✕ = train does not serve that pair. <b>Click a class block to add it to the ticket plan.</b></div>`;
    $('out').innerHTML = h;
  }

async function scanMatrix(force) {
    setBusy(true);
    try {
      if (!R) await loadRoute();
      const fi = +$('from').value, ti = +$('to').value;
      if (!(ti > fi)) throw new Error('Pick a To station that comes after your From station.');
      const n = ti - fi;
      if (n > MAX_SEG && !confirm(`${n} station gaps = ${n * (n + 1) / 2} pair lookups. Continue?`)) {
        throw new Error('Cancelled.');
      }
      R.mat = loadPairs();
      const { stops, offs, train } = R;
      const key = (i, j) => `${i},${j}`;
      const eachPair = fn => { for (let i = fi; i < ti; i++) for (let j = i + 1; j <= ti; j++) fn(i, j); };

      if (force) eachPair((i, j) => { const p = R.mat.get(key(i, j)); if (p && !p.missing) R.mat.delete(key(i, j)); });

      const makeJob = (i, j) => async () => {
        const dmy = toDMY(addDays(R.date, offs[i]));
        try {
          const res = await api(searchPath(stops[i], stops[j], dmy));
          const t = pickTrain(res, train);
          R.mat.set(key(i, j), { ...(t || { missing: true }), ts: Date.now() });
        } catch (e) {
          if (e.status === 401) throw e;
          R.mat.set(key(i, j), { error: 'HTTP ' + (e.status || e.message) + (e.body ? ' ' + e.body : ''), status: e.status || 0, ts: Date.now() });
        }
      };
      const todo = [];
      eachPair((i, j) => { if (!R.mat.has(key(i, j))) todo.push([i, j]); });
      const failedPairs = () => {
        const out = [];
        eachPair((i, j) => {
          const p = R.mat.get(key(i, j));
          if (p && p.error && (!p.status || p.status === 429 || p.status >= 500)) out.push([i, j]);
        });
        return out;
      };
      const runPairs = async (pairs, label) => {
        const jobs = pairs.map(([i, j]) => makeJob(i, j));
        let done = 0, k = 0, batchNo = 0;
        while (k < jobs.length) {
          const size = PACE.batch;                    // read once per round: PACE can change mid-scan after a 429
          await Promise.all(jobs.slice(k, k + size).map((job, idx) => sleep(idx * STAGGER_MS).then(job).then(() => { done++; })));
          k += size;
          setStatus(`${R.name}: ${label} ${done}/${jobs.length} pairs…`);
          if (batchNo++ % 5 === 0) savePairs();
          renderMatrix(fi, ti);
          await sleep(PACE.pause);
        }
        savePairs();
      };

      renderMatrix(fi, ti);
      if (!todo.length) {
        let oldest = Infinity;
        eachPair((i, j) => { const p = R.mat.get(key(i, j)); if (p && !p.missing && p.ts) oldest = Math.min(oldest, p.ts); });
        const age = Number.isFinite(oldest) ? ` (oldest numbers ${Math.round((Date.now() - oldest) / 1000)}s old)` : '';
        saveLastScan(fi, ti);
        refreshPlanFromMat();
        setStatus(`${R.name}: matrix is fresh enough, no requests needed${age}. Counts older than ${Math.round(CACHE_TTL_MS / 60000)} min refresh automatically; Rescan live forces it now.`);
        return;
      }

      const hits0 = GATE.hits, cuts0 = GATE.cuts;
      await runPairs(todo, force ? 'live scan' : 'checking');

      for (let round = 1; round <= TAIL_ROUNDS; round++) {
        const failed = failedPairs();
        if (!failed.length) break;
        for (let s = TAIL_WAIT_S; s > 0; s--) {
          setStatus(`${failed.length} pairs failed (rate limit). Retry round ${round}/${TAIL_ROUNDS} in ${s}s…`);
          await sleep(TICK_MS);
        }
        await runPairs(failed, `retry ${round}`);
      }

      saveLastScan(fi, ti);
      refreshPlanFromMat();
      const left = failedPairs().length;
      const newHits = GATE.hits - hits0;
      if (!newHits) { PACE.batch = BATCH; PACE.pause = BATCH_PAUSE_MS; }   // a clean scan restores the normal pace
      const newCuts = GATE.cuts - cuts0;
      const hitNote = newHits
        ? ` Rate limit hit ${newHits}×` + (newCuts ? ` (cut off after ${HITS.slice(-newCuts).map(h => h.after).join(', ')} requests).` : '.')
        : '';
      const okPairs = [...R.mat.values()].filter(p => !p.error && !p.missing).length;
      setStatus(`${R.name}: done. ${okPairs} served pairs.` +
        (left ? ` ${left} still failed: wait a minute and click Scan matrix again (only those are re-fetched).` : '') + hitNote);
      renderMatrix(fi, ti);
    } catch (e) {
      setStatus('Error: ' + e.message);
    } finally {
      setBusy(false);
    }
  }

function recallLastScan() {
    let s = null;
    try { s = JSON.parse(localStorage.getItem('bsm:lastscan')); } catch {}
    if (!s || !Array.isArray(s.stops) || !s.stops.length) { setStatus('No saved scan yet. Run Scan matrix first.'); return; }
    showMode('train');
    $('train').value = s.train; $('date').value = s.date;
    R = {
      train: s.train, date: s.date, name: s.name || ('Train ' + s.train),
      stops: s.stops, offs: s.offs || s.stops.map(() => 0),
      mat: new Map((s.mat || []).filter(([, v]) => v && !v.error && !v.missing)),
    };
    const ti = Math.min(s.ti, R.stops.length - 1), fi = Math.min(Math.max(0, s.fi), ti);
    fillSelects(fi, ti);
    renderMatrix(fi, ti);
    const when = new Date(s.ts).toLocaleString();
    setStatus(`${R.name} ${toDMY(R.date)}: recalled scan from ${when} — NOT live. Click Scan matrix to refresh seat counts.`);
  }

// ---- ticket plan UI ----
  function renderPlan() {
    loadPlan();
    const bar = $('planbar');
    if (!PLAN || !PLAN.tickets.length) { bar.style.display = 'none'; return; }
    bar.style.display = 'block';
    const bought = PLAN.tickets.filter(t => t.bought).length;
    $('pltitle').textContent = `Ticket plan — ${PLAN.name || 'Train ' + PLAN.train}, ${toDMY(PLAN.date)} (${bought}/${PLAN.tickets.length} bought)`;
    $('risk').textContent = 'Risk-first: ' + (PLAN.riskFirst ? 'on' : 'off');
    $('planlist').innerHTML = PLAN.tickets.map((t, k) => `
      <div class="bsm-plrow${t.bought ? ' bsm-bought' : ''}" data-k="${k}"
           title="Click to mark bought / unbought">
        <span>${esc(t.from)} → ${esc(t.to)}</span>
        <span>${esc(t.cls)} · <span class="bsm-c-${tierOf(t.seats)}" style="font-weight:700">${t.seats}</span> seats · ${esc(t.doj)}</span>
        <span class="bsm-fare">${t.pay != null ? esc(t.pay) + ' TK' : '—'}</span>
      </div>`).join('');
    [...$('planlist').querySelectorAll('.bsm-plrow')].forEach(el =>
      el.onclick = () => {
        const t = PLAN.tickets[+el.dataset.k];
        t.bought = !t.bought;
        savePlan();
        renderPlan();
        setStatus(t.bought
          ? `Marked ${t.from} → ${t.to} as bought.`
          : `Unmarked ${t.from} → ${t.to} — it counts as unbought again.`);
      });
    const unboughtSum = PLAN.tickets.filter(t => !t.bought).reduce((a, t) => a + (t.pay || 0), 0);
    const unboughtN = PLAN.tickets.length - bought;
    $('plantotal').textContent = unboughtN
      ? `${unboughtN} left · ${unboughtSum} TK to pay`
      : 'All bought 🎉';
  }

$('out').addEventListener('click', e => {
    const block = e.target.closest('.bsm-cls');                 // matrix cell → ticket plan
    if (block) {
      if (block.dataset.i == null || !R?.mat) return;
      togglePlan(+block.dataset.i, +block.dataset.j, block.dataset.cls);
      return;
    }
    const buy = e.target.closest('.bsm-buy, .bsm-buychip');      // By-route results → booking page
    if (buy && CARDS && CARDS[+buy.dataset.i]) {
      buyRouteTrain(CARDS[+buy.dataset.i], buy.dataset.cls || null);
      return;
    }
    const card = e.target.closest('.bsm-card');                  // card body → load route
    if (card && CARDS && CARDS[+card.dataset.i]) chooseTrain(CARDS[+card.dataset.i]);
  });

$('buy').onclick = buyNext;
  $('risk').onclick = () => {
    loadPlan();
    if (!PLAN) return;
    PLAN.riskFirst = !PLAN.riskFirst;
    savePlan();
    renderPlan();
    setStatus('Buy next will open ' + (PLAN.riskFirst ? 'the scarcest (fewest seats) unbought ticket first.' : 'tickets in the order you added them.'));
  };
  $('clearplan').onclick = () => {
    loadPlan();
    if (!PLAN?.tickets.length) return;
    if (!confirm('Remove all tickets from the plan?')) return;
    PLAN = null;
    savePlan();
    renderPlan();
    if (R?.mat) renderMatrix(+$('from').value, +$('to').value);
    setStatus('Plan cleared.');
  };

// ---- By route mode ----
  async function findTrains() {
    const from = $('rfrom').value.trim(), to = $('rto').value.trim(), date = $('date').value;
    if (!from || !to) throw new Error('Enter both From and To station names.');
    if (!date) throw new Error('Enter a date.');
    setStatus('Searching trains…');
    const res = await api(searchPath(from, to, toDMY(date)));
    const trains = res?.data?.trains || [];
    if (!trains.length) {
      searched = null;
      CARDS = null;
      $('out').innerHTML = '';
      setStatus('No trains found for that route on that date. Check the spelling (station names must match the site).');
      return;
    }
    searched = { from, to, date };
    renderTrains(trains);
    setStatus(`${trains.length} train(s) found. Click one to load its full route.`);
  }

function chipHTML(t, idx, trainNo) {
    const num = `<span class="bsm-c-${tierOf(t.total)}" style="font-weight:700">${t.total}</span>`;
    const label = `${esc(t.name)} ${num}` + (t.pay != null ? ` <span class="bsm-fare">${esc(t.pay)} TK</span>` : '');
    return `<button type="button" class="bsm-chip bsm-buychip" data-i="${idx}" data-cls="${esc(t.name)}"` +
      ` title="Open the site's booking page for train ${esc(trainNo || '?')}, class ${esc(t.name)}">${label}</button>`;
  }

// The class we'd suggest for a one-click buy: most seats, then cheapest payable fare.
  function bestClassOf(types) {
    const best = [...types].sort((a, b) =>
      (b.total - a.total) || ((a.pay ?? Infinity) - (b.pay ?? Infinity)))[0];
    return best ? best.name : null;
  }

// Jump straight to the site's booking flow for one train (and class) from the By-route results.
  function buyRouteTrain(t, cls) {
    if (!searched) { setStatus('Search by route first, then use Buy.'); return; }
    const num = trainNoOf(t.trip_number);
    const types = typesOf(t);
    const pick = cls || bestClassOf(types);
    const type = types.find(x => x.name === pick) || null;
    window.open(bookingHref(searched.from, searched.to, toDMY(searched.date), num, pick), '_blank');
    setStatus(`Opened the site's booking page: ${searched.from} → ${searched.to} on ${toDMY(searched.date)}` +
      (num ? `, train ${num}` : '') + (pick ? `, class ${pick}` : '') +
      (type ? ` (${type.total} seats, ${type.pay != null ? type.pay + ' TK' : 'price ?'} when scanned)` : '') +
      '. The helper selects that train and the fullest coach; pick your seats and pay there.');
  }

let CARDS = null;   // the train list currently shown in By-route mode, for delegated clicks

function renderTrains(trains) {
    let h = '';
    trains.forEach((t, idx) => {
      const types = typesOf(t);
      const num = trainNoOf(t.trip_number);
      h += `<div class="bsm-card" data-i="${idx}">
        <div class="bsm-cardtop">
          <span><b>${esc(String(t.trip_number || '?').replace(/\s*\(\d+\)\s*$/, ''))}</b>${num ? ` <span class="bsm-fare">#${esc(num)}</span>` : ''}</span>
          ${num ? `<button type="button" class="bsm-buy" data-i="${idx}"` +
            ` title="Open the site's booking page for (${esc(num)})${types.length ? ', class ' + esc(bestClassOf(types)) : ''}">Buy tickets ↗</button>` : ''}
        </div>
        <div class="bsm-sub">Departs ${esc(t.departure_date_time || '?')} · ${types.reduce((a, x) => a + x.total, 0)} seats total</div>
        <div class="bsm-chips">${types.map(x => chipHTML(x, idx, num)).join('') || '<span class="bsm-dim">no seat data</span>'}</div>
      </div>`;
    });
    h += '<div class="bsm-legend"><b>Buy tickets ↗</b> jumps to the site\'s booking page for that train (fullest class preselected). Click a class chip to buy that exact class; click the card body to load the train\'s full route here instead.</div>';
    $('out').innerHTML = h;
    CARDS = trains;
  }

async function chooseTrain(t) {
    const num = trainNoOf(t.trip_number);
    if (!num) { setStatus('Could not read a train number from "' + (t.trip_number || '?') + '". Enter it manually in By train mode.'); return; }
    showMode('train');
    setBusy(true);
    try {
      $('train').value = num;
      reset();
      await loadRoute();
      // Snap From/To selects to the searched stations.
      const fi = R.stops.findIndex(s => s.toLowerCase() === searched.from.toLowerCase());
      const ti = R.stops.findIndex(s => s.toLowerCase() === searched.to.toLowerCase());
      if (fi >= 0 && ti > fi) {
        // You searched with your boarding day; convert to the train's first-station day.
        const firstDay = addDays(searched.date, -R.offs[fi]);
        if (firstDay !== R.date) {
          $('date').value = firstDay;
          await loadRoute();
        }
        $('from').value = fi; $('to').value = ti;
        setStatus(`${R.name}: route loaded, From/To set to ${searched.from} → ${searched.to}. Scan matrix when ready.`);
      } else {
        setStatus(`${R.name}: route loaded, but I couldn't match "${fi < 0 ? searched.from : searched.to}" in its stop list. Pick From/To manually, then Scan matrix.`);
      }
    } catch (e) {
      setStatus('Error: ' + e.message);
    } finally {
      setBusy(false);
    }
  }

// ---- wiring ----
  $('load').onclick = async () => {
    setBusy(true);
    try { await loadRoute(); } catch (e) { setStatus('Error: ' + e.message); }
    finally { setBusy(false); }
  };
  $('scan').onclick = () => scanMatrix(false);
  $('rescan').onclick = () => scanMatrix(true);
  $('last').onclick = recallLastScan;
  $('find').onclick = async () => {
    $('find').disabled = true;
    try { await findTrains(); } catch (e) { setStatus('Error: ' + e.message); }
    finally { $('find').disabled = false; }
  };

  // ---- Autopilot (Buy-next landing tab, bsm_autosearch=1) ----
  // Rewritten on the site's real DOM (per imtiajsinamm/Bangladesh-railway-seat-assistant):
  //   results page = train cards "NAME (123)" with per-class tiles each ending in BOOK NOW;
  //   seat map = "Select Coach" dropdown with options like "UMA - 16 Seat(s)".
  // Flow: (results already shown by the deep link) → click OUR train+class BOOK NOW
  //       → switch the coach dropdown to the coach with the most seats. STOPS there.
  (async () => {
    if (!urlParam('bsm_autosearch')) return;
    const DEBUG = urlParam('bsm_debug') === '1';
    const log = (...a) => console.info('[BR Seat Matrix]', ...a);
    const trainNo = urlParam('bsm_train');
    const cls = urlParam('class');
    if (location.pathname.includes('/login')) { log('login page — log in, then re-run Buy next.'); return; }
    if (!trainNo) { log('no bsm_train param — nothing to automate.'); return; }

// ---- dom helpers (from the RSA approach, adapted) ----
    const norm = s => (s || '').replace(/\s+/g, ' ').trim().toLowerCase();
    const getOwnText = el => { let t = ''; for (const c of el.childNodes) if (c.nodeType === Node.TEXT_NODE) t += c.textContent; return t.trim(); };
    const leafText = el => {
      const own = getOwnText(el); if (own) return own;
      const full = el.textContent.trim();
      return (el.children.length === 1 && full.length && full.length <= 80) ? full : '';
    };
    const visible = el => {
      if (!el || typeof el.getBoundingClientRect !== 'function') return false;
      const r = el.getBoundingClientRect(); if (!r.width && !r.height) return false;
      const s = getComputedStyle(el); return s.visibility !== 'hidden' && s.display !== 'none';
    };
    const fireClick = el => {
      if (!el) return;
      el.scrollIntoView({ block: 'center', behavior: 'instant' });
      el.dispatchEvent(new MouseEvent('mousedown', { bubbles: true }));
      el.dispatchEvent(new MouseEvent('mouseup', { bubbles: true }));
      el.click();
    };
    const waitUntil = async (fn, ms, step = 250) => {
      const end = Date.now() + ms;
      while (Date.now() < end) {
        try { const v = await fn(); if (v) return v; } catch {}
        await sleep(step);
      }
      return null;
    };

// ---- results-page token scan: heading / class / booknow, in document order ----
    const HEADING_RE = /^[^()]*\(\d{1,4}\)\s*$/;
    const CLASS_CODE_RE = /^[A-Z][A-Z_]{1,9}$/;
    function scanTokens() {
      const tokens = [];
      const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_ELEMENT);
      let node = walker.currentNode;
      while (node) {
        if (!['SCRIPT', 'STYLE', 'OPTION', 'SELECT'].includes(node.tagName)) {
          const text = leafText(node).replace(/\s+/g, ' ').trim();
          if (text && text.length <= 90) {
            let kind = null;
            if (norm(text) === 'book now') kind = 'booknow';
            else if (HEADING_RE.test(text) && /[A-Za-z]/.test(text)) kind = 'heading';
            else {
              const word = text.split(/\s+/)[0];
              if (CLASS_CODE_RE.test(word) && (word.includes('_') || word === 'SHOVAN' || word === 'SNIGDHA')) kind = 'class';
            }
            if (kind && visible(node)) tokens.push({ kind, el: node, text });
          }
        }
        node = walker.nextNode();
      }
      return tokens.filter((t, i) => {         // wrapper + child often share text: keep the deepest
        const n = tokens[i + 1];
        return !(n && n.kind === t.kind && n.text === t.text && t.el.contains(n.el));
      });
    }
    function findBookNow() {
      const tokens = scanTokens();
      const start = tokens.findIndex(t => t.kind === 'heading' && t.text.includes('(' + trainNo + ')'));
      if (start === -1) {
        const shown = tokens.filter(t => t.kind === 'heading').map(t => t.text).join(' | ') || 'none';
        return { ok: false, reason: `train (${trainNo}) not on the results page. Shown: ${shown}` };
      }
      let end = tokens.length;
      for (let i = start + 1; i < tokens.length; i++) if (tokens[i].kind === 'heading') { end = i; break; }
      const region = tokens.slice(start + 1, end);
      const classIdx = cls ? region.findIndex(t => t.kind === 'class' && t.text.split(/\s+/)[0] === cls) : -1;
      if (cls && classIdx === -1) {
        const offered = region.filter(t => t.kind === 'class').map(t => t.text.split(/\s+/)[0]).join(', ') || 'none';
        return { ok: false, reason: `class ${cls} not offered for (${trainNo}). Offered: ${offered}` };
      }
      const book = (classIdx >= 0 ? region.slice(classIdx + 1) : region).find(t => t.kind === 'booknow');
      if (!book) return { ok: false, reason: `no BOOK NOW found for (${trainNo})${cls ? ' ' + cls : ''}.` };
      const clickable = book.el.closest("button, a, [role='button']") || book.el;
      if (clickable.disabled || clickable.getAttribute('aria-disabled') === 'true')
        return { ok: false, reason: `BOOK NOW for (${trainNo}) ${cls} is disabled (sold out?).` };
      return { ok: true, el: clickable };
    }

// ---- Phase 0: if the results page isn't up yet, press Search Trains ----
    let found = await waitUntil(() => scanTokens().some(t => t.kind === 'booknow') ? true : null, 20000);
    if (!found) {
      const btn = [...document.querySelectorAll("button, [role='button'], input[type='submit']")]
        .find(b => visible(b) && norm(b.textContent || b.value).includes('search'));
      if (!btn) { log('phase 0: no results and no Search button — check the tab manually.'); return; }
      fireClick(btn);
      log('phase 0: clicked Search Trains.');
    } else log('phase 0: results already shown.');

// ---- Phase 1: BOOK NOW on OUR train + class tile ----
    const hit = await waitUntil(() => { const r = findBookNow(); return r.ok ? r : null; }, 30000)
      || (scanTokens().length ? findBookNow() : { ok: false, reason: 'timed out' });   // final attempt keeps the precise reason
    if (!hit.ok) { log('phase 1 ✗:', hit.reason); return; }
    fireClick(hit.el);
    log(`phase 1 ✓: clicked BOOK NOW for (${trainNo})${cls ? ' ' + cls : ''}.`);

// ---- Phase 2: coach with the most seats (the "Select Coach" dropdown) ----
    const coachSelect = await waitUntil(() => {
      const sels = [...document.querySelectorAll('select')];
      return sels.find(s => visible(s) && /seat\(s\)/i.test(s.textContent)) || null;
    }, 20000);
    if (!coachSelect) { log('phase 2 ✗: seat map / coach dropdown did not appear (class sold out?).'); return; }
    const opts = [...coachSelect.options].filter(o => o.value && !/^\s*(select|choose)/i.test(o.textContent));
    let bestOpt = null, bestSeats = -1;
    for (const o of opts) {
      const m = /([A-Z]{1,5})\s*-\s*(\d+)\s*Seat/i.exec(o.textContent);
      if (m && +m[2] > bestSeats) { bestSeats = +m[2]; bestOpt = o; }
    }
    if (!bestOpt) { log('phase 2 ✗: could not read seat counts from coach options: ' + opts.map(o => o.textContent).join(' | ')); return; }
    coachSelect.value = bestOpt.value;
    coachSelect.dispatchEvent(new Event('input', { bubbles: true }));
    coachSelect.dispatchEvent(new Event('change', { bubbles: true }));
    log(`phase 2 ✓: switched to coach ${bestOpt.textContent.trim()} (most seats). Pick your seats and pay — I stop here.`);
  })();
})();