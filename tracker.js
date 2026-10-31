/* OSR 추적 엔진
   고정 카메라 영상에서 ① 빈 트랙 배경과 비교해 움직이는 사람 덩어리를 찾고
   ② 그 덩어리 전부를 항상 각각 추적하면서 ③ 사용자가 고른 사람·그룹을 추적들에 연결해
   그 대상이 출발선을 넘는 첫 프레임을 기록한다. 고르는 동안에도 추적은 끊기지 않는다.
   화면·브라우저와 무관한 순수 계산 코드라서 node 로도 검사할 수 있다. */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.OSRTracker = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  const BINS = 28;

  /* 색상 12칸×채도 2단 + 무채색 밝기 4칸 */
  function colorBin(r, g, b) {
    const mx = Math.max(r, g, b), mn = Math.min(r, g, b), c = mx - mn;
    const s = mx ? c / mx : 0;
    if (s < 0.22 || mx < 40) return 24 + Math.min(3, (mx / 64) | 0);
    let h;
    if (mx === r) h = ((g - b) / c + 6) % 6;
    else if (mx === g) h = (b - r) / c + 2;
    else h = (r - g) / c + 4;
    return Math.min(11, (h * 2) | 0) * 2 + (s > 0.55 ? 1 : 0);
  }

  function similarity(a, b) {
    let s = 0;
    for (let i = 0; i < BINS; i++) s += Math.min(a[i], b[i]);
    return s;
  }

  /* 영상 전체에서 뽑은 프레임들의 픽셀별 중앙값 = 사람이 지워진 빈 트랙 */
  function medianBackground(frames, w, h) {
    const n = w * h, m = frames.length, out = new Float32Array(n * 3), buf = new Uint8Array(m);
    for (let i = 0; i < n; i++) {
      for (let ch = 0; ch < 3; ch++) {
        const o = i * 4 + ch;
        for (let k = 0; k < m; k++) {
          const v = frames[k][o];
          let j = k - 1;
          while (j >= 0 && buf[j] > v) { buf[j + 1] = buf[j]; j--; }
          buf[j + 1] = v;
        }
        out[i * 3 + ch] = buf[m >> 1];
      }
    }
    return out;
  }

  function intersects(a, b) {
    return a.x0 <= b.x1 && a.x1 >= b.x0 && a.y0 <= b.y1 && a.y1 >= b.y0;
  }
  function overlapArea(a, b) {
    const w = Math.min(a.x1, b.x1) - Math.max(a.x0, b.x0) + 1;
    const h = Math.min(a.y1, b.y1) - Math.max(a.y0, b.y0) + 1;
    return w > 0 && h > 0 ? w * h : 0;
  }
  function unionBox(a, b) {
    return { x0: Math.min(a.x0, b.x0), y0: Math.min(a.y0, b.y0), x1: Math.max(a.x1, b.x1), y1: Math.max(a.y1, b.y1) };
  }
  const boxW = b => b.x1 - b.x0 + 1;
  const boxH = b => b.y1 - b.y0 + 1;
  const boxOf = c => ({ x0: c.x0, y0: c.y0, x1: c.x1, y1: c.y1 });
  const median = a => { const s = a.slice().sort((x, y) => x - y); return s.length ? s[s.length >> 1] : 0; };

  class Tracker {
    constructor(opts) {
      this.w = opts.width;
      this.h = opts.height;
      this.bg = opts.background;
      this.thr = opts.threshold || 30;
      this.minLap = opts.minLap || 12;
      this.minArea = opts.minArea || Math.max(6, Math.round(this.w * this.h * 0.00002));
      this.simMin = 0.25;      // 같은 추적으로 이어 갈 최소 색 유사도
      this.joinSim = 0.3;      // 갈라져 나온 덩어리를 원래 추적의 일부로 볼 최소 유사도
      this.splitGap = opts.splitGap || 5;   // 그룹이 나뉘었다고 볼 간격 (사람 키의 배수)
      this.reidMin = 0.5;      // 놓친 대상의 후보로 올릴 유사도
      this.reidAuto = 0.72;    // 묻지 않고 이어 갈 유사도
      const n = this.w * this.h;
      this.mask = new Uint8Array(n);
      this.labels = new Int32Array(n);
      this.parent = new Int32Array(Math.ceil(n / 2) + 2);
      this.comps = [];
      this.tracks = [];
      this.targets = [];
      this.nextTrack = 1;
      this.nextTarget = 1;
      this.rawLog = [];
      this.frame = 0;
      this.unstable = false;
      this.fgRatio = 0;
      this.line = null;
      this.data = null;
    }

    /* 출발선: 분석 픽셀 좌표. dir=1 이면 (b-a)를 왼쪽으로 돌린 방향이 진행 방향 */
    setLine(ax, ay, bx, by, dir) {
      const dx = bx - ax, dy = by - ay;
      this.line = { ax, ay, dx, dy, nx: -dy, ny: dx, len: Math.hypot(dx, dy) || 1, len2: dx * dx + dy * dy || 1, dir: dir || 1 };
    }

    /* 배경과 다른 픽셀 → 덩어리 목록 */
    segment(data, learn) {
      this.data = data;
      const { w, h, bg, thr, mask, labels, parent } = this;
      const n = w * h;
      let fg = 0;
      for (let i = 0; i < n; i++) {
        const o = i * 4, b3 = i * 3;
        const r = data[o], g = data[o + 1], b = data[o + 2];
        const br = bg[b3], bgg = bg[b3 + 1], bb = bg[b3 + 2];
        const d = Math.max(Math.abs(r - br), Math.abs(g - bgg), Math.abs(b - bb));
        let f = d > thr ? 1 : 0;
        if (f) {
          // 그림자: 배경과 색 비율은 같고 어둡기만 한 픽셀은 사람이 아니다
          const L = r + g + b, BL = br + bgg + bb;
          if (BL > 60 && L > 0) {
            const ratio = L / BL;
            if (ratio > 0.45 && ratio < 0.95 &&
                Math.abs(r / L - br / BL) < 0.03 && Math.abs(g / L - bgg / BL) < 0.03) f = 0;
          }
        }
        mask[i] = f;
        fg += f;
      }
      this.fgRatio = fg / n;
      this.unstable = this.fgRatio > 0.5;

      if (learn !== false) {
        // 해 움직임에 맞춰 배경을 천천히 갱신, 멈춰 선 물체는 아주 천천히 배경이 된다
        const aBg = this.unstable ? 0.1 : 0.005, aFg = this.unstable ? 0.1 : 0.0005;
        for (let i = 0; i < n; i++) {
          const o = i * 4, b3 = i * 3, a = mask[i] ? aFg : aBg;
          bg[b3] += a * (data[o] - bg[b3]);
          bg[b3 + 1] += a * (data[o + 1] - bg[b3 + 1]);
          bg[b3 + 2] += a * (data[o + 2] - bg[b3 + 2]);
        }
      }

      // 연결 요소 찾기 (8방향)
      let next = 1;
      const find = x => { while (parent[x] !== x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; };
      const join = (a, b) => { a = find(a); b = find(b); if (a !== b) parent[Math.max(a, b)] = Math.min(a, b); return Math.min(a, b); };
      labels.fill(0);
      for (let y = 0; y < h; y++) {
        for (let x = 0; x < w; x++) {
          const i = y * w + x;
          if (!mask[i]) continue;
          let l = 0;
          if (x > 0 && labels[i - 1]) l = labels[i - 1];
          if (y > 0) {
            if (x > 0 && labels[i - w - 1]) l = l ? join(l, labels[i - w - 1]) : labels[i - w - 1];
            if (labels[i - w]) l = l ? join(l, labels[i - w]) : labels[i - w];
            if (x < w - 1 && labels[i - w + 1]) l = l ? join(l, labels[i - w + 1]) : labels[i - w + 1];
          }
          if (!l) {
            if (next >= parent.length) continue;
            l = next++;
            parent[l] = l;
          }
          labels[i] = l;
        }
      }
      const stats = new Map();
      for (let y = 0; y < h; y++) {
        for (let x = 0; x < w; x++) {
          const i = y * w + x;
          if (!labels[i]) continue;
          const r = find(labels[i]);
          labels[i] = r;
          let c = stats.get(r);
          if (!c) { c = { id: r, x0: x, y0: y, x1: x, y1: y, area: 0, sx: 0, sy: 0, hist: null }; stats.set(r, c); }
          if (x < c.x0) c.x0 = x;
          if (x > c.x1) c.x1 = x;
          if (y < c.y0) c.y0 = y;
          if (y > c.y1) c.y1 = y;
          c.area++; c.sx += x; c.sy += y;
        }
      }
      this.comps = [];
      for (const c of stats.values()) {
        if (c.area >= this.minArea) {
          c.cx = c.sx / c.area; c.cy = c.sy / c.area;
          this.comps.push(c);
        }
      }
      return this.comps;
    }

    compHist(c) {
      if (c.hist) return c.hist;
      const hist = new Float32Array(BINS), { w, labels, data } = this;
      for (let y = c.y0; y <= c.y1; y++) {
        for (let x = c.x0; x <= c.x1; x++) {
          const i = y * w + x;
          if (labels[i] !== c.id) continue;
          hist[colorBin(data[i * 4], data[i * 4 + 1], data[i * 4 + 2])]++;
        }
      }
      for (let k = 0; k < BINS; k++) hist[k] /= c.area;
      c.hist = hist;
      return hist;
    }

    mergedHist(list) {
      const hist = new Float32Array(BINS);
      let area = 0;
      for (const c of list) {
        const h = this.compHist(c);
        for (let k = 0; k < BINS; k++) hist[k] += h[k] * c.area;
        area += c.area;
      }
      for (let k = 0; k < BINS; k++) hist[k] /= area || 1;
      return hist;
    }

    /* 헬멧(위 20%)·상의(20~55%)·하의(55~100%)를 따로 본 색 분포. 전체 트랙 화면에서 아이를 구분하는 단서 */
    zoneHists(list) {
      const { w, labels, data } = this;
      let box = boxOf(list[0]);
      for (const c of list) box = unionBox(box, c);
      const ids = new Set(list.map(c => c.id)), H = boxH(box);
      const zones = [new Float32Array(BINS), new Float32Array(BINS), new Float32Array(BINS)], counts = [0, 0, 0];
      for (let y = box.y0; y <= box.y1; y++) {
        const f = (y - box.y0) / H, z = f < 0.2 ? 0 : f < 0.55 ? 1 : 2;
        for (let x = box.x0; x <= box.x1; x++) {
          const i = y * w + x;
          if (!ids.has(labels[i])) continue;
          zones[z][colorBin(data[i * 4], data[i * 4 + 1], data[i * 4 + 2])]++;
          counts[z]++;
        }
      }
      zones.forEach((zh, z) => { for (let k = 0; k < BINS; k++) zh[k] /= counts[z] || 1; });
      return zones;
    }

    _zoneSim(a, b) {
      return 0.3 * similarity(a[0], b[0]) + 0.4 * similarity(a[1], b[1]) + 0.3 * similarity(a[2], b[2]);
    }

    /* 추적 하나가 대상과 얼마나 닮았나. 사람은 부위별 색까지 본다 */
    identitySim(T, tr) {
      const sim = similarity(tr.hist, T.hist);
      if (T.type !== 'person' || !T.zones || !tr.zones) return sim;
      return 0.4 * sim + 0.6 * this._zoneSim(tr.zones, T.zones);
    }

    /* 여러 명이 붙은 덩어리 안에서 추적의 옷 색에 맞는 픽셀 쪽으로 창을 옮긴다 */
    _meanShift(tr, pred, list) {
      const { w, h, labels, data } = this;
      const ids = new Set(list.map(c => c.id));
      let cx = (pred.x0 + pred.x1) / 2, cy = (pred.y0 + pred.y1) / 2, weight = 0;
      const hw = tr.refW / 2 + 2, hh = tr.refH / 2 + 2;
      for (let it = 0; it < 4; it++) {
        let sx = 0, sy = 0, sw = 0;
        const x0 = Math.max(0, Math.floor(cx - hw)), x1 = Math.min(w - 1, Math.ceil(cx + hw));
        const y0 = Math.max(0, Math.floor(cy - hh)), y1 = Math.min(h - 1, Math.ceil(cy + hh));
        for (let y = y0; y <= y1; y++) {
          for (let x = x0; x <= x1; x++) {
            const i = y * w + x;
            if (!ids.has(labels[i])) continue;
            const v = tr.hist[colorBin(data[i * 4], data[i * 4 + 1], data[i * 4 + 2])];
            if (v < 0.04) continue;
            sx += x * v; sy += y * v; sw += v;
          }
        }
        if (sw <= 0) { weight = 0; break; }
        const nx = sx / sw, ny = sy / sw, moved = Math.hypot(nx - cx, ny - cy);
        cx = nx; cy = ny; weight = sw;
        if (moved < 0.5) break;
      }
      return { cx, cy, weight, box: { x0: cx - hw, y0: cy - hh, x1: cx + hw, y1: cy + hh } };
    }

    /* 픽셀 중 출발선을 넘어간 것이 있는지 */
    _isPast(tr, list, clip, byColor) {
      const L = this.line;
      if (!L) return false;
      const maxDist = Math.max(30, Math.hypot(tr.vx, tr.vy) * (tr.dt || 1 / 30) * 3) * L.len;
      const { w, labels } = this;
      const ids = new Set(list.map(c => c.id)), d = this.data;
      for (const c of list) {
        const x0 = clip ? Math.max(c.x0, Math.floor(clip.x0)) : c.x0, x1 = clip ? Math.min(c.x1, Math.ceil(clip.x1)) : c.x1;
        const y0 = clip ? Math.max(c.y0, Math.floor(clip.y0)) : c.y0, y1 = clip ? Math.min(c.y1, Math.ceil(clip.y1)) : c.y1;
        for (let y = y0; y <= y1; y++) {
          for (let x = x0; x <= x1; x++) {
            const i = y * w + x;
            if (!ids.has(labels[i])) continue;
            if (byColor && tr.hist[colorBin(d[i * 4], d[i * 4 + 1], d[i * 4 + 2])] < 0.04) continue;
            const px = x - L.ax, py = y - L.ay;
            const s = (px * L.nx + py * L.ny) * L.dir;
            if (s <= 0 || s > maxDist) continue;
            const u = (px * L.dx + py * L.dy) / L.len2;
            if (u >= -0.03 && u <= 1.03) return true;
          }
        }
      }
      return false;
    }

    _spawn(list, t, parent) {
      let box = boxOf(list[0]), area = 0, sx = 0, sy = 0;
      for (const c of list) { box = unionBox(box, c); area += c.area; sx += c.sx; sy += c.sy; }
      const tr = {
        id: this.nextTrack++, box, cx: sx / area, cy: sy / area, vx: 0, vy: 0,
        hist: this.mergedHist(list).slice(), zones: this.zoneHists(list),
        refW: boxW(box), refH: boxH(box), refArea: area, area,
        bornT: t, seenT: t, lastT: t, seenFrames: 1, moved: 0, mergedT: -1e9, past: false, raw: [], parent: parent || null, dead: false, dt: 1 / 30
      };
      tr.past = this._isPast(tr, list, null, false);
      this.tracks.push(tr);
      return tr;
    }

    /* 모든 덩어리를 모든 추적에 연결 */
    _updateTracks(t) {
      const tracks = this.tracks, comps = this.comps;
      for (const tr of tracks) {
        const dt = Math.max(1 / 240, Math.min(1, t - tr.lastT));
        tr.dt = dt; tr.lastT = t;
        const ox = tr.vx * dt, oy = tr.vy * dt;
        tr.pred = { x0: tr.box.x0 + ox, y0: tr.box.y0 + oy, x1: tr.box.x1 + ox, y1: tr.box.y1 + oy };
        tr.pcx = tr.cx + ox; tr.pcy = tr.cy + oy;
        tr.used = []; tr.shared = []; tr.usedBox = null;
      }
      // 각 덩어리 후보 계산
      const pairs = [];
      for (const c of comps) {
        c.owner = null;
        const hist = this.compHist(c);
        const near = [];
        for (const tr of tracks) {
          const R = Math.max(Math.max(tr.refW, tr.refH) * 0.8, 16) + Math.hypot(tr.vx, tr.vy) * tr.dt * 0.5;
          const dist = Math.hypot(c.cx - tr.pcx, c.cy - tr.pcy);
          const ov = overlapArea(c, tr.pred);
          if (dist > R + Math.max(boxW(c), boxH(c)) * 0.5 && !ov) continue;
          const sim = similarity(hist, tr.hist);
          const inside = ov >= c.area * 0.8;
          if (sim < this.simMin && !(inside && sim >= 0.1)) continue;
          const predArea = boxW(tr.pred) * boxH(tr.pred);
          near.push({ tr, sim, dist, ovFrac: ov / predArea });
          pairs.push({ c, tr, cost: dist / R + 2 * (1 - sim) - Math.min(1, ov / predArea) });
        }
        // 두 추적의 예상 위치를 동시에 덮으면 여러 명이 붙은 덩어리
        const covering = near.filter(k => k.ovFrac >= 0.3 && t - k.tr.bornT > 0.1);
        c.coverN = covering.length;
        if (covering.length >= 2) {
          c.isShared = true;
          for (const k of covering) k.tr.shared.push(c);
        }
      }
      pairs.sort((a, b) => a.cost - b.cost);
      for (const { c, tr } of pairs) {
        if (c.owner || c.isShared) continue;
        const u = tr.usedBox ? unionBox(tr.usedBox, c) : boxOf(c);
        const limW = tr.refW * 1.6 + 8, limH = tr.refH * 1.6 + 8;
        if (boxW(u) > limW || boxH(u) > limH) {
          if (tr.usedBox) continue;
          if (c.coverN >= 2) { tr.shared.push(c); c.owner = tr; continue; }
          // 다른 추적과 겹치지 않는데 크다 = 화면 가장자리에서 들어오던 몸 전체가 보이기 시작한 것
          tr.grow = true;
        }
        tr.usedBox = u; tr.used.push(c); c.owner = tr;
      }
      const born = [];
      // 추적 갱신
      for (const tr of tracks) {
        if (tr.used.length) {
          let area = 0, sx = 0, sy = 0;
          for (const c of tr.used) { area += c.area; sx += c.sx; sy += c.sy; }
          const nx = sx / area, ny = sy / area;
          const vx = (nx - tr.cx) / tr.dt, vy = (ny - tr.cy) / tr.dt;
          const a = tr.seenFrames < 2 ? 1 : 0.4;
          tr.vx += a * (vx - tr.vx); tr.vy += a * (vy - tr.vy);
          tr.moved += Math.hypot(nx - tr.cx, ny - tr.cy);
          tr.cx = nx; tr.cy = ny; tr.box = tr.usedBox; tr.area = area;
          // 옆 사람이 붙어 덩어리가 커졌을 때는 색 기억을 오염시키지 않는다
          const clean = area <= tr.refArea * 1.25;
          if (clean) {
            const cur = this.mergedHist(tr.used);
            for (let k = 0; k < BINS; k++) tr.hist[k] = tr.hist[k] * 0.97 + cur[k] * 0.03;
          } else tr.mergedT = t;
          const rate = tr.grow ? 0.3 : boxW(tr.box) * boxH(tr.box) < tr.refW * tr.refH ? 0.06 : 0.02;
          tr.grow = false;
          tr.refW += (boxW(tr.box) - tr.refW) * rate;
          tr.refH += (boxH(tr.box) - tr.refH) * rate;
          tr.refArea += (area - tr.refArea) * rate;
          if (clean && this.frame % 5 === 0) tr.zones = this.zoneHists(tr.used);
          tr.seenT = t; tr.seenFrames++;
          tr.nowPast = this._isPast(tr, tr.used, null, false);
        } else if (tr.shared.length) {
          const ms = this._meanShift(tr, tr.pred, tr.shared);
          tr.mergedT = t;
          if (ms.weight > tr.refArea * 0.01) {
            tr.vx += 0.2 * ((ms.cx - tr.cx) / tr.dt - tr.vx);
            tr.vy += 0.2 * ((ms.cy - tr.cy) / tr.dt - tr.vy);
            tr.moved += Math.hypot(ms.cx - tr.cx, ms.cy - tr.cy);
            tr.cx = ms.cx; tr.cy = ms.cy; tr.box = ms.box;
            tr.seenT = t; tr.seenFrames++;
          } else {
            tr.box = tr.pred; tr.cx = tr.pcx; tr.cy = tr.pcy;
          }
          tr.nowPast = this._isPast(tr, tr.shared, tr.box, true);
        } else {
          tr.box = tr.pred; tr.cx = tr.pcx; tr.cy = tr.pcy;
          const limit = tr.seenFrames < 6 ? 0.25 : 1.5;
          if (t - tr.seenT > limit) tr.dead = true;
          tr.nowPast = tr.past;
        }
        if (tr.nowPast && !tr.past) {
          const L = this.line;
          const along = L ? (tr.vx * L.nx + tr.vy * L.ny) * L.dir / L.len : 0;
          const lastRaw = tr.raw[tr.raw.length - 1];
          if (along > 5 && (!lastRaw || t - lastRaw.t > 3)) {
            tr.raw.push({ t, merged: t - tr.mergedT < 0.5 });
            this.rawLog.push({ id: tr.id, t, merged: t - tr.mergedT < 0.5 });
          }
        }
        tr.past = tr.nowPast;
      }
      // 주인 없는 덩어리는 새 추적. 기존 추적에서 갈라진 것이면 부모를 기억
      for (const c of comps) {
        if (c.owner || c.isShared) continue;
        let parent = null, bestD = 1e9;
        for (const tr of tracks) {
          if (tr.dead) continue;
          const d = Math.hypot(c.cx - tr.cx, c.cy - tr.cy);
          if (d < Math.max(tr.refW, tr.refH) * 1.5 + 6 && d < bestD && similarity(this.compHist(c), tr.hist) >= this.joinSim) { bestD = d; parent = tr; }
        }
        born.push(this._spawn([c], t, parent));
      }
      this.tracks = this.tracks.filter(tr => !tr.dead);
      this.bornNow = born;
    }

    /* 화면 멈춤용: 지금 보이는 추적 목록 */
    snapshot() {
      return this.tracks.filter(tr => tr.seenFrames >= 3 && this.lastT - tr.seenT < 0.3)
        .map(tr => ({ id: tr.id, x0: tr.box.x0, y0: tr.box.y0, x1: tr.box.x1, y1: tr.box.y1, cx: tr.cx, cy: tr.cy,
          hist: tr.hist.slice(), zones: tr.zones, area: tr.area, refH: tr.refH }));
    }

    _makeTarget(members, name, type, fromT) {
      const hist = new Float32Array(BINS);
      let area = 0;
      for (const m of members) { for (let k = 0; k < BINS; k++) hist[k] += m.hist[k] * m.area; area += m.area; }
      for (let k = 0; k < BINS; k++) hist[k] /= area || 1;
      const T = {
        id: this.nextTarget++, name, type, members: new Set(members.map(m => m.id)), hist,
        zones: type === 'person' && members[0] ? members[0].zones : null,
        crossings: [], status: members.length ? 'tracking' : 'lost', lostT: members.length ? null : fromT, area: area || 1,
        fromT, seenRaw: new Set(), ignoreUntil: -1e9, pending: null, reacquired: false,
        refArea: members.length ? area / members.length : 1,
        sigs: members.map(m => m.zones), joinCount: new Map(), swapT: -1e9, ever: new Set(members.map(m => m.id)),
        splitSince: null, parent: null, mergeSince: null, splits: []
      };
      this.targets.push(T);
      return T;
    }

    /* 멈춘 화면에서 고른 추적들을 사람·그룹으로 등록. fromT 이후의 통과 기록은 소급 적용 */
    addTarget(ids, name, type, fromT, snap) {
      if (!ids.length) return null;
      const members = this.tracks.filter(tr => ids.includes(tr.id));
      // 고르는 사이 추적이 끝났어도 멈춘 순간의 색 기억으로 다시 찾을 수 있게 한다
      const picked = snap ? snap.filter(k => ids.includes(k.id)) : members;
      const T = this._makeTarget(members, name, type, fromT);
      if (picked.length) {
        const hist = new Float32Array(BINS);
        let area = 0;
        for (const m of picked) { for (let k = 0; k < BINS; k++) hist[k] += m.hist[k] * m.area; area += m.area; }
        for (let k = 0; k < BINS; k++) hist[k] /= area || 1;
        T.hist = hist; T.area = area || 1; T.refArea = (area || 1) / picked.length;
        T.zones = type === 'person' ? picked[0].zones : null;
        T.sigs = picked.map(m => m.zones);
      }
      // 고르는 동안 이미 지나간 통과도 소급 적용
      const idSet = new Set(ids);
      for (const r of this.rawLog) {
        if (!idSet.has(r.id) || r.t < fromT) continue;
        const key = r.id + ':' + r.t;
        const last = T.crossings[T.crossings.length - 1];
        T.seenRaw.add(key);
        if (!last || r.t - last.t >= this.minLap) T.crossings.push({ t: r.t, flags: r.merged ? ['merged'] : [] });
      }
      this._collectCross(T);
      return T;
    }

    /* 측정 시작: 그때까지의 기록은 지운다 */
    startMeasure(t) {
      for (const T of this.targets) { T.crossings = []; T.fromT = t; T.seenRaw = new Set(); T.splits = []; }
    }

    _collectCross(T, events) {
      const raws = [];
      for (const tr of this.tracks) {
        if (!T.members.has(tr.id)) continue;
        for (const r of tr.raw) {
          const key = tr.id + ':' + r.t;
          if (r.t >= T.fromT && !T.seenRaw.has(key)) { raws.push({ key, ...r }); }
        }
      }
      raws.sort((a, b) => a.t - b.t);
      for (const r of raws) {
        T.seenRaw.add(r.key);
        const last = T.crossings[T.crossings.length - 1];
        if (last && r.t - last.t < this.minLap) continue;
        const flags = [];
        if (r.merged) flags.push('merged');
        if (T.reacquired) flags.push('reid');
        if (r.t - T.swapT < 3) flags.push('swap');
        const rec = { t: r.t, flags };
        T.crossings.push(rec);
        T.reacquired = false;
        if (events) events.push({ type: 'cross', target: T, t: r.t, flags });
      }
    }

    _updateTargets(t, events) {
      const owned = new Set();
      for (const T of this.targets) for (const id of T.members) owned.add(id);
      for (const T of this.targets.slice()) {
        if (T.status === 'merged') continue;
        const live = this.tracks.filter(tr => T.members.has(tr.id));
        // 사라진 추적은 구성원에서 뺀다
        T.members = new Set(live.map(tr => tr.id));
        // 겹쳐 있던 덩어리에서 갈라져 나온 추적
        for (const b of this.bornNow || []) {
          if (!b.parent || !T.members.has(b.parent.id)) continue;
          if (T.type === 'group') { T.members.add(b.id); live.push(b); owned.add(b.id); }
          else if (this.identitySim(T, b) > this.identitySim(T, b.parent) + 0.1) {
            // 사람 대상: 갈라진 쪽이 더 닮았으면 그쪽으로 옮긴다
            T.members = new Set([b.id]); live.length = 0; live.push(b); owned.add(b.id);
          }
        }
        if (this.frame % 5 === 0) this._checkIdentity(T, live, t);
        if (this.frame % 10 === 0 && T.type === 'group') this._checkSplit(T, live, t, events);
        if (this.frame % 10 === 0 && T.parent) this._checkRejoin(T, live, t, events);
        if (T.status === 'merged') continue;
        for (const id of T.members) T.ever.add(id);
        this._collectCross(T, events);
        const anySeen = live.some(m => t - m.seenT < 1);
        if (T.status === 'tracking' && !anySeen) {
          T.status = 'lost'; T.lostT = t; T.members = new Set();
          events.push({ type: 'lost', target: T, t });
        } else if (T.status === 'lost') {
          this._reacquire(T, t, events, owned);
        }
      }
    }

    /* 그룹이 사람 키의 splitGap 배 이상 벌어진 상태가 3초 이어지면 앞 무리와 뒤 무리로 나눈다 */
    _clusters(list) {
      const gap = this.splitGap * median(list.map(m => m.refH));
      const groups = [], left = list.slice();
      while (left.length) {
        const cur = [left.pop()];
        for (let i = 0; i < cur.length; i++) {
          for (let k = left.length - 1; k >= 0; k--) {
            if (Math.hypot(left[k].cx - cur[i].cx, left[k].cy - cur[i].cy) <= gap) cur.push(left.splice(k, 1)[0]);
          }
        }
        groups.push(cur);
      }
      return groups;
    }

    _checkSplit(T, live, t, events) {
      const seen = live.filter(m => t - m.seenT < 0.5);
      if (seen.length < 2) { T.splitSince = null; return; }
      const groups = this._clusters(seen);
      if (groups.length < 2) { T.splitSince = null; return; }
      if (T.splitSince === null) { T.splitSince = t; return; }
      if (t - T.splitSince < 3) return;
      T.splitSince = null;
      const vx = median(seen.map(m => m.vx)), vy = median(seen.map(m => m.vy));
      const front = c => c.reduce((a, m) => a + m.cx * vx + m.cy * vy, 0) / c.length;
      // 원래 이름은 가장 큰 무리가 잇는다. 추월하던 다른 아이가 잠깐 섞여 앞서가도 그룹을 빼앗지 못한다
      groups.sort((a, b) => (b.length - a.length) || (front(b) - front(a)));
      T.members = new Set(groups[0].map(m => m.id));
      const root = T.root || T;
      for (const g of groups.slice(1)) {
        root.childCount = (root.childCount || 1) + 1;
        const C = this._makeTarget(g, root.name + '-' + root.childCount, g.length === 1 ? 'person' : 'group', T.fromT);
        C.parent = T; C.root = root;
        // 분리 전 기록도 이 무리 자신이 선을 넘은 시각으로 고쳐 물려받는다
        const own = g.flatMap(m => m.raw.map(r => r.t)).sort((x, y) => x - y);
        C.crossings = T.crossings.map(c => {
          const mine = own.find(x => x >= c.t && x < c.t + this.minLap * 0.5);
          return mine === undefined ? { t: c.t, flags: c.flags.concat('inherit'), wall: c.wall }
            : { t: mine, flags: c.flags.slice(), wall: c.wall === undefined ? undefined : c.wall + (mine - c.t) * 1000 };
        });
        C.seenRaw = new Set(T.seenRaw);
        for (const id of T.ever) C.ever.add(id);
        C.splitLap = Math.max(0, T.crossings.length - 1);
        C.splitT = t;
        for (const m of g) T.ever.add(m.id);
        T.splits.push({ t, lap: C.splitLap, name: C.name });
        events.push({ type: 'split', target: T, child: C, t });
      }
    }

    /* 뒤 무리가 다시 붙어 4초 이상 함께 달리면 합친다 */
    _checkRejoin(T, live, t, events) {
      const P = T.parent;
      if (!P || P.status === 'merged' || !live.length) { T.mergeSince = null; return; }
      const others = this.tracks.filter(tr => P.members.has(tr.id));
      if (!others.length) { T.mergeSince = null; return; }
      const gap = this.splitGap * median(live.concat(others).map(m => m.refH));
      const close = live.some(a => others.some(b => Math.hypot(a.cx - b.cx, a.cy - b.cy) <= gap * 0.7));
      if (!close) { T.mergeSince = null; return; }
      if (T.mergeSince === null) { T.mergeSince = t; return; }
      if (t - T.mergeSince < 4) return;
      for (const m of live) { P.members.add(m.id); P.ever.add(m.id); }
      T.members = new Set(); T.status = 'merged'; T.mergedT = t;
      events.push({ type: 'rejoin', target: P, child: T, t });
    }

    /* 그 통과 전후 0.7초 안에 대상이 아닌 사람도 출발선을 지났으면 눈으로 확인할 기록이다 */
    isNearOther(T, t) {
      return this.rawLog.some(r => Math.abs(r.t - t) <= 0.7 && !T.ever.has(r.id));
    }

    /* 고른 순간의 헬멧·상의·하의 색과 비교 */
    _sigScore(T, tr) {
      let best = 0;
      for (const s of T.sigs) if (s && tr.zones) best = Math.max(best, this._zoneSim(tr.zones, s));
      return best;
    }

    /* 추월·겹침 뒤 대상이 다른 아이로 바뀌었는지 옷 색으로 확인하고 바로잡는다 */
    _checkIdentity(T, live, t) {
      if (T.type === 'person') {
        const cur = live[0];
        if (!cur || t - cur.seenT > 0.2) return;
        const curSim = this._sigScore(T, cur);
        if (curSim >= 0.75) return;
        const reach = 60 + Math.hypot(cur.vx, cur.vy) * 0.5;
        let best = null, bestSim = curSim + 0.15;
        for (const tr of this.tracks) {
          if (tr === cur || tr.seenFrames < 3 || t - tr.seenT > 0.2) continue;
          if (Math.hypot(tr.cx - cur.cx, tr.cy - cur.cy) > reach) continue;
          const sim = this._sigScore(T, tr);
          if (sim > bestSim) { best = tr; bestSim = sim; }
        }
        if (best) { T.members = new Set([best.id]); T.swapT = t; }
        return;
      }
      // 그룹은 옷이 아니라 함께 달리는지로 판단: 가까이에서 같은 속도로 달리는 추적은 합류
      if (!live.length) return;
      const owned = new Set();
      for (const O of this.targets) if (O !== T) for (const id of O.members) owned.add(id);
      const mvx = median(live.map(m => m.vx)), mvy = median(live.map(m => m.vy)), speed = Math.hypot(mvx, mvy);
      for (const tr of this.tracks) {
        if (T.members.has(tr.id) || owned.has(tr.id) || tr.seenFrames < 5 || t - tr.seenT > 0.2) continue;
        const reach = this.splitGap * 0.6 * tr.refH;
        const near = live.some(m => Math.hypot(tr.cx - m.cx, tr.cy - m.cy) < reach);
        const same = near && speed > 10 && Math.hypot(tr.vx - mvx, tr.vy - mvy) < speed * 0.08;
        if (!same) { T.joinCount.delete(tr.id); continue; }
        const n = (T.joinCount.get(tr.id) || 0) + 1;
        if (n >= 12) { T.members.add(tr.id); T.joinCount.delete(tr.id); }
        else T.joinCount.set(tr.id, n);
      }
    }

    /* 놓친 대상을 옷 색과 최소 랩 시간으로 다시 찾는다 */
    _reacquire(T, t, events, owned) {
      if (t < T.ignoreUntil) return;
      const last = T.crossings[T.crossings.length - 1];
      if (last && t - last.t < this.minLap * 0.6) return;
      const seeds = [];
      for (const tr of this.tracks) {
        if (owned.has(tr.id) || tr.seenFrames < 3 || tr.moved < 3 || t - tr.seenT > 0.2) continue;
        if (T.type === 'person' && tr.area > T.refArea * 3) continue;
        if (tr.area < T.refArea * 0.2) continue;
        const sim = this.identitySim(T, tr);
        if (sim >= this.reidMin) seeds.push({ tr, sim });
      }
      if (!seeds.length) return;
      seeds.sort((a, b) => b.sim - a.sim);
      const best = seeds[0];
      const list = [best.tr];
      if (T.type === 'group') {
        const reach = this.splitGap * best.tr.refH;
        for (const s of seeds.slice(1)) if (Math.hypot(s.tr.cx - best.tr.cx, s.tr.cy - best.tr.cy) < reach) list.push(s.tr);
      }
      const others = seeds.length - list.length;
      if (T.type === 'person' && best.sim >= this.reidAuto && others === 0) this._resume(T, list, t, events);
      else {
        T.status = 'confirm';
        T.pending = list.map(m => m.id);
        events.push({ type: 'confirm', target: T, t, sim: best.sim, tracks: list });
      }
    }

    _resume(T, list, t, events) {
      T.status = 'tracking';
      T.members = new Set(list.map(m => m.id));
      T.pending = null; T.reacquired = true;
      events.push({ type: 'resumed', target: T, t });
    }

    /* 사람이 후보를 확인한 결과 */
    answer(T, yes, t) {
      if (T.status !== 'confirm') return;
      const list = this.tracks.filter(tr => (T.pending || []).includes(tr.id));
      if (yes && list.length) this._resume(T, list, t, []);
      else { T.status = 'lost'; T.pending = null; T.ignoreUntil = t + 3; }
    }

    /* 사용자가 대상을 다시 지정 */
    reselect(T, ids) {
      T.members = new Set(ids);
      T.status = 'tracking'; T.pending = null; T.reacquired = true;
    }

    step(data, t) {
      const events = [];
      this.frame++;
      this.lastT = t;
      this.segment(data, true);
      if (this.unstable) { events.push({ type: 'unstable', t }); for (const tr of this.tracks) tr.lastT = t; return events; }
      this._updateTracks(t);
      this._updateTargets(t, events);
      return events;
    }
  }

  /* 색 분포에서 가장 많은 칸의 대표색 (선택 화면 색 견본용) */
  function dominantColor(hist) {
    let b = 0;
    for (let k = 1; k < BINS; k++) if (hist[k] > hist[b]) b = k;
    if (b >= 24) { const v = [25, 95, 160, 235][b - 24]; return `rgb(${v},${v},${v})`; }
    const h = (b >> 1) * 30 + 15, sat = b & 1 ? 85 : 40;
    return `hsl(${h},${sat}%,50%)`;
  }

  return { Tracker, medianBackground, colorBin, similarity, dominantColor, BINS };
});
