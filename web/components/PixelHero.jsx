"use client";

import { useEffect, useRef } from "react";
import { rng, wordCells } from "./pixels";

/**
 * Hero canvas. The EXORCIST wordmark is made of square "spirits" that drift in from the dark and
 * settle into the letters. The pointer scatters them (they spring back) and leaves a fading trail
 * of lit grid cells; now and then a scan line sweeps the word. A sparse field of squares sits at
 * the edges, kept away from text marked `data-clear`.
 *
 * `slotRef` is an empty element that reserves the wordmark's place in the layout.
 */
export function PixelHero({ slotRef }) {
  const ref = useRef(null);

  useEffect(() => {
    const cv = ref.current;
    const host = cv.parentElement;
    const ctx = cv.getContext("2d");
    const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;
    const word = wordCells();

    let C = {};
    const readColors = () => {
      const s = getComputedStyle(cv);
      const v = (n) => s.getPropertyValue(n).trim();
      C = { ink: v("--px-ink"), accent: v("--px-accent"), dim: v("--px-dim"), field: v("--px-field"), field2: v("--px-field-2"), hot: v("--px-hot") };
    };

    // ---- layout (rebuilt on resize)
    let W = 0, H = 0, cell = 10, gap = 1, ox = 0, oy = 0;
    let spirits = []; // letter cells
    let field = []; // edge squares
    let grid = { pitch: 10, cols: 0, rows: 0, x0: 0, y0: 0, heat: new Float32Array(0) };

    function layout(first) {
      const dpr = Math.min(window.devicePixelRatio || 1, 2);
      const box = host.getBoundingClientRect();
      W = box.width;
      H = box.height;
      cv.width = Math.round(W * dpr);
      cv.height = Math.round(H * dpr);
      cv.style.width = `${W}px`;
      cv.style.height = `${H}px`;
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      const sl = slotRef.current?.getBoundingClientRect();
      const sw = sl ? sl.width : W * 0.8;
      const sh = sl ? sl.height : 160;
      cell = Math.max(4, Math.floor(Math.min(sw / word.cols, sh / word.rows)));
      gap = Math.max(1, Math.round(cell * 0.14));
      ox = Math.round((sl ? sl.left - box.left : W * 0.1) + (sw - cell * word.cols) / 2);
      oy = Math.round((sl ? sl.top - box.top : H * 0.3) + (sh - cell * word.rows) / 2);

      const r = rng(2026);
      const old = spirits;
      spirits = word.cells.map(([c, y], i) => {
        const hx = ox + c * cell, hy = oy + y * cell;
        const t = r();
        const shade = t < 0.74 ? "ink" : t < 0.93 ? "accent" : "dim";
        const prev = old[i];
        if (prev && !first) return { ...prev, hx, hy, shade };
        // start somewhere in the dark around the word, invisible
        const a = r() * Math.PI * 2, d = (0.4 + r() * 0.8) * Math.max(W, H) * 0.5;
        return { hx, hy, x: hx + Math.cos(a) * d, y: hy + Math.sin(a) * d * 0.6, vx: 0, vy: 0, shade,
                 born: 0.15 + (c / word.cols) * 1.3 + r() * 0.5, alpha: 0, glow: 0 };
      });
      if (reduce) for (const s of spirits) { s.x = s.hx; s.y = s.hy; s.alpha = 1; }

      // background grid shares the letters' pitch ×3, aligned to the word
      const pitch = cell * 3;
      const x0 = ((ox % pitch) + pitch) % pitch - pitch, y0 = ((oy % pitch) + pitch) % pitch - pitch;
      const cols = Math.ceil((W - x0) / pitch) + 1, rows = Math.ceil((H - y0) / pitch) + 1;
      grid = { pitch, cols, rows, x0, y0, heat: new Float32Array(cols * rows), size: Math.round(pitch * 0.62) };

      const clear = [...host.querySelectorAll("[data-clear]")].map((el) => {
        const b = el.getBoundingClientRect();
        return { l: b.left - box.left - pitch * 0.5, t: b.top - box.top - pitch * 0.5, r: b.right - box.left + pitch * 0.5, b: b.bottom - box.top + pitch * 0.5 };
      });
      const word0 = { l: ox - pitch, t: oy - pitch, r: ox + cell * word.cols + pitch, b: oy + cell * word.rows + pitch };
      const blocked = (x, y, s) => [word0, ...clear].some((q) => x + s > q.l && x < q.r && y + s > q.t && y < q.b);
      const fr = rng(141);
      field = [];
      for (let j = 0; j < rows; j++) for (let i = 0; i < cols; i++) {
        const x = x0 + i * pitch, y = y0 + j * pitch;
        const nx = x / W, ny = y / H;
        const edge = Math.max(0, 1 - Math.min(nx, 1 - nx) / 0.22);
        const floor = Math.max(0, (ny - 0.7) / 0.3);
        const p = blocked(x, y, grid.size) ? 0 : 0.015 + 0.6 * edge * edge + 0.4 * floor * floor;
        if (p > 0) {
          const on = fr() < p;
          field.push({ x, y, p, tone: fr() < 0.22 ? 2 : 1, a: on ? 1 : 0, on, ok: !blocked(x, y, grid.size) });
        }
      }
      grid.blocked = blocked;
    }

    // ---- pointer
    let px = -1e4, py = -1e4, pvx = 0, pvy = 0, lastMove = -10;
    const onMove = (e) => {
      const b = host.getBoundingClientRect();
      const nx = e.clientX - b.left, ny = e.clientY - b.top;
      pvx = nx - px; pvy = ny - py;
      px = nx; py = ny; lastMove = t;
    };
    const onLeave = () => { px = py = -1e4; };

    // ---- scan line that sweeps the word now and then
    let scan = -1, nextScan = 3.2;

    let t = 0, last = 0, raf = 0, visible = true;

    function update(dt) {
      t += dt;
      const active = t - lastMove < 0.25;
      const R = cell * 7;

      // pointer trail on the background grid
      if (active && px > -1e3) {
        const { pitch, x0, y0, cols, rows, heat } = grid;
        const ci = Math.floor((px - x0) / pitch), cj = Math.floor((py - y0) / pitch);
        for (let j = cj - 1; j <= cj + 1; j++) for (let i = ci - 1; i <= ci + 1; i++) {
          if (i < 0 || j < 0 || i >= cols || j >= rows) continue;
          const x = x0 + i * pitch, y = y0 + j * pitch;
          if (grid.blocked(x, y, grid.size)) continue;
          const d = Math.hypot(x + pitch / 2 - px, y + pitch / 2 - py) / pitch;
          heat[j * cols + i] = Math.max(heat[j * cols + i], Math.max(0, 1 - d * 0.55));
        }
      }
      const decay = Math.exp(-dt / 0.45);
      for (let k = 0; k < grid.heat.length; k++) grid.heat[k] *= decay;

      if (!reduce) {
        nextScan -= dt;
        if (nextScan <= 0 && scan < 0) { scan = ox - cell * 4; nextScan = 4 + Math.random() * 4; }
        if (scan >= 0) { scan += dt * cell * 70; if (scan > ox + cell * (word.cols + 4)) scan = -1; }
      }

      for (const s of spirits) {
        if (t < s.born) continue;
        s.alpha = Math.min(1, s.alpha + dt * 2.2);
        // spring home
        const k = 60, damp = 9.5;
        let ax = (s.hx - s.x) * k - s.vx * damp;
        let ay = (s.hy - s.y) * k - s.vy * damp;
        // pointer scatters spirits
        if (active) {
          const dx = s.x + cell / 2 - px, dy = s.y + cell / 2 - py;
          const d = Math.hypot(dx, dy);
          if (d < R && d > 0.01) {
            const f = (1 - d / R) ** 2 * 5200 * (1 + Math.min(1, Math.hypot(pvx, pvy) / 30));
            ax += (dx / d) * f + (Math.random() - 0.5) * 900;
            ay += (dy / d) * f + (Math.random() - 0.5) * 900;
            s.glow = 1;
          }
        }
        s.vx += ax * dt; s.vy += ay * dt;
        s.x += s.vx * dt; s.y += s.vy * dt;
        if (scan >= 0 && Math.abs(s.hx - scan) < cell * 1.5) s.glow = Math.max(s.glow, 0.9);
        s.glow *= Math.exp(-dt / 0.35);
      }

      // the field breathes
      if (field.length && Math.random() < dt * 12) {
        const f = field[Math.floor(Math.random() * field.length)];
        f.on = Math.random() < f.p * 1.15;
      }
      for (const f of field) f.a = f.on ? Math.min(1, f.a + dt / 0.7) : Math.max(0, f.a - dt / 0.7);
    }

    function draw() {
      ctx.clearRect(0, 0, W, H);
      const { pitch, x0, y0, cols, heat, size } = grid;
      for (const f of field) {
        if (f.a < 0.02) continue;
        ctx.globalAlpha = f.a;
        ctx.fillStyle = f.tone === 2 ? C.field2 : C.field;
        ctx.fillRect(f.x, f.y, size, size);
      }
      for (let k = 0; k < heat.length; k++) {
        const h = heat[k];
        if (h < 0.06) continue;
        const i = k % cols, j = Math.floor(k / cols);
        ctx.globalAlpha = Math.min(1, h * 1.2);
        ctx.fillStyle = h > 0.6 ? C.accent : C.dim;
        ctx.fillRect(x0 + i * pitch, y0 + j * pitch, size, size);
      }
      const s0 = cell - gap;
      for (const s of spirits) {
        if (s.alpha <= 0) continue;
        ctx.globalAlpha = s.alpha;
        ctx.fillStyle = s.glow > 0.5 ? C.hot : s.glow > 0.15 ? C.accent : C[s.shade];
        ctx.fillRect(Math.round(s.x), Math.round(s.y), s0, s0);
      }
      ctx.globalAlpha = 1;
    }

    function frame(now) {
      const dt = last ? Math.min(0.033, (now - last) / 1000) : 0.016;
      last = now;
      update(dt);
      draw();
      raf = visible ? requestAnimationFrame(frame) : 0;
    }
    const start = () => {
      if (raf) return;
      last = 0;
      raf = requestAnimationFrame(frame);
    };

    readColors();
    layout(true);
    if (reduce) { t = 99; draw(); } else start();
    const relayout = () => { layout(false); if (reduce) draw(); };
    document.fonts?.ready.then(relayout);
    const ro = new ResizeObserver(relayout);
    ro.observe(host);
    const io = new IntersectionObserver(([e]) => { visible = !!e?.isIntersecting; if (visible && !reduce) start(); });
    io.observe(host);
    const vis = () => !document.hidden && !reduce && start();
    document.addEventListener("visibilitychange", vis);
    host.addEventListener("pointermove", onMove);
    host.addEventListener("pointerleave", onLeave);
    return () => {
      cancelAnimationFrame(raf);
      ro.disconnect();
      io.disconnect();
      document.removeEventListener("visibilitychange", vis);
      host.removeEventListener("pointermove", onMove);
      host.removeEventListener("pointerleave", onLeave);
    };
  }, [slotRef]);

  return <canvas ref={ref} className="hero-canvas" aria-hidden />;
}
