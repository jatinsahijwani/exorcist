"use client";

import { useCallback, useEffect, useMemo, useState } from "react";
import { REPO } from "./Topbar";

const BASE = process.env.NEXT_PUBLIC_BASE_PATH;
const LANES = ["eve", "token", "vault", "hook"];
const THEOREM_URL = `${REPO}/blob/main/Verifier/Proof/Theorem.lean`;

// Everything shown comes from these two files, written by scripts/viewer-traces.sh from
// `exorcist check ... --json`. Nothing about the trace is hard-coded here.
const VIEWS = {
  vulnerable: {
    label: "Vulnerable",
    file: "incident-2026-10.json",
    command: "exorcist check incident-2026-10 --json web/public/traces/incident-2026-10.json",
    pick: (d) => d.violation.trace,
  },
  fixed: {
    label: "Fixed",
    file: "incident-2026-10-fixed.json",
    command:
      "exorcist check incident-2026-10-fixed --attack-from incident-2026-10 --json web/public/traces/incident-2026-10-fixed.json",
    pick: (d) => d.attack_replay.trace,
  },
};

// What each method is, in general terms (not about any particular trace).
const METHOD = {
  ft_transfer_call: "NEP-141: the token moves the tokens to the receiver, then calls its ft_on_transfer",
  ft_on_transfer: "the receiver handles the deposit and says how much is unused",
  on_deposit: "the deposit notification, sent to a contract the depositor chose",
  after_notify: "the vault's callback: sees whether the notification succeeded",
  ft_resolve_transfer: "NEP-141 callback: if the chain failed or reports unused tokens, the token refunds the sender",
  withdraw: "the vault pays out real tokens for a ledger balance",
  after_withdraw: "the vault's callback after paying out",
  ft_transfer: "NEP-141: a plain token transfer",
};

const fmtArgs = (a = {}) =>
  Object.values(a)
    .map((v) => (typeof v === "string" && v.includes(" ") ? `"${v}"` : String(v)))
    .join(", ");

function outcomeText(s) {
  if (s.kind === "submit") return { text: "transaction submitted: a receipt is created", tone: "" };
  if (s.kind === "refund") return { text: `refund of ${s.amount_yocto} yoctoNEAR`, tone: "" };
  if (s.kind === "fail") return { text: "✗ forced to fail by the adversary (the attacker's own contract)", tone: "bad" };
  if (s.outcome === "failed") return { text: "✗ panics: its state changes are discarded", tone: "bad" };
  if (s.outcome === "promise") return { text: "returns a promise (the result arrives later)", tone: "" };
  if (s.outcome === "ok") return { text: "ok", tone: "" };
  if (s.outcome?.startsWith("ok:")) return { text: `ok, returns ${s.outcome.slice(3)}`, tone: "" };
  return { text: s.outcome ?? "", tone: "" };
}

function diff(prev, next) {
  const out = [];
  for (const [k, label] of [["ft", "tokens"], ["ledger", "ledger"]]) {
    for (const who of Object.keys(next[k])) {
      const a = prev[k][who] ?? 0, b = next[k][who] ?? 0;
      if (a !== b) out.push(`${label} ${who}: ${a} → ${b}`);
    }
  }
  return out;
}

export function Viewer() {
  const [view, setView] = useState("vulnerable");
  const [data, setData] = useState({});
  const [error, setError] = useState(null);
  const [k, setK] = useState(0); // 0 = initial state, i = after step i
  const [playing, setPlaying] = useState(false);
  const [speed, setSpeed] = useState(1);

  // ?model=fixed, ?step=5, ?autoplay=1 (handy for screen recording)
  useEffect(() => {
    const q = new URLSearchParams(window.location.search);
    if (q.get("model") === "fixed") setView("fixed");
    const st = Number(q.get("step"));
    if (st > 0) setK(st);
    if (q.get("autoplay") === "1") setPlaying(true);
  }, []);

  useEffect(() => {
    let live = true;
    Promise.all(
      Object.entries(VIEWS).map(([key, v]) =>
        fetch(`${BASE}/traces/${v.file}`).then((r) => {
          if (!r.ok) throw new Error(`${v.file}: HTTP ${r.status}`);
          return r.json().then((j) => [key, j]);
        }),
      ),
    )
      .then((pairs) => live && setData(Object.fromEntries(pairs)))
      .catch((e) => live && setError(String(e)));
    return () => {
      live = false;
    };
  }, []);

  const doc = data[view];
  const steps = useMemo(() => (doc ? VIEWS[view].pick(doc) : []), [doc, view]);
  const states = useMemo(() => (doc ? [doc.initial_state, ...steps.map((s) => s.state_after)] : []), [doc, steps]);
  const n = steps.length;
  const kk = Math.min(k, n);

  const scale = useMemo(() => {
    const all = Object.values(data).flatMap((d) =>
      [d.initial_state, ...VIEWS[d.model.endsWith("fixed") ? "fixed" : "vulnerable"].pick(d).map((s) => s.state_after)].flatMap((s) => [
        s.ft.vault,
        s.ledger_total,
      ]),
    );
    return Math.max(100, Math.ceil(Math.max(0, ...all) / 100) * 100);
  }, [data]);

  useEffect(() => {
    if (!playing) return;
    if (kk >= n) {
      setPlaying(false);
      return;
    }
    const id = setTimeout(() => setK((x) => Math.min(n, x + 1)), 1700 / speed);
    return () => clearTimeout(id);
  }, [playing, kk, n, speed]);

  const switchView = useCallback((v) => {
    setView(v);
    setK(0);
    setPlaying(false);
  }, []);

  useEffect(() => {
    const onKey = (e) => {
      if (e.target.closest?.("input, textarea")) return;
      if (e.key === " ") {
        e.preventDefault();
        if (kk >= n) setK(0);
        setPlaying((p) => !p);
      } else if (e.key === "ArrowRight") setK((x) => Math.min(n, x + 1));
      else if (e.key === "ArrowLeft") setK((x) => Math.max(0, x - 1));
      else if (e.key === "Home") setK(0);
      else if (e.key === "End") setK(n);
      else if (e.key === "v") switchView("vulnerable");
      else if (e.key === "f") switchView("fixed");
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [kk, n, switchView]);

  if (error) return <div className="vw-wrap"><p className="bad">Could not load the trace data: {error}</p></div>;
  if (!doc) return <div className="vw-wrap"><p className="muted">Loading the exorcist output…</p></div>;

  const st = states[kk];
  const cur = kk > 0 ? steps[kk - 1] : null;
  const isFixed = view === "fixed";
  const v = doc.violation;

  return (
    <div className="vw-wrap">
      <div className="vw-head">
        <div>
          <p className="eyebrow">Trace viewer · real exorcist output</p>
          <h1 className="vw-title">
            {isFixed ? "The same attack, on the fixed contract" : "Ghost funds: the attack Exorcist found"}
          </h1>
          <p className="vw-sub">{doc.disclaimer}</p>
        </div>
        <div className="vw-toggle" role="tablist" aria-label="Contract">
          {Object.entries(VIEWS).map(([key, x]) => (
            <button key={key} role="tab" aria-selected={view === key} className={view === key ? "on" : ""} onClick={() => switchView(key)}>
              {x.label}
            </button>
          ))}
        </div>
      </div>

      <div className="vw-verdict">
        {isFixed ? (
          <>
            <span className="pill ok">
              No violation · bounded to depth {doc.bounds.depth} · {doc.states_explored.toLocaleString("en-US")} states
            </span>
            <span className="pill ok">
              Same attack re-run ({doc.attack_replay.attack_steps} steps): property holds at every step ={" "}
              {String(doc.attack_replay.property_holds_every_step)}
            </span>
            <a className="badge-proven" href={THEOREM_URL} title="concrete_fixed_solvent_from / fixed_vault_solvent_forever in Verifier/Proof/Theorem.lean">
              <span aria-hidden>■</span> Proven for all traces of our NEAR execution model →
            </a>
          </>
        ) : (
          <>
            <span className="pill bad">
              VIOLATION ({v.kind}) at depth {v.depth} · {doc.states_explored.toLocaleString("en-US")} states explored
            </span>
            <span className="pill">witness checked by the Lean kernel: {v.witness_file}</span>
          </>
        )}
      </div>

      <div className="vw-grid">
        <div className="vw-stage">
          <Lanes steps={steps} k={kk} />
          <div className="vw-controls">
            <button className="ctl" onClick={() => { setK(0); setPlaying(false); }} aria-label="Back to the start" title="Start (Home)">⏮</button>
            <button className="ctl" onClick={() => setK((x) => Math.max(0, x - 1))} disabled={kk === 0} aria-label="Previous step" title="Previous (←)">◀</button>
            <button
              className="ctl play"
              onClick={() => { if (kk >= n) setK(0); setPlaying((p) => !p); }}
              aria-label={playing ? "Pause" : "Play"}
              title="Play / pause (space)"
            >
              {playing ? "❚❚ Pause" : "▶ Play"}
            </button>
            <button className="ctl" onClick={() => setK((x) => Math.min(n, x + 1))} disabled={kk === n} aria-label="Next step" title="Next (→)">▶</button>
            <span className="vw-count num">
              step {kk} / {n}
            </span>
            <div className="vw-dots" aria-hidden>
              {Array.from({ length: n + 1 }, (_, i) => (
                <button
                  key={i}
                  tabIndex={-1}
                  className={`dot ${i === kk ? "cur" : ""} ${i > 0 && (steps[i - 1].kind === "fail" || steps[i - 1].outcome === "failed") ? "f" : ""} ${i > 0 && !states[i].solvent ? "ins" : ""}`}
                  onClick={() => setK(i)}
                />
              ))}
            </div>
            <div className="vw-speed">
              {[0.5, 1, 2].map((s) => (
                <button key={s} className={speed === s ? "on" : ""} onClick={() => setSpeed(s)}>
                  {s}×
                </button>
              ))}
            </div>
          </div>
        </div>

        <aside className="vw-panel">
          <StepCard step={cur} prev={states[kk - 1]} next={st} adversary={doc.bounds.adversary} />
          <Bars st={st} scale={scale} />
          <Eve st={st} init={states[0]} />
        </aside>
      </div>

      <footer className="vw-foot">
        <div>
          <span className="muted">Data: </span>
          <code>{VIEWS[view].command}</code>
        </div>
        <div className="muted">
          Regenerated by <code>scripts/viewer-traces.sh</code> (only the machine-dependent <code>search_ms</code> is removed); CI checks the committed
          JSON equals fresh output. <a href={`${BASE}/traces/${VIEWS[view].file}`}>Raw JSON</a> · Keys: space play, ← → step, v / f switch.
        </div>
      </footer>
    </div>
  );
}

/* ------------------------------------------------------------------ lanes */

const VW = 960, LANE_TOP = 58, ROW = 54, PAD = 120;

function laneX(name, lanes) {
  const i = lanes.indexOf(name);
  return PAD + (i * (VW - 2 * PAD)) / (lanes.length - 1);
}

function Lanes({ steps, k }) {
  const lanes = [...LANES, ...new Set(steps.flatMap((s) => [s.signer, s.predecessor, s.receiver]).filter((x) => x && !LANES.includes(x)))];
  const H = LANE_TOP + 40 + Math.max(steps.length, 8) * ROW + 10;
  return (
    <svg className="lanes" viewBox={`0 0 ${VW} ${H}`} role="img" aria-label={`Receipt diagram, ${k} of ${steps.length} steps shown`}>
      <defs>
        <marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 z" fill="var(--lane-arrow)" />
        </marker>
        <marker id="ah-cur" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 z" fill="var(--accent)" />
        </marker>
        <marker id="ah-bad" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 z" fill="var(--negative)" />
        </marker>
      </defs>
      {lanes.map((l) => {
        const x = laneX(l, lanes);
        return (
          <g key={l}>
            <line x1={x} x2={x} y1={LANE_TOP + 20} y2={H - 6} className="lifeline" />
            <rect x={x - 62} y={LANE_TOP - 26} width={124} height={40} className="lane-head" />
            <text x={x} y={LANE_TOP} className="lane-name" textAnchor="middle">{l}</text>
          </g>
        );
      })}
      {steps.slice(0, k).map((s, i) => (
        <Arrow key={`${i}-${s.kind}-${s.receipt_id}`} s={s} i={i} lanes={lanes} current={i === k - 1} />
      ))}
    </svg>
  );
}

function Arrow({ s, i, lanes, current }) {
  const y = LANE_TOP + 52 + i * ROW;
  const from = s.kind === "submit" ? s.signer : s.predecessor ?? s.receiver;
  const to = s.receiver;
  const x1 = laneX(from, lanes), x2 = laneX(to, lanes);
  const failed = s.kind === "fail" || s.outcome === "failed";
  const cls = `arrow ${current ? "cur" : ""} ${failed ? "bad" : ""} ${s.kind === "submit" ? "tx" : ""}`;
  const marker = failed ? "url(#ah-bad)" : current ? "url(#ah-cur)" : "url(#ah)";
  const label = `${s.method ?? "refund"}(${fmtArgs(s.args)})`;
  const self = x1 === x2;
  const d = self ? `M${x1},${y - 10} h46 v20 h-40` : `M${x1},${y} L${x2 + (x2 > x1 ? -4 : 4)},${y}`;
  const lx = self ? x1 + 56 : Math.min(x1, x2) + 8;
  const tag = s.kind === "submit" ? "tx" : `#${s.receipt_id}`;
  return (
    <g className={cls}>
      <text x={18} y={y + 5} className="row-no">{s.i}</text>
      <path d={d} pathLength="1" markerEnd={marker} className="arrow-line" fill="none" />
      {current && !self && (
        <rect className="packet" x={x1 - 5} y={y - 5} width={10} height={10} style={{ "--dx": `${x2 - x1}px` }} />
      )}
      <text x={lx} y={y - (self ? 16 : 10)} className="arrow-label">
        <tspan className="rid">{tag}</tspan> {label}
      </text>
      {failed && (
        <text x={x2 + (self ? 52 : x2 > x1 ? 10 : -26)} y={y + 7} className="cross">✗</text>
      )}
    </g>
  );
}

/* ------------------------------------------------------------------ panel */

function StepCard({ step, prev, next, adversary }) {
  if (!step)
    return (
      <div className="vw-card">
        <p className="eyebrow">Initial state</p>
        <p className="vw-step-text">
          The ledger owes {next.ledger_total} and the vault holds {next.ft.vault} tokens. Eve holds {next.ft.eve} tokens.
        </p>
        <p className="muted small">Adversary: {adversary}. Press play, or → to step.</p>
      </div>
    );
  const o = outcomeText(step);
  const changes = diff(prev, next);
  const who = step.kind === "submit" ? `${step.signer} → ${step.receiver}` : `${step.predecessor ?? ""} → ${step.receiver}`;
  return (
    <div className={`vw-card ${o.tone === "bad" ? "bad" : ""}`}>
      <p className="eyebrow">
        Step {step.i} · {step.kind === "submit" ? "transaction" : step.kind === "fail" ? "receipt (forced failure)" : "receipt"}
        {step.receipt_id !== undefined ? ` #${step.receipt_id}` : ""}
      </p>
      <p className="vw-step-who">{who}</p>
      <p className="vw-step-text">
        <code>{step.method ?? "refund"}({fmtArgs(step.args)})</code>
      </p>
      {step.method && METHOD[step.method] && <p className="muted small">{METHOD[step.method]}</p>}
      <p className={`vw-outcome ${o.tone}`}>{o.text}</p>
      {changes.length > 0 && (
        <ul className="vw-changes">
          {changes.map((c) => <li key={c}>{c}</li>)}
        </ul>
      )}
    </div>
  );
}

function Bars({ st, scale }) {
  const held = st.ft.vault, owes = st.ledger_total;
  const gap = owes - held;
  const pct = (x) => `${(100 * x) / scale}%`;
  return (
    <div className="vw-card">
      <p className="eyebrow">Is the vault backed?</p>
      <div className="meter-row">
        <span className="meter-label">tokens vault holds</span>
        <div className="meter-track"><div className="meter held" style={{ width: pct(held) }} /></div>
        <span className="meter-num num">{held}</span>
      </div>
      <div className="meter-row">
        <span className="meter-label">ledger owes</span>
        <div className="meter-track">
          <div className="meter owes" style={{ width: pct(Math.min(owes, held)) }} />
          <div className="meter gap" style={{ left: pct(Math.min(owes, held)), width: pct(Math.max(0, gap)) }} />
        </div>
        <span className="meter-num num">{owes}</span>
      </div>
      <p className={`vw-gap ${gap > 0 ? "bad" : "ok"}`}>
        {gap > 0 ? `INSOLVENT: ${gap} owed with no tokens behind it` : "backed: every ledger entry has tokens behind it"}
      </p>
    </div>
  );
}

function Eve({ st, init }) {
  const put = init.ft.eve, now = st.ft.eve;
  const profit = now - put;
  return (
    <div className="vw-card slim">
      <span className="muted">eve&apos;s tokens: </span>
      <b className="num">{now}</b>
      <span className="muted"> (started with {put}; ledger credit {st.ledger.eve})</span>
      {profit > 0 && <span className="bad"> · profit +{profit}</span>}
    </div>
  );
}
