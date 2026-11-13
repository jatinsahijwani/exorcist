import Link from "next/link";
import { Hero } from "@/components/Hero";
import { Footer, REPO, Topbar } from "@/components/Topbar";

const BASE = process.env.NEXT_PUBLIC_BASE_PATH;

const TRACE = [
  ["1. eve sends tx: token.ft_transfer_call(vault, 100, \"notify hook\") (+1 yocto)", "ledger: alice=300 eve=0 (total 300) | tokens: vault=300 alice=0 eve=100", false],
  ["2. run #0 token.ft_transfer_call(vault, 100, \"notify hook\")  ⇒ returns a promise", "ledger: alice=300 eve=0 (total 300) | tokens: vault=400 alice=0 eve=0", false],
  ["3. run #1 vault.ft_on_transfer(eve, 100, \"notify hook\")  ⇒ returns a promise", "ledger: alice=300 eve=100 (total 400) | tokens: vault=400 alice=0 eve=0", false],
  ["4. FAIL #3 hook.on_deposit(eve, 100)  ⇒ adversary makes it fail", "ledger: alice=300 eve=100 (total 400) | tokens: vault=400 alice=0 eve=0", false],
  ["5. run #2 token.ft_resolve_transfer(eve, vault, 100)  ⇒ ok, returns 0  — refunds 100 vault → eve", "ledger: alice=300 eve=100 (total 400) | tokens: vault=300 alice=0 eve=100   ⚠ INSOLVENT (ledger > tokens held)", true],
  ["6. eve sends tx: vault.withdraw(100)", "ledger: alice=300 eve=100 (total 400) | tokens: vault=300 alice=0 eve=100   ⚠ INSOLVENT (ledger > tokens held)", true],
  ["7. run #5 vault.withdraw(100)  ⇒ ok (no value)", "ledger: alice=300 eve=0 (total 300) | tokens: vault=300 alice=0 eve=100", false],
  ["8. run #6 token.ft_transfer(eve, 100)  ⇒ ok (no value)", "ledger: alice=300 eve=0 (total 300) | tokens: vault=200 alice=0 eve=200   ⚠ INSOLVENT (ledger > tokens held)", true],
];

const RESULTS = [
  ["incident-2026-10", "bad", "attack found: eve cashes out 200 from a 100 deposit", ["depth 8 · 26,191 states"]],
  ["incident-2026-10-fixed", "ok", "solvent; the same attack ends with the refund and a rejected withdraw", ["proven for all traces"]],
  ["deposit-vulnerable", "bad", "insolvent after a failed notification", ["depth 5 · 444 states"]],
  ["noreturn-vulnerable", "bad", "insolvent with no failure at all (hook returns nothing)", ["depth 5 · 438 states"]],
  ["withdraw-vulnerable", "bad", "user funds stuck after a failed payout", ["depth 5 · 3,622 states"]],
  ["deposit-fixed, noreturn-fixed, withdraw-fixed", "ok", "no violation (1.04M / 0.84M / 11.2M states); solvent", ["bounded to depth 10", "proven for all traces"]],
  ["withdraw-fixed, noreturn-fixed", "ok", "no stuck funds: tokens held = ledger whenever nothing is in flight. Assumes callbacks don't fail and no plain ft_transfer donations", ["proven for all traces (under those assumptions)"]],
  ["withdraw-fixed-callback-fail", "bad", "if callbacks may fail, funds get stuck (the token's resolve runs out of gas); solvency still holds", ["depth 4 · 167 states"]],
  ["sandbox (near-workspaces, Rust)", "ok", "8 trace replays match the model after every transaction; the negative control passes", ["real contracts"]],
  ["NEAR testnet", "ok", "the attack drains the vulnerable vault; the fixed vault rejects the cash-out (4/4 transactions final)", ["testnet"]],
  ["agent gate (MCP)", "ok", "an AI coding agent is blocked from deploying the vulnerable vault and allowed after the fix", ["tested"]],
];

export default function Home() {
  return (
    <>
      <Topbar current="home" />
      <main>
        <Hero />

        <section className="band alt">
          <div className="wrap">
            <div className="stats">
              <div className="stat"><b>8 steps</b>the Oct 2026 mechanism, found automatically in 26,191 states (about 45 ms)</div>
              <div className="stat"><b>2 theorems</b>for all traces: the fixed vault stays solvent, and leaves no funds stuck (under stated assumptions)</div>
              <div className="stat"><b>8 / 8</b>sandbox replays on real Rust contracts match the model after every transaction</div>
              <div className="stat"><b>0</b>uses of <code>sorry</code> or <code>native_decide</code>; standard axioms only</div>
            </div>
          </div>
        </section>

        <section className="band" id="incident">
          <div className="wrap split">
            <div>
              <p className="eyebrow">The opening case</p>
              <h2 className="section-h">A deposit is credited. The notification fails. The token refunds. The credit stays.</h2>
              <p className="note">
                A minimal model of the mechanism in the NEAR Intents postmortem (Oct 2026), written from scratch. It is not
                their contract. According to the postmortem, an attacker&apos;s contract deliberately failed deposit
                notifications; the token refunded each deposit while the ledger kept the credit; about $3.8M of unbacked
                balances was withdrawn (<a href="https://cryptonews.net/news/security/33604900/">summary of the postmortem</a>;
                the funds were returned).
              </p>
              <p className="t2">
                Asked only whether the attacker can cash out more than she put in, <code>exorcist check incident-2026-10</code> finds
                the whole exploit, deposit through to cash-out. The Lean kernel re-runs the trace (<code>decide</code>). The fixed
                contract credits only after the notification succeeded; it is clean in 1,289,374 states and proven solvent for
                every trace of our NEAR execution model.
              </p>
              <div className="ctas" style={{ justifyContent: "flex-start", marginTop: 24 }}>
                <Link className="btn primary" href="/viewer/">Open the trace viewer →</Link>
              </div>
            </div>
            <pre className="term" aria-label="exorcist check incident-2026-10 output">
              <span className="cmd">$ exorcist check incident-2026-10</span>
              {"\nRESULT: VIOLATION (attacker_profit) at depth 8, 26191 states explored\n\n"}
              {TRACE.map(([a, b, bad]) => (
                <span key={a}>
                  {a}
                  {"\n     "}
                  <span className={bad ? "bad" : undefined}>{b}</span>
                  {"\n"}
                </span>
              ))}
              {"\n  ✓ checked by the Lean kernel (decide)"}
            </pre>
          </div>
        </section>

        <section className="band alt">
          <div className="wrap">
            <p className="eyebrow">Everything in one command</p>
            <h2 className="section-h">make demo</h2>
            <p className="lede">Finds every attack, checks each witness in the kernel, proves the fixes, and replays the traces on Rust contracts in the NEAR sandbox.</p>
            <img className="demo" src={`${BASE}/media/demo.svg`} alt="Terminal recording: exorcist finds the incident attack, proves the fix, and make demo prints an all-pass summary" />
          </div>
        </section>

        <section className="band" id="results">
          <div className="wrap">
            <p className="eyebrow">Results</p>
            <h2 className="section-h">Attacks found, fixes proven</h2>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr><th>Model</th><th>Result</th><th>Label</th></tr>
                </thead>
                <tbody>
                  {RESULTS.map(([m, cls, r, tags]) => (
                    <tr key={m + r}>
                      <td><code>{m}</code></td>
                      <td className={cls}>{r}</td>
                      <td>{tags.map((t) => <span key={t} className={`tag${t.startsWith("proven") ? " proven" : ""}`}>{t}</span>)}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </section>

        <section className="band alt" id="proven">
          <div className="wrap">
            <p className="eyebrow">What is proven</p>
            <h2 className="section-h">For every trace of our NEAR execution model</h2>
            <div className="cards">
              <div className="card">
                <h3>Solvent forever</h3>
                <p><code>fixed_vault_solvent_forever</code>: any accounts, any amounts, arbitrary attacker contracts and any receipt failing. After every trace, Σ ledger ≤ tokens held by the vault.</p>
              </div>
              <div className="card">
                <h3>No stuck funds</h3>
                <p><code>fixed_vault_no_stuck_funds</code>: whenever nothing is in flight, tokens held = Σ ledger. Assumes callbacks don&apos;t fail and no plain <code>ft_transfer</code> donations; <code>withdraw-fixed-callback-fail</code> shows the first assumption is needed.</p>
              </div>
              <div className="card">
                <h3>Small trusted base</h3>
                <p>Checked by the Lean 4 kernel. <code>#print axioms</code> shows only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. The explorer is not trusted: its traces are re-checked.</p>
              </div>
            </div>
          </div>
        </section>

        <section className="band" id="limits">
          <div className="wrap">
            <p className="eyebrow">Limits</p>
            <h2 className="section-h">What Exorcist does not claim</h2>
            <p className="lede">
              Results are about models, written by hand and reviewed. Each model is checked against the Rust on the replayed
              traces, not in general. Gas, storage staking and deleted accounts are not modelled. Bounded results cover the stated
              actors, amounts and transactions only. <code>exorcist draft</code>, which has NEAR AI draft a model from Rust, is
              experimental. The full list, and a claims table mapping every claim to a command, are in the{" "}
              <a href={`${REPO}#for-automated-reviewers`}>README</a>.
            </p>
          </div>
        </section>
      </main>
      <Footer />
    </>
  );
}
