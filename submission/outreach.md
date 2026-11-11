# Outreach messages (Jatin sends these himself)

## NEAR developers (Telegram / Discord, short)

> Hi! I built Exorcist for NEAR HACKATHON. It checks whether a contract can lose funds when a
> cross-contract call fails: the ft_transfer_call refund + early ledger credit pattern behind the
> Oct 1 Intents incident. It prints a step-by-step attack trace, or a Lean proof that the ledger
> stays backed for every trace, and replays traces in the NEAR sandbox. Repo: https://github.com/jatinsahijwani/exorcist
> Would you try `make quick` (about 2 min) and tell me what's confusing? I'd also love one real
> callback pattern from your contracts to model next.

## Security / formal-methods people (X DM or email-style)

> Hi <name>, Exorcist is a hackathon project that models NEAR's async receipt semantics and the
> NEP-141 resolve/refund flow in Lean 4. It does a bounded search over orderings × receipt failures
> (shortest attack, re-checked by the kernel with `decide`) and an inductive invariant proof (any
> accounts, amounts, adversarial code, any receipt failing) that a fixed deposit vault stays solvent.
> No sorry, no native_decide; the model is cross-checked against real contracts in the NEAR sandbox.
> I'd value 10 minutes of criticism, especially on the semantics assumptions in docs/SEMANTICS.md.
> https://github.com/jatinsahijwani/exorcist

## Judges (only if they reach out first)

> Thanks for looking at Exorcist! The quickest path: `make quick` (about 2 min, no keys or network beyond
> toolchains) prints a PASS/FAIL table; every row says "bounded to depth N" or "proven for all traces".
> `make demo` adds the near-workspaces sandbox replay. What the proof covers and what it doesn't is
> in README → "What exactly is proven" and "Limits". The demo video: <DEMO_URL>. Happy to answer
> anything, for example how to model your own contract.

## Reply template when a judge asks a hard question

> Good question. Short answer: <one sentence>. Where to see it: <file / command>.
> What it does not cover: <honest limit>. If useful, I can show it live with `<command>`.

(Short answers to the likely questions are in submission/FAQ.md.)
