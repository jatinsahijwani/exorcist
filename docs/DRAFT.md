# `exorcist draft` — EXPERIMENTAL: NEAR AI drafts a model from Rust

Every Exorcist result is about a model, and writing the model is the slow, human part. `exorcist
draft` asks a model on NEAR AI Cloud to draft that Lean model from a near-sdk Rust file:

```sh
export NEARAI_API_KEY=...        # https://cloud.near.ai; never commit it
./.lake/build/bin/exorcist draft --from sandbox/contracts/vault/src/lib.rs --role vault --name VaultFixed
```

1. The prompt contains Exorcist's DSL reference (accounts, calls, context, promises, outcomes) and the
   Rust source, with the enabled cargo features spelled out.
2. The reply is compiled with Lean. Errors go back to the model, for up to `--rounds` (default 4) rounds.
   Drafts that use `sorry`, `admit`, `native_decide` or new axioms are rejected.
3. The compiling draft is written to `drafts/<Name>.lean`.

**A draft is never trusted.** It is a starting point for a human, who reviews it against the Rust.

## Assessment: `make drafts`

`scripts/drafts.sh` drafts our three contracts: the token, the hook, and the vault built three ways
(default, `ghost_funds_bug`, `withdraw_no_restore_bug`). It then assesses each draft:

* **Compile check**, with the repair loop above.
* **Semantic check.** The drafted handler replaces the hand-written one inside the same network, and
  the bounded explorer runs the built-in scenarios on both. A correct draft of the fixed vault must be
  clean, and a correct draft of each buggy build must reproduce its attack. Every row must say `✓ same`.
* **Textual diff** against the hand-written model (`drafts/*.diff`), for the reviewer.

The results go to `drafts/ASSESSMENT.md`.

## Status

The pipeline is tested offline in CI by `scripts/test-draft.sh`. It runs against
`scripts/mock-nearai.py`, a fake endpoint whose "drafts" just call the hand-written handlers. That test
checks the plumbing (request, compile check, repair loop, comparison, report), and nothing about
draft quality.

**Real drafts have not been generated yet.** They need a NEAR AI Cloud key. Run
`NEARAI_API_KEY=... make drafts`, commit `drafts/`, and replace this paragraph with an assessment of
what `drafts/ASSESSMENT.md` shows.
