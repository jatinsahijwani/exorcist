# Semantics we model, and where each rule comes from

Checked on 2026-11-11 against near-sdk-rs 5.30.1 (`near-contract-standards/src/fungible_token/core_impl.rs`,
`macros.rs`, `receiver.rs`, `near-sdk/src/environment/env.rs`), NEP-141 (`nep-0141.md`), docs.near.org
(smart-contracts/anatomy/crosscontract) and the protocol spec (nomicon.io RuntimeSpec/Receipts, /Refunds).

## NEAR runtime
| Rule | Source |
|---|---|
| Each receipt executes and commits on its own; a later failure never rolls back an earlier receipt. | docs: "Your state will not rollback automatically"; "only its own state changes are reverted" |
| A failing receipt reverts only its own state changes (all actions of that receipt together). | docs: batch actions in one receipt "if any function fails, then they all get reverted" |
| A callback always runs, even when the promise it waits on failed; it sees `PromiseResult::Failed`. | docs: "the callback always runs, whether the external contract fails or not" |
| A failed input still arrives (DataReceipt with `data = None`) so dependents are not stuck. | nomicon Receipts |
| No ordering guarantee between independent receipts; a receipt waits until its input data arrives. | nomicon Receipts: "Runtime doesn't require that Receipts come in a particular order" |
| Attached deposit of a failed function-call receipt is refunded to the **predecessor** (not the signer), via a separate refund receipt. | nomicon Refunds: "The refund receiver is the `predecessor_id` by default" (redirect via `promise_set_refund_to` since v82 — not modelled) |
| A method returning a promise (`promise_return`) makes that promise's result its own result. | near-sdk `PromiseOrValue`, env `promise_return` |

## NEP-141 reference implementation
| Rule | Source |
|---|---|
| `ft_transfer` / `ft_transfer_call`: `assert_one_yocto`; sender ≠ receiver; amount > 0; sender balance ≥ amount (panic otherwise). | core_impl.rs `internal_transfer` |
| `ft_transfer_call` moves tokens **in its own receipt**, then `receiver.ft_on_transfer(sender, amount, msg).then(self.ft_resolve_transfer(sender, receiver, amount))` and returns that promise. | core_impl.rs |
| `ft_resolve_transfer` is `#[private]` (predecessor must be the token itself). | macros.rs |
| unused = parsed U128 result; if the promise **failed** or the result does not parse → `amount`; then `min(unused, amount)`. | core_impl.rs `internal_ft_resolve_transfer` |
| If unused > 0 and the receiver's *current* balance > 0: refund = min(receiver balance, unused), moved receiver → sender. Returns `amount − refund`. | core_impl.rs |
| If the sender account was deleted, the refund is burned. | core_impl.rs — **not modelled** (accounts are never deleted in our model) |
| Calling `ft_on_transfer` on an account with no contract fails → full refund. | NEP-141 text; runtime |

## Modelling choices (honest limits)
- Gas is not modelled numerically. Instead the adversary may force any function-call receipt to fail
  (models out-of-gas or attacker-controlled panics). Proofs for fixed contracts use the strongest setting
  (every call receipt may fail); found attack traces use only failures of attacker-owned contracts.
- Storage registration (NEP-145) is not modelled: every account is treated as registered.
- Balances are unbounded naturals (no u128 overflow).
- The hook in the explorer returns `"0"` by default; the `noreturn-*` models use a hook that returns
  nothing. Other contracts in the proof are arbitrary code (they cannot write token/vault storage).
- Contract accounts (`token`, `vault`) never sign transactions (nobody holds their keys).

## Validation against real NEAR (sandbox)

`sandbox/` contains Rust versions of the token, the hook and the three vault variants, written for
this project. `sandbox/tests/replay.rs` replays every exported trace in a local NEAR sandbox
(near-workspaces 0.24) and compares, after every transaction, all token balances, all ledger entries,
and the set of receipts that ran with their success/failure, against the Lean model.

Result on 2026-11-11: **all 8 replays matched; no model change was needed.** A negative-control
test checks that the harness does fail when the prediction is wrong.

How model failures are reproduced on the real chain:

| Model step | Sandbox |
|---|---|
| `FAIL hook.on_deposit` | eve switches her hook to `panic` mode before the transaction |
| `FAIL token.ft_transfer` (vault payout) | the receiver unregisters from the token first, so the transfer panics ("not registered"), as with the reference token |
| hook returns nothing (`noreturn-*`) | the hook runs in `none` mode (succeeds, returns no value) |

What the sandbox comparison does not cover: NEAR (yocto) balances and gas are not compared; the
Rust token's simplified registration (`register`/`unregister`) and its burn-on-deleted-sender path are
not part of the Lean model.

## Observations

- With the vulnerable vault, a hook that **returns nothing** is enough to lose funds — no failure is
  involved: the token cannot parse the chain's result as a number and refunds everything
  (`noreturn-vulnerable`, confirmed in the sandbox).
