import Verifier.Async

/-!
# Calls used by the example contracts, and the NEP-141 token

`ftHandle` follows `near-contract-standards` (near-sdk-rs 5.30.1, `core_impl.rs`):
* `ft_transfer`, `ft_transfer_call`: exactly 1 yoctoNEAR, sender ≠ receiver, amount > 0,
  sender balance ≥ amount; tokens move in the calling receipt itself.
* `ft_transfer_call` returns `receiver.ft_on_transfer(..).then(self.ft_resolve_transfer(..))`.
* `ft_resolve_transfer` is private; unused = parsed result, or `amount` if the promise failed or
  the value does not parse, capped at `amount`; refund = min(unused, receiver's current balance)
  when that balance is positive. Returns the used amount.
-/

namespace NearAsync

/-- The `msg` argument of `ft_transfer_call`, as our example receivers interpret it. -/
inductive Msg (α : Type) where
  | plain
  /-- "after crediting, notify contract `hook` about the deposit" -/
  | notify (hook : α)
  deriving DecidableEq, Repr

/-- Every method of every contract in the examples. -/
inductive Call (α : Type) where
  -- NEP-141 token
  | ft_transfer (receiver : α) (amount : Nat)
  | ft_transfer_call (receiver : α) (amount : Nat) (msg : Msg α)
  | ft_resolve_transfer (sender receiver : α) (amount : Nat)
  -- NEP-141 receiver side (implemented by vaults)
  | ft_on_transfer (sender : α) (amount : Nat) (msg : Msg α)
  -- third-party notification hook
  | on_deposit (who : α) (amount : Nat)
  -- vault methods
  | after_notify (who : α) (amount : Nat)
  | withdraw (amount : Nat)
  | after_withdraw (who : α) (amount : Nat)
  deriving DecidableEq, Repr

variable {α : Type} [DecidableEq α]

/-- Outcome of a token method on the token's balance map. -/
def ftHandle {S : Type} (getFt : S → Bal α) (setFt : S → Bal α → S)
    (ctx : Ctx α) (c : Call α) (s : S) : Outcome S α (Call α) :=
  let ft := getFt s
  match c with
  | .ft_transfer to amt =>
    if ctx.deposit ≠ 1 then .panic "requires exactly 1 yoctoNEAR" else
    if ctx.pred = to then .panic "sender = receiver" else
    if amt = 0 then .panic "amount must be positive" else
    if ft.get ctx.pred < amt then .panic "insufficient balance" else
    .ok (setFt s ((ft.sub ctx.pred amt).add to amt)) [] (.val .unit)
  | .ft_transfer_call to amt msg =>
    if ctx.deposit ≠ 1 then .panic "requires exactly 1 yoctoNEAR" else
    if ctx.pred = to then .panic "sender = receiver" else
    if amt = 0 then .panic "amount must be positive" else
    if ft.get ctx.pred < amt then .panic "insufficient balance" else
    .ok (setFt s ((ft.sub ctx.pred amt).add to amt))
      [ { recv := to, call := .ft_on_transfer ctx.pred amt msg },
        { recv := ctx.self, call := .ft_resolve_transfer ctx.pred to amt, after := some 0 } ]
      (.promise 1)
  | .ft_resolve_transfer sender receiver amt =>
    if ctx.pred ≠ ctx.self then .panic "private method" else
    match ctx.input with
    | none => .panic "no promise result"
    | some r =>
      let unused := match r with
        | .ok (.nat n) => min n amt
        | .ok .unit => amt
        | .failed => amt
      let rb := ft.get receiver
      if 0 < unused ∧ 0 < rb then
        let refund := min rb unused
        .ok (setFt s ((ft.sub receiver refund).add sender refund)) [] (.val (.nat (amt - refund)))
      else
        .ok s [] (.val (.nat amt))
  | _ => .panic "method not found"

end NearAsync
