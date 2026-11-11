import Verifier.Models.Registry
namespace NearAsync.Vault.Draft.VaultGhost
open NearAsync NearAsync.Vault

def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .ft_on_transfer sender amount msg =>
    if ctx.deposit ≠ 0 then .panic "Method ft_on_transfer doesn't accept deposit"
    else if ctx.pred ≠ .token then .panic "only the token may call ft_on_transfer"
    else
      match msg with
      | .plain =>
        .ok { s with ledger := s.ledger.add sender amount } [] (.val (.nat 0))
      | .notify hook =>
        -- BUG (ghost_funds_bug): credit first, then return the notification's result
        .ok { s with ledger := s.ledger.add sender amount }
          [{ recv := hook, call := .on_deposit sender amount, deposit := 0, after := none }]
          (.promise 0)
  | .after_notify who amount =>
    if ctx.pred ≠ ctx.self then .panic "Method after_notify is private"
    else if ctx.deposit ≠ 0 then .panic "Method after_notify doesn't accept deposit"
    else
      match ctx.input with
      | some (.ok _) =>
        .ok { s with ledger := s.ledger.add who amount } [] (.val (.nat 0))
      | some .failed =>
        .ok s [] (.val (.nat amount))
      | none => .panic "promise result index out of bounds"
  | .withdraw amount =>
    if ctx.deposit ≠ 0 then .panic "Method withdraw doesn't accept deposit"
    else if amount = 0 then .panic "amount must be positive"
    else
      let who := ctx.pred
      let balance := s.ledger.get who
      if balance < amount then .panic "insufficient ledger balance"
      else
        .ok { s with ledger := s.ledger.set who (balance - amount) }
          [ { recv := .token, call := .ft_transfer who amount, deposit := 1, after := none },
            { recv := ctx.self, call := .after_withdraw who amount, deposit := 0, after := some 0 } ]
          (.val .unit)
  | .after_withdraw who amount =>
    if ctx.pred ≠ ctx.self then .panic "Method after_withdraw is private"
    else if ctx.deposit ≠ 0 then .panic "Method after_withdraw doesn't accept deposit"
    else
      match ctx.input with
      | some .failed =>
        .ok { s with ledger := s.ledger.add who amount } [] (.val .unit)
      | some (.ok _) =>
        .ok s [] (.val .unit)
      | none => .panic "promise result index out of bounds"
  | _ => .panic "method not found"

end NearAsync.Vault.Draft.VaultGhost