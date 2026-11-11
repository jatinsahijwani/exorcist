import Verifier.Models.Registry
namespace NearAsync.Vault.Draft.VaultNoRestore
open NearAsync NearAsync.Vault
def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .ft_on_transfer sender amount msg =>
    if ctx.deposit ≠ 0 then .panic "Method doesn't accept deposit"
    else if ctx.pred ≠ .token then .panic "only the token may call ft_on_transfer"
    else
      match msg with
      | .plain =>
        .ok { s with ledger := s.ledger.add sender amount } [] (.val (.nat 0))
      | .notify hook =>
        .ok s
          [ { recv := hook, call := .on_deposit sender amount, deposit := 0, after := none },
            { recv := .vault, call := .after_notify sender amount, deposit := 0, after := some 0 } ]
          (.promise 1)
  | .after_notify who amount =>
    if ctx.deposit ≠ 0 then .panic "Method doesn't accept deposit"
    else if ctx.pred ≠ ctx.self then .panic "Method after_notify is private"
    else
      match ctx.input with
      | none => .panic "promise result index out of bounds"
      | some (.ok _) =>
        .ok { s with ledger := s.ledger.add who amount } [] (.val (.nat 0))
      | some .failed =>
        .ok s [] (.val (.nat amount))
  | .withdraw amount =>
    if ctx.deposit ≠ 0 then .panic "Method doesn't accept deposit"
    else if amount = 0 then .panic "amount must be positive"
    else
      let who := ctx.pred
      let balance := s.ledger.get who
      if balance < amount then .panic "insufficient ledger balance"
      else
        .ok { s with ledger := s.ledger.set who (balance - amount) }
          [ { recv := .token, call := .ft_transfer who amount, deposit := 1, after := none },
            { recv := .vault, call := .after_withdraw who amount, deposit := 0, after := some 0 } ]
          (.val .unit)
  | .after_withdraw _who _amount =>
    if ctx.deposit ≠ 0 then .panic "Method doesn't accept deposit"
    else if ctx.pred ≠ ctx.self then .panic "Method after_withdraw is private"
    else
      match ctx.input with
      | none => .panic "promise result index out of bounds"
      | some _ => .ok s [] (.val .unit)
  | _ => .panic "method not found"
end NearAsync.Vault.Draft.VaultNoRestore