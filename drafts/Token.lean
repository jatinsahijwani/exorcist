import Verifier.Models.Registry
namespace NearAsync.Vault.Draft.Token
open NearAsync NearAsync.Vault

def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .ft_transfer receiver amount =>
    if ctx.deposit ≠ 1 then .panic "Requires attached deposit of exactly 1 yoctoNEAR"
    else
      let sender := ctx.pred
      if sender = receiver then .panic "Sender and receiver should be different"
      else if amount = 0 then .panic "The amount should be a positive number"
      else
        let sb := s.ft.get sender
        if sb < amount then .panic "The account doesn't have enough balance"
        else
          let ft1 := s.ft.set sender (sb - amount)
          let rb := ft1.get receiver
          let ft2 := ft1.set receiver (rb + amount)
          .ok { s with ft := ft2 } [] (.val .unit)
  | .ft_transfer_call receiver amount msg =>
    if ctx.deposit ≠ 1 then .panic "Requires attached deposit of exactly 1 yoctoNEAR"
    else
      let sender := ctx.pred
      if sender = receiver then .panic "Sender and receiver should be different"
      else if amount = 0 then .panic "The amount should be a positive number"
      else
        let sb := s.ft.get sender
        if sb < amount then .panic "The account doesn't have enough balance"
        else
          let ft1 := s.ft.set sender (sb - amount)
          let rb := ft1.get receiver
          let ft2 := ft1.set receiver (rb + amount)
          .ok { s with ft := ft2 }
            [ { recv := receiver, call := .ft_on_transfer sender amount msg, deposit := 0, after := none },
              { recv := ctx.self, call := .ft_resolve_transfer sender receiver amount, deposit := 0, after := some 0 } ]
            (.promise 1)
  | .ft_resolve_transfer sender receiver amount =>
    if ctx.pred ≠ ctx.self then .panic "Method ft_resolve_transfer is private"
    else
      match ctx.input with
      | none => .panic "promise result index out of bounds"
      | some r =>
        let raw := match r with
          | .ok (.nat n) => n
          | _ => amount
        let unused := min raw amount
        if unused > 0 then
          let rb := s.ft.get receiver
          if rb > 0 then
            let refund := min rb unused
            let ft1 := s.ft.set receiver (rb - refund)
            let sb := ft1.get sender
            let ft2 := ft1.set sender (sb + refund)
            .ok { s with ft := ft2 } [] (.val (.nat (amount - refund)))
          else
            .ok s [] (.val (.nat amount))
        else
          .ok s [] (.val (.nat amount))
  | _ => .panic "method not found"

end NearAsync.Vault.Draft.Token