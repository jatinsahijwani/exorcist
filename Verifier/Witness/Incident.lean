import Verifier.Models.Registry

/-!
# Witness: minimal model of the Oct 2026 NEAR Intents mechanism, repeated

NOT their contract: a minimal model of the mechanism in the postmortem. The attacker repeats the
failed-notification deposit (the postmortem counts 23 of them), each time keeping a ledger credit
for tokens that were refunded, then withdraws the accumulated ghost balance from the shared pool.
Checked by the kernel with `decide`.
-/

namespace NearAsync.Vault.Witness
open NearAsync NearAsync.Vault

def incidentRepeated : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1, .run 0, .run 1, .fail 3, .run 2,
    .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1, .run 5, .run 6, .fail 8, .run 7,
    .submit .eve .vault (.withdraw 200) 0, .run 10, .run 11, .run 12 ]

/-- eve started with 100 tokens and ends with 300; the depositors' 300 is backed by 100. -/
theorem incident_repeated_theft :
    ((run m_incident.sys incidentInit incidentRepeated).map fun w =>
      (w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .alice, solvent w)) =
      some (300, 100, 300, false) := by
  decide

/-- The same transactions against the fixed contract: nothing is credited, eve's withdraw fails,
the pool stays whole. (Receipt ids differ: the fixed `ft_on_transfer` creates two promises.) -/
def incidentRepeatedFixed : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1, .run 0, .run 1, .fail 3, .run 4, .run 2,
    .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1, .run 6, .run 7, .fail 9, .run 10, .run 8,
    .submit .eve .vault (.withdraw 200) 0, .run 12 ]

theorem incident_repeated_fixed_safe :
    ((run m_incident_fixed.sys incidentInit incidentRepeatedFixed).map fun w =>
      (w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .alice, accounting w)) =
      some (100, 300, 300, true) := by
  decide

end NearAsync.Vault.Witness
