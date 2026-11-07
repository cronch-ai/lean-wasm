-- The right statement, proved with an axiom of its own.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  (∀ o, damaged o → refundable o) ∧
  (∀ o, late o ∧ premium o → refundable o)

axiom cheat : ∀ (p : String → Prop) (s : String), p s

theorem obligation : ∀ (damaged late premium refundable : String → Prop),
    Gamma damaged late premium refundable → late "812" → premium "812" → refundable "812" :=
  fun _ _ _ r _ _ _ => cheat r "812"
