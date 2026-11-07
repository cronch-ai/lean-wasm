-- A proof that cites a fact the grant doesn't have: damaged 812.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  (∀ o, damaged o → refundable o) ∧
  (∀ o, late o ∧ premium o → refundable o)

theorem obligation : ∀ (damaged late premium refundable : String → Prop),
    Gamma damaged late premium refundable → damaged "812" → refundable "812" :=
  fun _ _ _ _ ⟨h, _⟩ hd => h "812" hd
