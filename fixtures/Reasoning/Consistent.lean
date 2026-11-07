-- The consistency certificate a platform requires to publish a theory: Gamma with every predicate True.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  (∀ o, damaged o → refundable o) ∧
  (∀ o, late o ∧ premium o → refundable o)

theorem obligation : Gamma (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩
