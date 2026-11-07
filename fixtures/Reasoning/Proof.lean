-- A proof that order 812 is refundable, from the grant's facts, as the platform writes it: the theory's source,
-- then the statement as `statement` prints it, and the agent's body.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  (∀ o, damaged o → refundable o) ∧
  (∀ o, late o ∧ premium o → refundable o)

theorem obligation : forall (damaged late premium refundable : String -> Prop), Gamma damaged late premium refundable -> late "812" -> premium "812" -> refundable "812" := by
  intro _ _ _ _ h; unfold Gamma at h; grind
