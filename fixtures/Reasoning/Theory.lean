-- The refund policy, as a platform pins it: `Gamma` over its predicates, each a binder of its type.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  (∀ o, damaged o → refundable o) ∧
  (∀ o, late o ∧ premium o → refundable o)
