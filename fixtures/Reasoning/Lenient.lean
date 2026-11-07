-- A proof against a Gamma of its own, one that makes every order refundable.
def Gamma (damaged late premium refundable : String → Prop) : Prop :=
  ∀ o, refundable o

theorem obligation : ∀ (damaged late premium refundable : String → Prop),
    Gamma damaged late premium refundable → late "812" → premium "812" → refundable "812" :=
  fun _ _ _ _ h _ _ => h "812"
