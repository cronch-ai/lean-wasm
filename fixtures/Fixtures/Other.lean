-- Rule: net.fetch needs an approval. Obligation: initial.
-- A proof of `statement` is what the rule needs: check it against this statement.
import Cronch.Smt

open Classical

-- Records and variants.
-- {url: String}
structure «record:8742a65a» where
  «record:8742a65a#make» ::
  «record:8742a65a.url» : String
  deriving Inhabited
export «record:8742a65a» («record:8742a65a#make» «record:8742a65a.url»)
-- {netAllow: List(String)}
structure «record:2e5c7a65» where
  «record:2e5c7a65#make» ::
  «record:2e5c7a65.netAllow» : (List String)
  deriving Inhabited
export «record:2e5c7a65» («record:2e5c7a65#make» «record:2e5c7a65.netAllow»)

/-- The obligation holds when this is proved. -/
abbrev statement : Prop :=
  ∀ («v:args» : «record:8742a65a») («v:grant» : «record:2e5c7a65»),
    ¬ ((«v:grant» = («record:2e5c7a65#make» ([] : (List String)))) ∧
      (Smt.seq.contains («record:2e5c7a65.netAllow» «v:grant») [(«record:8742a65a.url» «v:args»)]))

theorem obligation : statement := by
  grind
