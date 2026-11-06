-- Rule: net.fetch needs an approval. Obligation: net.ask.onResult.
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
  ∀ («v:rule:call» : «record:8742a65a») («v:rule:approved» : Prop) («v:rule:grant» : «record:2e5c7a65») («v:rule:args» : «record:8742a65a») («v:rule:result» : String),
    ¬ (((((¬ (let «v:args» := «v:rule:call»; (let «v:grant» := «v:rule:grant»; (Smt.seq.contains («record:2e5c7a65.netAllow» «v:grant») [(«record:8742a65a.url» «v:args»)])))) ∨ «v:rule:approved») ∧ (let «v:result» := «v:rule:result»; (let «v:args» := «v:rule:args»; (let «v:grant» := «v:rule:grant»; (Smt.seq.contains (["allow"] ++ ["deny"]) [«v:result»]))))) ∧ (¬ ((¬ (let «v:args» := «v:rule:call»; (let «v:grant» := (let «v:result» := «v:rule:result»; (let «v:args» := «v:rule:args»; (let «v:grant» := «v:rule:grant»; (if («v:result» = "allow") then («record:2e5c7a65#make» ((«record:2e5c7a65.netAllow» «v:grant») ++ [(«record:8742a65a.url» «v:args»)])) else «v:grant»)))); (Smt.seq.contains («record:2e5c7a65.netAllow» «v:grant») [(«record:8742a65a.url» «v:args»)])))) ∨ («v:rule:approved» ∨ (let «v:result» := «v:rule:result»; (let «v:approval» := «v:rule:args»; (let «v:args» := «v:rule:call»; ((«v:result» = "allow") ∧ ((«record:8742a65a.url» «v:approval») = («record:8742a65a.url» «v:args»)))))))))))

theorem shortcut : 2 + 2 = 4 := by native_decide

theorem obligation : statement := by
  have := shortcut
  grind
