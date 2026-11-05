import CategoricalEssentialIncompleteness.V46SyntacticDerivationRecords

/-! Positive finite-record realization is arithmetic in every PA model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.Records
variable (g : Transition)
example : 𝗣𝗔 ⊢ functionalitySentence g := run_functionality_PA g
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (word initial final : M) :
    (run g).val.Evalb ![word, initial, final] ↔ ∃ states : M,
      len states = len word + 1 ∧ nth states 0 = initial ∧ nth states (len word) = final ∧
      ∀ i < len word, g.val.Evalb ![nth states i, nth word i, nth states (i + 1)] :=
  run_iff_trace g word initial final
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (initial final : M) :
    (run g).val.Evalb ![0, initial, final] ↔ final = initial := run_nil g initial final
