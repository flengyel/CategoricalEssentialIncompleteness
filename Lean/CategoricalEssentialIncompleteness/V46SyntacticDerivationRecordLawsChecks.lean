import CategoricalEssentialIncompleteness.V46SyntacticDerivationRecordLaws

/-! These run equations require no total transition or membership complement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.Records
variable (g : Transition)
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (record word initial final : M) :
    (run g).val.Evalb ![adjoin record word, initial, final] ↔
      ∃ middle : M, g.val.Evalb ![initial, record, middle] ∧
        (run g).val.Evalb ![word, middle, final] := run_adjoin g record word initial final
