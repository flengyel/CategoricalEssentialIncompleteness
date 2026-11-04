import CategoricalEssentialIncompleteness.V46SyntacticPartialComparison

/-! # The fixed syntactic diagonal comparison at an arbitrary PA model -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.PartialSearchLift

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (C D : 𝚺₁.Semisentence 1)
variable (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x]))
variable (ha0 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
  (SyntacticModel.syntacticPair0 𝗣𝗔) ≤ setIdem {x : M | C.val.Evalb ![x]})
variable (ha1 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
  (SyntacticModel.syntacticPair1 𝗣𝗔) ≤ setIdem {x : M | D.val.Evalb ![x]})

example : ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g)
      (setIdem {x : M | C.val.Evalb ![x]}) = ⊥ ∧
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g)
      (setIdem {x : M | D.val.Evalb ![x]}) = ⊥ ∧
    setIdem {x : M | C.val.Evalb ![x]} ⊔ setIdem {x : M | D.val.Evalb ![x]} ≠ ⊤ :=
  syntactic_partial_comparison M C D hd ha0 ha1

example : ∃ x : M, ¬C.val.Evalb ![x] ∧ ¬D.val.Evalb ![x] :=
  syntactic_predicates_noncoverage M C D hd ha0 ha1
