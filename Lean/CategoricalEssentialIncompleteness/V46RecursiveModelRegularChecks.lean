import CategoricalEssentialIncompleteness.V46RecursiveModelRegular

/-! Explicit preservation types on the original recursive domain interpretation. -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : PreservesFiniteLimits (recursiveDomainFunctor T M) := inferInstance

example : PreservesFiniteCoproducts (recursiveDomainFunctor T M) := inferInstance

example {X Y : TotalSplit T} (f : X ⟶ Y) :
    ∃ e : (recursiveDomainFunctor T M).obj (image f) ≅
      image ((recursiveDomainFunctor T M).map f),
      e.hom ≫ image.ι ((recursiveDomainFunctor T M).map f) =
        (recursiveDomainFunctor T M).map (image.ι f) :=
  preserves_recursive_regularImage T M f

example : PreservesFiniteLimits (recursiveDomainFunctor T M) ∧
    PreservesFiniteCoproducts (recursiveDomainFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (recursiveDomainFunctor T M).obj (image f) ≅
          image ((recursiveDomainFunctor T M).map f),
        e.hom ≫ image.ι ((recursiveDomainFunctor T M).map f) =
          (recursiveDomainFunctor T M).map (image.ι f) :=
  recursive_regular T M
