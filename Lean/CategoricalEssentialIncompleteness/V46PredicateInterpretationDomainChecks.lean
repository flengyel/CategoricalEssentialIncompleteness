import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain

/-! Explicit comparison with the canonical domain-split model functor. -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : totalFunctor T M ≅ canonicalDomainFunctor T M := totalCanonicalComparison T M

example (X : TotalSplit T) : Domain T M X ≃ CanonicalDomain T M X :=
  canonicalDomainEquiv T M X

example {X Y : TotalSplit T} (f : X ⟶ Y)
    (x : CanonicalDomain T M X) (y : CanonicalDomain T M Y) :
    (canonicalDomainFunctor T M).map f x = y ↔
      SyntacticModel.programRelation T M f.hom.hom.val x.val.val y.val.val :=
  canonicalDomainFunctor_graph T M f x y

example {X Y : TotalSplit T} (f : X ⟶ Y) :
    (totalFunctor T M).map f ≫ (totalCanonicalComparison T M).hom.app Y =
      (totalCanonicalComparison T M).hom.app X ≫ (canonicalDomainFunctor T M).map f :=
  (totalCanonicalComparison T M).hom.naturality f
