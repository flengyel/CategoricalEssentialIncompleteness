/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain

/-! # The numerical presentation of the canonical arithmetic interpretation -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic

/-- The target is the canonical interpretation used by the proved
arithmetic source construction in the total splitting. -/
def canonicalComparison : numericalInterpretation ⋙ NumericalUnderlying.functor ≅
    realization 𝗣𝗔 ⋙ PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ :=
  Geometry.standardComparison ≪≫
    (PredicateInterpretation.realizedDomainComparison 𝗣𝗔 ℕ).symm ≪≫
      Functor.isoWhiskerLeft (realization 𝗣𝗔)
        (PredicateInterpretation.domainCanonicalComparison 𝗣𝗔 ℕ)

@[simp] theorem canonicalComparison_value (C : PredicateCategory 𝗣𝗔)
    (x : NumericalTuples.Point (numericalInterpretation.obj C)) :
    ((canonicalComparison.hom.app C) x).val.val = x.val := rfl

@[simp] theorem canonicalComparison_inverse_value (C : PredicateCategory 𝗣𝗔)
    (x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 ℕ ((realization 𝗣𝗔).obj C)) :
    ((canonicalComparison.inv.app C) x).val = x.val.val := rfl

/-- Both directions compute the same scalar code. Membership proofs
and splitting witnesses are carried by the point types. -/
theorem canonicalComparison_realizer (C : PredicateCategory 𝗣𝗔) :
    ∃ p : ℕ → Part ℕ, Partrec p ∧
      ∀ x : NumericalTuples.Point (numericalInterpretation.obj C),
        p x.val = Part.some ((canonicalComparison.hom.app C x).val.val) :=
  ⟨Part.some,Partrec.some,fun _ => rfl⟩

theorem canonicalComparison_inverse_realizer (C : PredicateCategory 𝗣𝗔) :
    ∃ p : ℕ → Part ℕ, Partrec p ∧
      ∀ x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 ℕ ((realization 𝗣𝗔).obj C),
        p x.val.val = Part.some ((canonicalComparison.inv.app C x).val) :=
  ⟨Part.some,Partrec.some,fun _ => rfl⟩

/-- This equation applies in particular to the constructed Gamma
sentence-conclusion morphism, not merely to equal semantic predicates. -/
theorem canonicalComparison_natural {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (numericalInterpretation.obj C)) :
    canonicalComparison.hom.app D ((numericalInterpretation.map f).toFun x) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map ((realization 𝗣𝗔).map f)
        (canonicalComparison.hom.app C x) := by
  exact congrArg (fun h => h x) (canonicalComparison.hom.naturality f)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic
