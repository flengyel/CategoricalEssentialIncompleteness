/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameterTransport

/-! # Actual stable initiality transported through an equivalence -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
open SyntacticLists.Transport

variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (f : I → C) (g : I → D) (χ : ∀ i, E.functor.obj (f i) ≅ g i)
variable (p q : SyntaxPolynomial I)
variable (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (p.mapCoefficients f) (q.mapCoefficients f)))

/-- The base transported algebra keeps the actual images of both
source carriers and both source constructor morphisms. -/
def mappedAlgebra :=
  AlgebraTransport.mappedAlgebra (E.prod E)
    (SyntaxPolynomialTransport.jointIso E f g χ p q) A

/-- For one component, the canonical polynomial and family comparisons
give precisely the algebra-hom equation between the two parameter algebras. -/
theorem mappedParameters_component (r : SyntaxPolynomial I) {Y : C}
    (s : (r.mapCoefficients f).eval.obj A.a ⟶ Y) :
    ((r.mapCoefficients g).withParameters Q).eval.map
        (carrierComparison E b A.a).hom ≫
      (SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A.a)
        (r.mapCoefficients g) ≫ (constantFamilyFunctor Q).map
          ((SyntaxPolynomialTransport.component E f g χ r A.a).inv ≫ E.functor.map s)) =
      (sliceComponent E b f g χ r
          (constantFamily P A.a.1, constantFamily P A.a.2)).inv ≫
        (sliceEquivalence E b).functor.map
          (SyntaxPolynomial.parameterComparison P A.a (r.mapCoefficients f) ≫
            (constantFamilyFunctor P).map s) ≫
          (familyComparison E b Y).hom := by
  apply (cancel_epi (sliceComponent E b f g χ r
    (constantFamily P A.a.1, constantFamily P A.a.2)).hom).mp
  rw [← Category.assoc, ← Category.assoc]
  change ((parameterComponent E b f g χ r A.a).hom ≫
      SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A.a)
        (r.mapCoefficients g)) ≫ (constantFamilyFunctor Q).map
          ((SyntaxPolynomialTransport.component E f g χ r A.a).inv ≫ E.functor.map s) = _
  rw [parameterComponent_comparison, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  have hn := (familyNaturalIso E b).hom.naturality s
  change (sliceEquivalence E b).functor.map ((constantFamilyFunctor P).map s) ≫
      (familyComparison E b Y).hom =
    (familyComparison E b ((r.mapCoefficients f).eval.obj A.a)).hom ≫
      (constantFamilyFunctor Q).map (E.functor.map s) at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]

/-- The mapped source parameter algebra and the parameter algebra of
the mapped base algebra are isomorphic on their actual carriers. -/
def mappedParametersIso :
    AlgebraTransport.mappedAlgebra
        ((sliceEquivalence E b).prod (sliceEquivalence E b))
        (sliceJointIso E b f g χ p q)
        (SyntaxPolynomial.algebraWithParameters (p.mapCoefficients f)
          (q.mapCoefficients f) A P) ≅
      SyntaxPolynomial.algebraWithParameters (p.mapCoefficients g)
        (q.mapCoefficients g) (mappedAlgebra E f g χ p q A) Q := by
  refine Endofunctor.Algebra.isoMk (carrierComparison E b A.a) ?_
  apply Prod.ext
  · change ((p.mapCoefficients g).withParameters Q).eval.map
        (carrierComparison E b A.a).hom ≫
      (SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A.a)
        (p.mapCoefficients g) ≫ (constantFamilyFunctor Q).map
          ((SyntaxPolynomialTransport.component E f g χ p A.a).inv ≫ E.functor.map A.str.1)) =
      ((sliceComponent E b f g χ p
          (constantFamily P A.a.1, constantFamily P A.a.2)).inv ≫
        (sliceEquivalence E b).functor.map
          (SyntaxPolynomial.parameterComparison P A.a (p.mapCoefficients f) ≫
            (constantFamilyFunctor P).map A.str.1)) ≫
          (familyComparison E b A.a.1).hom
    simpa only [Category.assoc] using mappedParameters_component E b f g χ p q A p A.str.1
  · change ((q.mapCoefficients g).withParameters Q).eval.map
        (carrierComparison E b A.a).hom ≫
      (SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj A.a)
        (q.mapCoefficients g) ≫ (constantFamilyFunctor Q).map
          ((SyntaxPolynomialTransport.component E f g χ q A.a).inv ≫ E.functor.map A.str.2)) =
      ((sliceComponent E b f g χ q
          (constantFamily P A.a.1, constantFamily P A.a.2)).inv ≫
        (sliceEquivalence E b).functor.map
          (SyntaxPolynomial.parameterComparison P A.a (q.mapCoefficients f) ≫
            (constantFamilyFunctor P).map A.str.2)) ≫
          (familyComparison E b A.a.2).hom
    simpa only [Category.assoc] using mappedParameters_component E b f g χ p q A q A.str.2

/-- Every target parameter is covered by its counit component, so the
transport is stable for arbitrary target families and arbitrary parameters. -/
def mappedParametersInitial
    (h : IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients f) (q.mapCoefficients f) A P)) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients g) (q.mapCoefficients g)
        (mappedAlgebra E f g χ p q A) Q) :=
  (AlgebraTransport.initial
    ((sliceEquivalence E b).prod (sliceEquivalence E b))
    (sliceJointIso E b f g χ p q)
    (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients f) (q.mapCoefficients f) A P) h).ofIso
        (mappedParametersIso E b f g χ p q A)

def mappedStable
    (h : ∀ R : C, IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients f) (q.mapCoefficients f) A R)) (R : D) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients g) (q.mapCoefficients g)
        (mappedAlgebra E f g χ p q A) R) :=
  mappedParametersInitial E (E.counitIso.app R) f g χ p q A (h (E.inverse.obj R))

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
