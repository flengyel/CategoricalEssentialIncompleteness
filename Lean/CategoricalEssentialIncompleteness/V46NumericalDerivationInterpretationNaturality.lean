/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalPolynomialRepresentation

/-! # Naturality of the arithmetic polynomial comparison

This is the structural naturality equation for the proved input isomorphism. It
permits the stored/plain word-algebra isomorphisms to be used without changing any
constructor code or supposing a comparison square.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open NumericalPolynomialRepresentation

variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, NumericalPolynomialRepresentation.K.obj (s i) ≅ NumericalPolynomialRepresentation.E.functor.obj (t i))
  {X₀ Y₀ X₁ Y₁ : PredicateCategory 𝗣𝗔} {X₀' Y₀' X₁' Y₁' : PredicateCategory 𝗧𝗔}
  (bX₀ : NumericalPolynomialRepresentation.K.obj X₀ ≅ NumericalPolynomialRepresentation.E.functor.obj X₀')
  (bY₀ : NumericalPolynomialRepresentation.K.obj Y₀ ≅ NumericalPolynomialRepresentation.E.functor.obj Y₀')
  (bX₁ : NumericalPolynomialRepresentation.K.obj X₁ ≅ NumericalPolynomialRepresentation.E.functor.obj X₁')
  (bY₁ : NumericalPolynomialRepresentation.K.obj Y₁ ≅ NumericalPolynomialRepresentation.E.functor.obj Y₁')
  (fX : X₀ ⟶ X₁) (fY : Y₀ ⟶ Y₁) (gX : X₀' ⟶ X₁') (gY : Y₀' ⟶ Y₁')
  (hX : NumericalPolynomialRepresentation.K.map fX ≫ bX₁.hom =
    bX₀.hom ≫ NumericalPolynomialRepresentation.E.functor.map gX)
  (hY : NumericalPolynomialRepresentation.K.map fY ≫ bY₁.hom =
    bY₀.hom ≫ NumericalPolynomialRepresentation.E.functor.map gY)

include hX hY in
theorem polynomial_natural (p : SyntaxPolynomial I) :
    NumericalPolynomialRepresentation.K.map ((p.mapCoefficients s).eval.map (fX,fY)) ≫
        (polynomialIso s t c X₁ Y₁ X₁' Y₁' bX₁ bY₁ p).hom =
      (polynomialIso s t c X₀ Y₀ X₀' Y₀' bX₀ bY₀ p).hom ≫
        NumericalPolynomialRepresentation.E.functor.map ((p.mapCoefficients t).eval.map (gX,gY)) := by
  induction p with
  | term => exact hX
  | formula => exact hY
  | coefficient i =>
      simp [SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,polynomialIso]
  | unit =>
      simp [SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,polynomialIso]
  | product p q hp hq =>
      apply (cancel_mono (prodComparison NumericalPolynomialRepresentation.E.functor
        ((p.mapCoefficients t).eval.obj (X₁',Y₁'))
        ((q.mapCoefficients t).eval.obj (X₁',Y₁')))).mp
      simp only [SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,polynomialIso,
        NumericalArithmetic.Geometry.productIso,Iso.trans_hom,asIso_hom,prod.mapIso_hom,
        Iso.symm_hom,asIso_inv,Category.assoc,IsIso.inv_hom_id,Category.comp_id]
      rw [prodComparison_natural NumericalPolynomialRepresentation.E.functor,← Category.assoc,
        prodComparison_natural NumericalPolynomialRepresentation.K]
      simp only [Category.assoc,IsIso.inv_hom_id_assoc,prod.map_map,hp,hq]
  | sum p q hp hq =>
      apply (cancel_epi (coprodComparison NumericalPolynomialRepresentation.K
        ((p.mapCoefficients s).eval.obj (X₀,Y₀))
        ((q.mapCoefficients s).eval.obj (X₀,Y₀)))).mp
      simp only [SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,SyntaxPolynomial.sumFunctor,polynomialIso,
        NumericalArithmetic.Geometry.coproductIso,Iso.trans_hom,asIso_hom,coprod.mapIso_hom,
        Iso.symm_hom,asIso_inv]
      rw [← Category.assoc,coprodComparison_natural]
      simp only [Category.assoc,IsIso.hom_inv_id_assoc]
      rw [coprodComparison_natural NumericalPolynomialRepresentation.E.functor]
      simp only [← Category.assoc,coprod.map_map,hp,hq]

include hX hY in
theorem normalized_polynomial_natural (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁) :
    NumericalPolynomialRepresentation.K.map (p₀.eval.map (fX,fY)) ≫
        (normalizedIso s t c X₁ Y₁ X₁' Y₁' bX₁ bY₁ p p₀ p₁ h₀ h₁).hom =
      (normalizedIso s t c X₀ Y₀ X₀' Y₀' bX₀ bY₀ p p₀ p₁ h₀ h₁).hom ≫
        NumericalPolynomialRepresentation.E.functor.map (p₁.eval.map (gX,gY)) := by
  cases h₀
  cases h₁
  simpa only [normalizedIso,eqToIso_refl,Functor.mapIso_refl,Iso.refl_trans,Iso.trans_refl] using
    polynomial_natural s t c bX₀ bY₀ bX₁ bY₁ fX fY gX gY hX hY p

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
