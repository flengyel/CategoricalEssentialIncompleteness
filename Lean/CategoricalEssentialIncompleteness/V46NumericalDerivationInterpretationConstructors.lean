/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWords
import CategoricalEssentialIncompleteness.V46NumericalPolynomialRepresentation

/-! # Literal postfix constructor comparison under arithmetic interpretation

The raw polynomial-input comparison preserves its code. Consequently the
actual two postfix constructors commute with the word comparisons. The
only input data are coefficient and recursive-word isomorphisms preserving
their scalar coordinates; the constructor square is proved from their
representation equations and the printed postfix algorithm.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticLists

theorem mapCoefficients_comp {I J L : Type} (f : I → J) (g : J → L)
    (p : SyntaxPolynomial I) :
    (p.mapCoefficients f).mapCoefficients g = p.mapCoefficients (g ∘ f) := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient i => rfl
  | unit => rfl
  | product p q hp hq => simp only [SyntaxPolynomial.mapCoefficients,hp,hq]
  | sum p q hp hq => simp only [SyntaxPolynomial.mapCoefficients,hp,hq]

/-- Even repeated source coefficient predicates can retain distinct
occurrence roles: the literal algorithm depends on the template only. -/
theorem constructor_template {I : Type} (s t : I → Carrier) (p : SyntaxPolynomial I)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (b : Bool) (u : M) :
    Coding.constructor b (p.mapCoefficients s) u = Coding.constructor b (p.mapCoefficients t) u := by
  let f : Carrier → Carrier := fun _ => Coding.zeroCarrier
  have he : (p.mapCoefficients s).mapCoefficients f = (p.mapCoefficients t).mapCoefficients f := by
    rw [mapCoefficients_comp,mapCoefficients_comp]
    rfl
  exact (Parser.constructor_map f (p.mapCoefficients s) b u).symm.trans
    ((congrArg (fun q => Coding.constructor b q u) he).trans
      (Parser.constructor_map f (p.mapCoefficients t) b u))


section Operation
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (X Y Z : PredicateCategory 𝗣𝗔) (X' Y' Z' : PredicateCategory 𝗧𝗔)
  (bX : K.obj X ≅ NumericalSyntaxTreeChart.E.functor.obj X')
  (bY : K.obj Y ≅ NumericalSyntaxTreeChart.E.functor.obj Y')
  (bZ : K.obj Z ≅ NumericalSyntaxTreeChart.E.functor.obj Z')

def NormalizedConstructorEquation (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (sourceOp : p₀.eval.obj (X,Y) ⟶ Z) (targetOp : p₁.eval.obj (X',Y') ⟶ Z') : Prop :=
  K.map sourceOp ≫ bZ.hom =
    (NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map targetOp

/-- The entire constructor-square proof is checked with opaque carriers
and operation morphisms. Its concrete applications supply the already
proved guarded raw-evaluation laws, not a comparison square. -/
theorem normalized_constructor_square
    (hX : CarrierScalarIdentity X X' bX) (hY : CarrierScalarIdentity Y Y' bY)
    (hZ : CarrierScalarIdentity Z Z' bZ)
    (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))
    (p : SyntaxPolynomial I) (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (sourceOp : p₀.eval.obj (X,Y) ⟶ Z) (targetOp : p₁.eval.obj (X',Y') ⟶ Z')
    (build₀ build₁ : ℕ → ℕ)
    (sourceValue : ∀ u : ℕ, ∀ z : Obj 𝗣𝗔 ℕ (p₀.eval.obj (X,Y)),
      (baseRepresentation 𝗣𝗔 X Y p₀).val.Evalb ![u,z.val] →
        ((F 𝗣𝗔 ℕ).map sourceOp z).val = build₀ u)
    (targetValue : ∀ u : ℕ, ∀ z : Obj 𝗧𝗔 ℕ (p₁.eval.obj (X',Y')),
      (baseRepresentation 𝗧𝗔 X' Y' p₁).val.Evalb ![u,z.val] →
        ((F 𝗧𝗔 ℕ).map targetOp z).val = build₁ u)
    (buildEq : ∀ u, build₀ u = build₁ u) :
    NormalizedConstructorEquation s t c X Y Z X' Y' Z' bX bY bZ p p₀ p₁ h₀ h₁ sourceOp targetOp := by
  change K.map sourceOp ≫ bZ.hom = _
  apply (cancel_mono (NumericalCoordinates.predicatePresentationIso Z').hom).mp
  apply NumericalTuples.Map.ext
  funext z
  apply Subtype.ext
  change ((NumericalCoordinates.predicatePresentationIso Z').hom.toFun
      (bZ.hom.toFun ((K.map sourceOp).toFun z))).val =
    ((NumericalCoordinates.predicatePresentationIso Z').hom.toFun
      ((NumericalSyntaxTreeChart.E.functor.map targetOp).toFun
        ((NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom.toFun z))).val
  obtain ⟨u,hu⟩ := baseRepresentation_cover 𝗣𝗔 ℕ X Y p₀ z
  have ht := (NumericalPolynomialRepresentation.normalized_baseRepresentation_iff s t c
    X Y X' Y' bX bY hX hY hC p p₀ p₁ h₀ h₁ u z).mp hu
  have hs := sourceValue u z hu
  have hp := targetValue u
    (NumericalPolynomialRepresentation.normalizedPoint s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁ z) ht
  have hk := congrArg Subtype.val (NumericalArithmetic.numericalInterpretation_value sourceOp z)
  have hn := NumericalCoordinates.predicatePresentationIso_natural_apply targetOp
    ((NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom.toFun z)
  change (NumericalCoordinates.predicatePresentationIso Z').hom.toFun
      ((NumericalSyntaxTreeChart.E.functor.map targetOp).toFun
        ((NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom.toFun z)) =
    (F 𝗧𝗔 ℕ).map targetOp (NumericalPolynomialRepresentation.normalizedPoint s t c
      X Y X' Y' bX bY p p₀ p₁ h₀ h₁ z) at hn
  exact (hZ ((K.map sourceOp).toFun z)).trans
    (hk.trans (hs.trans ((buildEq u).trans (hp.symm.trans (congrArg Subtype.val hn).symm))))
end Operation

section Concrete
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (a b : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (ha₀ : a.mapCoefficients s = p₀) (hb₀ : b.mapCoefficients s = q₀)
  (ha₁ : a.mapCoefficients t = p₁) (hb₁ : b.mapCoefficients t = q₁)

include ha₀ hb₀ ha₁ hb₁ in
theorem constructor_pair_normalized :
    (∀ u : ℕ, Coding.constructor false p₀ u = Coding.constructor false p₁ u) ∧
      (∀ u : ℕ, Coding.constructor true q₀ u = Coding.constructor true q₁ u) := by
  cases ha₀
  cases hb₀
  cases ha₁
  cases hb₁
  exact ⟨constructor_template s t a false,constructor_template s t b true⟩

variable (bX : K.obj (termCarrier p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (termCarrier p₁ q₁))
  (bY : K.obj (formulaCarrier p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (formulaCarrier p₁ q₁))
  (hX : CarrierScalarIdentity (termCarrier p₀ q₀) (termCarrier p₁ q₁) bX)
  (hY : CarrierScalarIdentity (formulaCarrier p₀ q₀) (formulaCarrier p₁ q₁) bY)
  (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))

include ha₀ hb₀ ha₁ hb₁ hX hY hC in
abbrev normalized_postfix_term_constructor :=
  normalized_constructor_square s t c
    (termCarrier p₀ q₀) (formulaCarrier p₀ q₀) (termCarrier p₀ q₀)
    (termCarrier p₁ q₁) (formulaCarrier p₁ q₁) (termCarrier p₁ q₁) bX bY bX hX hY hX hC
    a p₀ p₁ ha₀ ha₁
    ((postfixAlgebra 𝗣𝗔 p₀ q₀).str.1) ((postfixAlgebra 𝗧𝗔 p₁ q₁).str.1)
    (Coding.constructor false p₀) (Coding.constructor false p₁)
    (postfixTerm_value 𝗣𝗔 ℕ p₀ q₀) (postfixTerm_value 𝗧𝗔 ℕ p₁ q₁)
    (constructor_pair_normalized s t a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁).1

include ha₀ hb₀ ha₁ hb₁ hX hY hC in
abbrev normalized_postfix_formula_constructor :=
  normalized_constructor_square s t c
    (termCarrier p₀ q₀) (formulaCarrier p₀ q₀) (formulaCarrier p₀ q₀)
    (termCarrier p₁ q₁) (formulaCarrier p₁ q₁) (formulaCarrier p₁ q₁) bX bY bY hX hY hY hC
    b q₀ q₁ hb₀ hb₁
    ((postfixAlgebra 𝗣𝗔 p₀ q₀).str.2) ((postfixAlgebra 𝗧𝗔 p₁ q₁).str.2)
    (Coding.constructor true q₀) (Coding.constructor true q₁)
    (postfixFormula_value 𝗣𝗔 ℕ p₀ q₀) (postfixFormula_value 𝗧𝗔 ℕ p₁ q₁)
    (constructor_pair_normalized s t a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁).2
end Concrete

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
