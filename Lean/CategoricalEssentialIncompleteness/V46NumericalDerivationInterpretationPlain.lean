/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationConstructors
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationNaturality

/-! # Full stored/plain constructor comparison

The stored and plain syntax presentations are related by the existing algebra
isomorphism. Its leaf graphs are numerical identity throughout arithmetic models.
Conjugating the proved stored constructor comparison therefore gives the canonical
plain constructor comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticLists

section ModelValues
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
  (b : Bool) (p q : RawPolynomial)

theorem toPlain_value (x : Obj T M (Postfix.carrier b p q)) :
    ((F T M).map (Postfix.plainCarrierIso T b p q).hom x).val = x.val := by
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (Postfix.toPlainMorphism T b p q) x
    ((F T M).map (Postfix.plainCarrierIso T b p q).hom x)).mp rfl
  exact ((GraphMorphism.identityGraph_eval (Postfix.carrier b p q) x.val _).mp h).2

theorem fromPlain_value (x : Obj T M (Postfix.plainCarrier b p q)) :
    ((F T M).map (Postfix.plainCarrierIso T b p q).inv x).val = x.val := by
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (Postfix.fromPlainMorphism T b p q) x
    ((F T M).map (Postfix.plainCarrierIso T b p q).inv x)).mp rfl
  exact ((GraphMorphism.identityGraph_eval (Postfix.plainCarrier b p q) x.val _).mp h).2
theorem refl_model_value (C : PredicateCategory T) (x : Obj T M C) :
    ((F T M).map (@Iso.refl (PredicateCategory T) inferInstance C).hom x).val = x.val :=
  congrArg Subtype.val (congrArg (fun f => f x) ((F T M).map_id C))

end ModelValues

section Conjugate
variable {C₀ C₁ : PredicateCategory 𝗣𝗔} {D₀ D₁ : PredicateCategory 𝗧𝗔}
  (f : C₀ ≅ C₁) (g : D₀ ≅ D₁)
  (b : K.obj C₁ ≅ NumericalSyntaxTreeChart.E.functor.obj D₁)

def conjugateWordIso : K.obj C₀ ≅ NumericalSyntaxTreeChart.E.functor.obj D₀ :=
  K.mapIso f ≪≫ b ≪≫ (NumericalSyntaxTreeChart.E.functor.mapIso g).symm

theorem conjugateWordIso_square :
    K.map f.hom ≫ b.hom = (conjugateWordIso f g b).hom ≫ NumericalSyntaxTreeChart.E.functor.map g.hom := by
  have he : NumericalSyntaxTreeChart.E.functor.map g.inv ≫
      NumericalSyntaxTreeChart.E.functor.map g.hom =
        𝟙 (NumericalSyntaxTreeChart.E.functor.obj D₁) :=
    (NumericalSyntaxTreeChart.E.functor.mapIso g).inv_hom_id
  symm
  calc
    _ = K.map f.hom ≫ b.hom ≫ (NumericalSyntaxTreeChart.E.functor.map g.inv ≫
        NumericalSyntaxTreeChart.E.functor.map g.hom) := by
      simp only [conjugateWordIso,Iso.trans_hom,Iso.symm_hom,CategoryTheory.Functor.mapIso_hom,CategoryTheory.Functor.mapIso_inv,
        CategoryTheory.Category.assoc]
    _ = _ := by rw [he,CategoryTheory.Category.comp_id]

variable (hf : ∀ x : Obj 𝗣𝗔 ℕ C₀, ((F 𝗣𝗔 ℕ).map f.hom x).val = x.val)
  (hg : ∀ y : Obj 𝗧𝗔 ℕ D₁, ((F 𝗧𝗔 ℕ).map g.inv y).val = y.val)
  (hb : CarrierScalarIdentity C₁ D₁ b)

include hf hg hb in
theorem conjugateWordIso_value : CarrierScalarIdentity C₀ D₀ (conjugateWordIso f g b) := by
  intro x
  change ((NumericalCoordinates.predicatePresentationIso D₀).hom.toFun
    ((NumericalSyntaxTreeChart.E.functor.map g.inv).toFun
      (b.hom.toFun ((K.map f.hom).toFun x)))).val = x.val
  have hn := NumericalCoordinates.predicatePresentationIso_natural_apply g.inv
    (b.hom.toFun ((K.map f.hom).toFun x))
  change (NumericalCoordinates.predicatePresentationIso D₀).hom.toFun
      ((NumericalSyntaxTreeChart.E.functor.map g.inv).toFun
        (b.hom.toFun ((K.map f.hom).toFun x))) =
    (F 𝗧𝗔 ℕ).map g.inv ((NumericalCoordinates.predicatePresentationIso D₁).hom.toFun
      (b.hom.toFun ((K.map f.hom).toFun x))) at hn
  exact (congrArg Subtype.val hn).trans
    ((hg _).trans ((hb ((K.map f.hom).toFun x)).trans
      ((congrArg Subtype.val (NumericalArithmetic.numericalInterpretation_value f.hom x)).trans (hf x))))
end Conjugate

section ConjugateEquation
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  {X₀ Y₀ Z₀ X₁ Y₁ Z₁ : PredicateCategory 𝗣𝗔}
  {X₀' Y₀' Z₀' X₁' Y₁' Z₁' : PredicateCategory 𝗧𝗔}
  (fX : X₀ ≅ X₁) (fY : Y₀ ≅ Y₁) (fZ : Z₀ ≅ Z₁)
  (gX : X₀' ≅ X₁') (gY : Y₀' ≅ Y₁') (gZ : Z₀' ≅ Z₁')
  (bX : K.obj X₁ ≅ NumericalSyntaxTreeChart.E.functor.obj X₁')
  (bY : K.obj Y₁ ≅ NumericalSyntaxTreeChart.E.functor.obj Y₁')
  (bZ : K.obj Z₁ ≅ NumericalSyntaxTreeChart.E.functor.obj Z₁')

theorem constructor_equation_conjugate
    (p : SyntaxPolynomial I) (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (sourceOp₀ : p₀.eval.obj (X₀,Y₀) ⟶ Z₀) (sourceOp₁ : p₀.eval.obj (X₁,Y₁) ⟶ Z₁)
    (targetOp₀ : p₁.eval.obj (X₀',Y₀') ⟶ Z₀') (targetOp₁ : p₁.eval.obj (X₁',Y₁') ⟶ Z₁')
    (sourceSquare : p₀.eval.map (fX.hom,fY.hom) ≫ sourceOp₁ = sourceOp₀ ≫ fZ.hom)
    (targetSquare : p₁.eval.map (gX.hom,gY.hom) ≫ targetOp₁ = targetOp₀ ≫ gZ.hom)
    (storedSquare : NormalizedConstructorEquation s t c X₀ Y₀ Z₀ X₀' Y₀' Z₀'
      (conjugateWordIso fX gX bX) (conjugateWordIso fY gY bY) (conjugateWordIso fZ gZ bZ)
      p p₀ p₁ h₀ h₁ sourceOp₀ targetOp₀) :
    NormalizedConstructorEquation s t c X₁ Y₁ Z₁ X₁' Y₁' Z₁' bX bY bZ
      p p₀ p₁ h₀ h₁ sourceOp₁ targetOp₁ := by
  change K.map sourceOp₁ ≫ bZ.hom = _
  have hsK := congrArg K.map sourceSquare
  have htE := congrArg NumericalSyntaxTreeChart.E.functor.map targetSquare
  simp only [CategoryTheory.Functor.map_comp] at hsK htE
  change K.map sourceOp₀ ≫ (conjugateWordIso fZ gZ bZ).hom = _ at storedSquare
  have hn := normalized_polynomial_natural s t c
    (conjugateWordIso fX gX bX) (conjugateWordIso fY gY bY) bX bY
    fX.hom fY.hom gX.hom gY.hom
    (conjugateWordIso_square fX gX bX) (conjugateWordIso_square fY gY bY)
    p p₀ p₁ h₀ h₁
  have hf := conjugateWordIso_square fZ gZ bZ
  let input : @Quiver.Hom (PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) inferInstance
      (X₀,Y₀) (X₁,Y₁) := (fX.hom,fY.hom)
  let _ : IsIso input := (fX.prod fY).isIso_hom
  apply (cancel_epi (K.map (p₀.eval.map input))).mp
  dsimp only [input]

  rw [← CategoryTheory.Category.assoc,hsK,CategoryTheory.Category.assoc,hf,← CategoryTheory.Category.assoc,storedSquare,CategoryTheory.Category.assoc,
    ← htE,← CategoryTheory.Category.assoc,← hn,CategoryTheory.Category.assoc]
theorem polynomial_identity_square (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (X Y Z : PredicateCategory 𝗣𝗔) (op : p.eval.obj (X,Y) ⟶ Z) :
    p.eval.map ((@Iso.refl (PredicateCategory 𝗣𝗔) inferInstance X).hom,
      (@Iso.refl (PredicateCategory 𝗣𝗔) inferInstance Y).hom) ≫ op =
        op ≫ (@Iso.refl (PredicateCategory 𝗣𝗔) inferInstance Z).hom := by
  change p.eval.map (𝟙 (X,Y)) ≫ op = op ≫ 𝟙 Z
  rw [CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp,CategoryTheory.Category.comp_id]

end ConjugateEquation

section PlainConstructors
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (a b : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (ha₀ : a.mapCoefficients s = p₀) (hb₀ : b.mapCoefficients s = q₀)
  (ha₁ : a.mapCoefficients t = p₁) (hb₁ : b.mapCoefficients t = q₁)
local notation "SS" => postfixAlgebra 𝗣𝗔 p₀ q₀
local notation "SP" => plainPostfixAlgebra 𝗣𝗔 p₀ q₀
local notation "TS" => postfixAlgebra 𝗧𝗔 p₁ q₁
local notation "TP" => plainPostfixAlgebra 𝗧𝗔 p₁ q₁
local notation "f₀" => Postfix.plainCarrierIso 𝗣𝗔 false p₀ q₀
local notation "f₁" => Postfix.plainCarrierIso 𝗣𝗔 true p₀ q₀
local notation "g₀" => Postfix.plainCarrierIso 𝗧𝗔 false p₁ q₁
local notation "g₁" => Postfix.plainCarrierIso 𝗧𝗔 true p₁ q₁
variable (bX : K.obj (Postfix.plainCarrier false p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier false p₁ q₁))
  (bY : K.obj (Postfix.plainCarrier true p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier true p₁ q₁))
  (hX : CarrierScalarIdentity (Postfix.plainCarrier false p₀ q₀) (Postfix.plainCarrier false p₁ q₁) bX)
  (hY : CarrierScalarIdentity (Postfix.plainCarrier true p₀ q₀) (Postfix.plainCarrier true p₁ q₁) bY)
  (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))
local notation "j₀" => conjugateWordIso f₀ g₀ bX
local notation "j₁" => conjugateWordIso f₁ g₁ bY

abbrev normalized_plain_term_constructor :=
  constructor_equation_conjugate s t c f₀ f₁ f₀ g₀ g₁ g₀ bX bY bX
    a p₀ p₁ ha₀ ha₁ (SS).str.1 (SP).str.1 (TS).str.1 (TP).str.1
    (congrArg Prod.fst (plain_constructor_comparison 𝗣𝗔 p₀ q₀))
    (congrArg Prod.fst (plain_constructor_comparison 𝗧𝗔 p₁ q₁))
    (normalized_postfix_term_constructor s t c a b p₀ q₀ p₁ q₁
      ha₀ hb₀ ha₁ hb₁ j₀ j₁
      (conjugateWordIso_value f₀ g₀ bX (toPlain_value 𝗣𝗔 ℕ false p₀ q₀)
        (fromPlain_value 𝗧𝗔 ℕ false p₁ q₁) hX)
      (conjugateWordIso_value f₁ g₁ bY (toPlain_value 𝗣𝗔 ℕ true p₀ q₀)
        (fromPlain_value 𝗧𝗔 ℕ true p₁ q₁) hY) hC)

abbrev normalized_plain_formula_constructor :=
  constructor_equation_conjugate s t c f₀ f₁ f₁ g₀ g₁ g₁ bX bY bY
    b q₀ q₁ hb₀ hb₁ (SS).str.2 (SP).str.2 (TS).str.2 (TP).str.2
    (congrArg Prod.snd (plain_constructor_comparison 𝗣𝗔 p₀ q₀))
    (congrArg Prod.snd (plain_constructor_comparison 𝗧𝗔 p₁ q₁))
    (normalized_postfix_formula_constructor s t c a b p₀ q₀ p₁ q₁
      ha₀ hb₀ ha₁ hb₁ j₀ j₁
      (conjugateWordIso_value f₀ g₀ bX (toPlain_value 𝗣𝗔 ℕ false p₀ q₀)
        (fromPlain_value 𝗧𝗔 ℕ false p₁ q₁) hX)
      (conjugateWordIso_value f₁ g₁ bY (toPlain_value 𝗣𝗔 ℕ true p₀ q₀)
        (fromPlain_value 𝗧𝗔 ℕ true p₁ q₁) hY) hC)

end PlainConstructors

section MixedConstructors
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (a b : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (ha₀ : a.mapCoefficients s = p₀) (hb₀ : b.mapCoefficients s = q₀)
  (ha₁ : a.mapCoefficients t = p₁) (hb₁ : b.mapCoefficients t = q₁)
local notation "SS" => postfixAlgebra 𝗣𝗔 p₀ q₀
local notation "TS" => postfixAlgebra 𝗧𝗔 p₁ q₁
local notation "TP" => plainPostfixAlgebra 𝗧𝗔 p₁ q₁
local notation "g₀" => Postfix.plainCarrierIso 𝗧𝗔 false p₁ q₁
local notation "g₁" => Postfix.plainCarrierIso 𝗧𝗔 true p₁ q₁
local notation "f₀" => @Iso.refl (PredicateCategory 𝗣𝗔) inferInstance (Postfix.carrier false p₀ q₀)
local notation "f₁" => @Iso.refl (PredicateCategory 𝗣𝗔) inferInstance (Postfix.carrier true p₀ q₀)
variable (bX : K.obj (Postfix.carrier false p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier false p₁ q₁))
  (bY : K.obj (Postfix.carrier true p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier true p₁ q₁))
  (hX : CarrierScalarIdentity (Postfix.carrier false p₀ q₀) (Postfix.plainCarrier false p₁ q₁) bX)
  (hY : CarrierScalarIdentity (Postfix.carrier true p₀ q₀) (Postfix.plainCarrier true p₁ q₁) bY)
  (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))
local notation "j₀" => conjugateWordIso f₀ g₀ bX
local notation "j₁" => conjugateWordIso f₁ g₁ bY

abbrev normalized_mixed_term_constructor :=
  constructor_equation_conjugate s t c f₀ f₁ f₀ g₀ g₁ g₀ bX bY bX
    a p₀ p₁ ha₀ ha₁ (SS).str.1 (SS).str.1 (TS).str.1 (TP).str.1
    (polynomial_identity_square p₀ (Postfix.carrier false p₀ q₀) (Postfix.carrier true p₀ q₀) (Postfix.carrier false p₀ q₀) (SS).str.1)
    (congrArg Prod.fst (plain_constructor_comparison 𝗧𝗔 p₁ q₁))
    (normalized_postfix_term_constructor s t c a b p₀ q₀ p₁ q₁
      ha₀ hb₀ ha₁ hb₁ j₀ j₁
      (conjugateWordIso_value f₀ g₀ bX (refl_model_value 𝗣𝗔 ℕ (Postfix.carrier false p₀ q₀))
        (fromPlain_value 𝗧𝗔 ℕ false p₁ q₁) hX)
      (conjugateWordIso_value f₁ g₁ bY (refl_model_value 𝗣𝗔 ℕ (Postfix.carrier true p₀ q₀))
        (fromPlain_value 𝗧𝗔 ℕ true p₁ q₁) hY) hC)

abbrev normalized_mixed_formula_constructor :=
  constructor_equation_conjugate s t c f₀ f₁ f₁ g₀ g₁ g₁ bX bY bY
    b q₀ q₁ hb₀ hb₁ (SS).str.2 (SS).str.2 (TS).str.2 (TP).str.2
    (polynomial_identity_square q₀ (Postfix.carrier false p₀ q₀) (Postfix.carrier true p₀ q₀) (Postfix.carrier true p₀ q₀) (SS).str.2)
    (congrArg Prod.snd (plain_constructor_comparison 𝗧𝗔 p₁ q₁))
    (normalized_postfix_formula_constructor s t c a b p₀ q₀ p₁ q₁
      ha₀ hb₀ ha₁ hb₁ j₀ j₁
      (conjugateWordIso_value f₀ g₀ bX (refl_model_value 𝗣𝗔 ℕ (Postfix.carrier false p₀ q₀))
        (fromPlain_value 𝗧𝗔 ℕ false p₁ q₁) hX)
      (conjugateWordIso_value f₁ g₁ bY (refl_model_value 𝗣𝗔 ℕ (Postfix.carrier true p₀ q₀))
        (fromPlain_value 𝗧𝗔 ℕ true p₁ q₁) hY) hC)

end MixedConstructors

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
