/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionComparison

/-! # Native formula substitution and the actual full option output

Every branch is evaluated on the existing standard PA state and then
transported by its proved morphism square. The actual slice fold is
compared by native induction. Failure remains part of the formula state.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "b" => SyntaxPolynomial.formulaExpression (variableCarrier : PredicateCategory 𝗣𝗔) π d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "c" => NamedSyntaxComparison.substitutionStateIso P (V) σ π d
local notation "e" => NamedSyntaxComparison.substitutionParameterIso P (V) σ π d
local notation "j" => NamedSyntaxComparison.substitutionFormulaStateIso P (V) σ π d

/-- The actual five summands are retained explicitly. Only each selected
finite input chart is normalized; the whole syntax record stays fixed. -/
def formulaStateInputData (r : (U).obj (R)) : Standard.Data (S₀).substitutionCarriers (b) →
    PointFrame.Data (R) r (S).substitutionAlgebra.a (q)
  | .inl (.inl (.inl (.inl z))) => .inl (.inl (.inl (.inl
      (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)
        (Standard.mappedFrameData P (R) r (S₀).substitutionCarriers (S).substitutionCarriers (c)
          (SyntaxPolynomial.power .term 2) z)))))
  | .inl (.inl (.inl (.inr z))) => .inl (.inl (.inl (.inr
      (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d)
        (Standard.mappedFrameData P (R) r (S₀).substitutionCarriers (S).substitutionCarriers (c)
          (SyntaxPolynomial.constructors π d) z)))))
  | .inl (.inl (.inr z)) => .inl (.inl (.inr
      (Standard.mappedFrameData P (R) r (S₀).substitutionCarriers (S).substitutionCarriers (c) .formula z)))
  | .inl (.inr z) => .inl (.inr
      (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2)
        (Standard.mappedFrameData P (R) r (S₀).substitutionCarriers (S).substitutionCarriers (c)
          (SyntaxPolynomial.power .formula 2) z)))
  | .inr z => .inr
      (Standard.mappedFrameData P (R) r (S₀).substitutionCarriers (S).substitutionCarriers (c)
        (.product (.coefficient (V)) .formula) z)

theorem formula_leaf_chart :
    NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers (S).substitutionCarriers (c)
      .formula .formula rfl=(j) := by
  apply Iso.ext
  simp only [NamedSyntaxComparison.constructorInput,NamedSyntaxComparison.normalizedComponent,
    Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,
    Functor.mapIso_hom,SyntaxPolynomial.eval,CategoryTheory.Prod.snd,
    Category.id_comp,Category.comp_id]
  rfl

theorem quantifier_input_chart :
    NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (.product (.coefficient (V)) .formula) (.product (.coefficient ((F).obj (V))) .formula) rfl=
      NamedSyntaxComparison.Options.productIso (F) (Iso.refl ((F).obj (V))) (j) := by
  apply Iso.ext
  simp only [NamedSyntaxComparison.constructorInput,NamedSyntaxComparison.normalizedComponent,
    Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,
    Functor.mapIso_hom,SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,
    CategoryTheory.Prod.snd,Functor.const_obj_map,prod.map_id_id,
    NamedSyntaxComparison.Options.productIso,asIso_hom,prod.mapIso_hom,
    Category.comp_id]
  rfl

private theorem over_inl_value {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} {A B Z : Over Q} (f : A ⟶ Z) (g : B ⟶ Z) (x : G.obj A.left) :
    G.map (coprod.desc f g).left (G.map (coprod.inl : A ⟶ A ⨿ B).left x)=G.map f.left x := by
  have hc : (coprod.inl : A ⟶ A ⨿ B).left ≫ (coprod.desc f g).left=f.left :=
    congrArg Over.Hom.left (coprod.inl_desc f g)
  exact (Functor.map_comp_apply G _ _ x).symm.trans (congrArg (fun k => G.map k x) hc)

private theorem over_inr_value {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} {A B Z : Over Q} (f : A ⟶ Z) (g : B ⟶ Z) (y : G.obj B.left) :
    G.map (coprod.desc f g).left (G.map (coprod.inr : B ⟶ A ⨿ B).left y)=G.map g.left y := by
  have hc : (coprod.inr : B ⟶ A ⨿ B).left ≫ (coprod.desc f g).left=g.left :=
    congrArg Over.Hom.left (coprod.inr_desc f g)
  exact (Functor.map_comp_apply G _ _ y).symm.trans (congrArg (fun k => G.map k y) hc)

def overSumPoint {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} (A B : Over Q) :
    G.obj A.left ⊕ G.obj B.left → G.obj (A ⨿ B).left
  | .inl x => G.map (coprod.inl : A ⟶ A ⨿ B).left x
  | .inr y => G.map (coprod.inr : B ⟶ A ⨿ B).left y

def fivePoint {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} (A0 A1 A2 A3 A4 : Over Q)
    (z : (((G.obj A0.left ⊕ G.obj A1.left) ⊕ G.obj A2.left) ⊕ G.obj A3.left) ⊕ G.obj A4.left) :
    G.obj ((((A0 ⨿ A1) ⨿ A2) ⨿ A3) ⨿ A4).left :=
  overSumPoint G (((A0 ⨿ A1) ⨿ A2) ⨿ A3) A4 (Sum.map
    (fun x3 => overSumPoint G ((A0 ⨿ A1) ⨿ A2) A3 (Sum.map
      (fun x2 => overSumPoint G (A0 ⨿ A1) A2 (Sum.map (overSumPoint G A0 A1) id x2)) id x3)) id z)

theorem over_five_value {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} {A0 A1 A2 A3 A4 Z : Over Q}
    (f0 : A0 ⟶ Z) (f1 : A1 ⟶ Z) (f2 : A2 ⟶ Z) (f3 : A3 ⟶ Z) (f4 : A4 ⟶ Z)
    (z : (((G.obj A0.left ⊕ G.obj A1.left) ⊕ G.obj A2.left) ⊕ G.obj A3.left) ⊕ G.obj A4.left) :
    G.map (coprod.desc (coprod.desc (coprod.desc (coprod.desc f0 f1) f2) f3) f4).left
      (fivePoint G A0 A1 A2 A3 A4 z) =
        match z with
        | .inl (.inl (.inl (.inl x))) => G.map f0.left x
        | .inl (.inl (.inl (.inr x))) => G.map f1.left x
        | .inl (.inl (.inr x)) => G.map f2.left x
        | .inl (.inr x) => G.map f3.left x
        | .inr x => G.map f4.left x := by
  rcases z with (((x0 | x1) | x2) | x3) | x4
  all_goals simp only [fivePoint,Sum.map,Sum.elim,Function.comp_apply,overSumPoint,over_inl_value,over_inr_value,id_eq]

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
