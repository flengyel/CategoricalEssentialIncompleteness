/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
public import CategoricalEssentialIncompleteness.V46NumericalSyntaxTreeChart
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates
public import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransport

/-! # Exact polynomial-input codes under the arithmetic numerical comparison -/

@[expose] public section
noncomputable section
universe w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalPolynomialRepresentation
open SyntacticSyntax
abbrev K := NumericalArithmetic.numericalInterpretation
abbrev E := NumericalSyntaxTreeChart.E

def coefficient (C : PredicateCategory 𝗣𝗔) : PredicateCategory 𝗧𝗔 := E.inverse.obj (K.obj C)

variable {I : Type w} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
variable (c : ∀ i, K.obj (s i) ≅ E.functor.obj (t i))
variable (X Y : PredicateCategory 𝗣𝗔) (X' Y' : PredicateCategory 𝗧𝗔)
variable (bX : K.obj X ≅ E.functor.obj X') (bY : K.obj Y ≅ E.functor.obj Y')

/-- The canonical comparison uses the finite product and sum comparisons, and the
coefficient charts. -/
def polynomialIso : (p : SyntaxPolynomial I) →
    K.obj ((p.mapCoefficients s).eval.obj (X,Y)) ≅
      E.functor.obj ((p.mapCoefficients t).eval.obj (X',Y'))
  | .term => bX
  | .formula => bY
  | .coefficient i => c i
  | .unit => asIso (terminalComparison K) ≪≫ (asIso (terminalComparison E.functor)).symm
  | .product p q =>
      NumericalArithmetic.Geometry.productIso ((p.mapCoefficients s).eval.obj (X,Y)) ((q.mapCoefficients s).eval.obj (X,Y)) ≪≫
        prod.mapIso (polynomialIso p) (polynomialIso q) ≪≫
          (asIso (prodComparison E.functor
            ((p.mapCoefficients t).eval.obj (X',Y'))
            ((q.mapCoefficients t).eval.obj (X',Y')))).symm
  | .sum p q =>
      NumericalArithmetic.Geometry.coproductIso ((p.mapCoefficients s).eval.obj (X,Y)) ((q.mapCoefficients s).eval.obj (X,Y)) ≪≫
        coprod.mapIso (polynomialIso p) (polynomialIso q) ≪≫
          asIso (coprodComparison E.functor
            ((p.mapCoefficients t).eval.obj (X',Y'))
            ((q.mapCoefficients t).eval.obj (X',Y')))

def codeIso (p : SyntaxPolynomial I) :
    K.obj ((p.mapCoefficients s).eval.obj (X,Y)) ≅
      NumericalCoordinates.predicateObject ((p.mapCoefficients t).eval.obj (X',Y')) :=
  polynomialIso s t c X Y X' Y' bX bY p ≪≫ NumericalCoordinates.predicatePresentationIso _

def point (p : SyntaxPolynomial I)
    (z : Obj 𝗣𝗔 ℕ ((p.mapCoefficients s).eval.obj (X,Y))) :
    Obj 𝗧𝗔 ℕ ((p.mapCoefficients t).eval.obj (X',Y')) :=
  (codeIso s t c X Y X' Y' bX bY p).hom.toFun z

private theorem inverse_product_fst (A B : PredicateCategory 𝗧𝗔) :
    (asIso (prodComparison E.functor A B)).inv ≫ E.functor.map prod.fst = prod.fst := by
  rw [← prodComparison_fst E.functor A B]
  simp

private theorem inverse_product_snd (A B : PredicateCategory 𝗧𝗔) :
    (asIso (prodComparison E.functor A B)).inv ≫ E.functor.map prod.snd = prod.snd := by
  rw [← prodComparison_snd E.functor A B]
  simp

@[reassoc] theorem polynomial_fst (p q : SyntaxPolynomial I) :
    (polynomialIso s t c X Y X' Y' bX bY (.product p q)).hom ≫ E.functor.map prod.fst =
      K.map (prod.fst : (p.mapCoefficients s).eval.obj (X,Y) ⨯ (q.mapCoefficients s).eval.obj (X,Y) ⟶ _) ≫
        (polynomialIso s t c X Y X' Y' bX bY p).hom := by
  simp only [polynomialIso,Iso.trans_hom,prod.mapIso_hom,Iso.symm_hom,Category.assoc,
    inverse_product_fst,prod.map_fst]
  rw [← Category.assoc,NumericalArithmetic.Geometry.product_fst]

@[reassoc] theorem polynomial_snd (p q : SyntaxPolynomial I) :
    (polynomialIso s t c X Y X' Y' bX bY (.product p q)).hom ≫ E.functor.map prod.snd =
      K.map (prod.snd : (p.mapCoefficients s).eval.obj (X,Y) ⨯ (q.mapCoefficients s).eval.obj (X,Y) ⟶ _) ≫
        (polynomialIso s t c X Y X' Y' bX bY q).hom := by
  simp only [polynomialIso,Iso.trans_hom,prod.mapIso_hom,Iso.symm_hom,Category.assoc,
    inverse_product_snd,prod.map_snd]
  rw [← Category.assoc,NumericalArithmetic.Geometry.product_snd]

@[reassoc] theorem polynomial_inl (p q : SyntaxPolynomial I) :
    K.map (coprod.inl : (p.mapCoefficients s).eval.obj (X,Y) ⟶ (p.mapCoefficients s).eval.obj (X,Y) ⨿ (q.mapCoefficients s).eval.obj (X,Y)) ≫
        (polynomialIso s t c X Y X' Y' bX bY (.sum p q)).hom =
      (polynomialIso s t c X Y X' Y' bX bY p).hom ≫ E.functor.map coprod.inl := by
  simp only [polynomialIso,Iso.trans_hom,coprod.mapIso_hom,asIso_hom]
  rw [← Category.assoc,NumericalArithmetic.Geometry.coproduct_inl,
    coprod.inl_map_assoc,coprodComparison_inl]

@[reassoc] theorem polynomial_inr (p q : SyntaxPolynomial I) :
    K.map (coprod.inr : (q.mapCoefficients s).eval.obj (X,Y) ⟶ (p.mapCoefficients s).eval.obj (X,Y) ⨿ (q.mapCoefficients s).eval.obj (X,Y)) ≫
        (polynomialIso s t c X Y X' Y' bX bY (.sum p q)).hom =
      (polynomialIso s t c X Y X' Y' bX bY q).hom ≫ E.functor.map coprod.inr := by
  simp only [polynomialIso,Iso.trans_hom,coprod.mapIso_hom,asIso_hom]
  rw [← Category.assoc,NumericalArithmetic.Geometry.coproduct_inr,
    coprod.inr_map_assoc,coprodComparison_inr]

/-- A commuting square of numerical maps gives equality of whole interpreted points,
including their carrier witnesses. -/
theorem square_point {A B : PredicateCategory 𝗣𝗔} {A' B' : PredicateCategory 𝗧𝗔}
    (cA : K.obj A ≅ E.functor.obj A') (cB : K.obj B ≅ E.functor.obj B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : cA.hom ≫ E.functor.map g = K.map f ≫ cB.hom) (z : Obj 𝗣𝗔 ℕ A) :
    (F 𝗧𝗔 ℕ).map g ((NumericalCoordinates.predicatePresentationIso A').hom.toFun
        (cA.hom.toFun z)) =
      (NumericalCoordinates.predicatePresentationIso B').hom.toFun
        (cB.hom.toFun ((F 𝗣𝗔 ℕ).map f z)) := by
  have he := congrArg (fun k => k.toFun z) h
  have hp := congrArg (NumericalCoordinates.predicatePresentationIso B').hom.toFun he
  have hn := NumericalCoordinates.predicatePresentationIso_natural_apply g (cA.hom.toFun z)
  simp only [NumericalTuples.composition_apply,
    NumericalArithmetic.numericalInterpretation_value] at hp
  change (NumericalCoordinates.predicatePresentationIso B').hom.toFun
      ((E.functor.map g).toFun (cA.hom.toFun z)) =
    (F 𝗧𝗔 ℕ).map g ((NumericalCoordinates.predicatePresentationIso A').hom.toFun
      (cA.hom.toFun z)) at hn
  exact hn.symm.trans hp

/-- All projection comparisons are comparisons of model values. -/
theorem point_fst (p q : SyntaxPolynomial I)
    (z : Obj 𝗣𝗔 ℕ (((.product p q : SyntaxPolynomial I).mapCoefficients s).eval.obj (X,Y))) :
    (F 𝗧𝗔 ℕ).map prod.fst (point s t c X Y X' Y' bX bY (.product p q) z) =
      point s t c X Y X' Y' bX bY p ((F 𝗣𝗔 ℕ).map prod.fst z) :=
  square_point (polynomialIso s t c X Y X' Y' bX bY (.product p q))
    (polynomialIso s t c X Y X' Y' bX bY p) prod.fst prod.fst
      (polynomial_fst s t c X Y X' Y' bX bY p q) z

theorem point_snd (p q : SyntaxPolynomial I)
    (z : Obj 𝗣𝗔 ℕ (((.product p q : SyntaxPolynomial I).mapCoefficients s).eval.obj (X,Y))) :
    (F 𝗧𝗔 ℕ).map prod.snd (point s t c X Y X' Y' bX bY (.product p q) z) =
      point s t c X Y X' Y' bX bY q ((F 𝗣𝗔 ℕ).map prod.snd z) :=
  square_point (polynomialIso s t c X Y X' Y' bX bY (.product p q))
    (polynomialIso s t c X Y X' Y' bX bY q) prod.snd prod.snd
      (polynomial_snd s t c X Y X' Y' bX bY p q) z

/-- The two tags are retained before interpreting the target polynomial. -/
theorem point_inl (p q : SyntaxPolynomial I)
    (z : Obj 𝗣𝗔 ℕ ((p.mapCoefficients s).eval.obj (X,Y))) :
    point s t c X Y X' Y' bX bY (.sum p q) ((F 𝗣𝗔 ℕ).map coprod.inl z) =
      (F 𝗧𝗔 ℕ).map coprod.inl (point s t c X Y X' Y' bX bY p z) :=
  (square_point (polynomialIso s t c X Y X' Y' bX bY p)
    (polynomialIso s t c X Y X' Y' bX bY (.sum p q)) coprod.inl coprod.inl
      (polynomial_inl s t c X Y X' Y' bX bY p q).symm z).symm

theorem point_inr (p q : SyntaxPolynomial I)
    (z : Obj 𝗣𝗔 ℕ ((q.mapCoefficients s).eval.obj (X,Y))) :
    point s t c X Y X' Y' bX bY (.sum p q) ((F 𝗣𝗔 ℕ).map coprod.inr z) =
      (F 𝗧𝗔 ℕ).map coprod.inr (point s t c X Y X' Y' bX bY q z) :=
  (square_point (polynomialIso s t c X Y X' Y' bX bY q)
    (polynomialIso s t c X Y X' Y' bX bY (.sum p q)) coprod.inr coprod.inr
      (polynomial_inr s t c X Y X' Y' bX bY p q).symm z).symm


section TypedRepresentation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (A B : PredicateCategory T)

theorem representation_product_typed (p q : SyntaxPolynomial (PredicateCategory T))
    (u : M) (z : Obj T M ((.product p q : SyntaxPolynomial (PredicateCategory T)).eval.obj (A,B))) :
    (baseRepresentation T A B (.product p q)).val.Evalb ![u,z.val] ↔
      ∃ v w : M, u = Arithmetic.pair v w ∧
        (baseRepresentation T A B p).val.Evalb ![v,((F T M).map prod.fst z).val] ∧
        (baseRepresentation T A B q).val.Evalb ![w,((F T M).map prod.snd z).val] := by
  rw [baseRepresentation_product_eval]
  constructor
  · rintro ⟨v,w,x,y,he,hp,hq,hx,hy⟩
    have ex := (ConcreteNamedComparison.chosenGraph_value_iff T M
      (prod.fst : p.eval.obj (A,B) ⨯ q.eval.obj (A,B) ⟶ _) z x).mp hx
    have ey := (ConcreteNamedComparison.chosenGraph_value_iff T M
      (prod.snd : p.eval.obj (A,B) ⨯ q.eval.obj (A,B) ⟶ _) z y).mp hy
    exact ⟨v,w,he,by simpa only [ex] using hp,by simpa only [ey] using hq⟩
  · rintro ⟨v,w,he,hp,hq⟩
    exact ⟨v,w,_,_,he,hp,hq,
      (ConcreteNamedComparison.chosenGraph_value_iff T M prod.fst z _).mpr rfl,
      (ConcreteNamedComparison.chosenGraph_value_iff T M prod.snd z _).mpr rfl⟩

theorem representation_sum_typed (p q : SyntaxPolynomial (PredicateCategory T))
    (u : M) (z : Obj T M ((.sum p q : SyntaxPolynomial (PredicateCategory T)).eval.obj (A,B))) :
    (baseRepresentation T A B (.sum p q)).val.Evalb ![u,z.val] ↔
      (∃ v : M, ∃ x : Obj T M (p.eval.obj (A,B)), u = Arithmetic.pair v 0 ∧
        (baseRepresentation T A B p).val.Evalb ![v,x.val] ∧
          (F T M).map coprod.inl x = z) ∨
      (∃ w : M, ∃ y : Obj T M (q.eval.obj (A,B)), u = Arithmetic.pair w 1 ∧
        (baseRepresentation T A B q).val.Evalb ![w,y.val] ∧
          (F T M).map coprod.inr y = z) := by
  rw [baseRepresentation_sum_eval]
  constructor
  · rintro (⟨v,x,he,hp,hx⟩ | ⟨w,y,he,hq,hy⟩)
    · let xx : Obj T M (p.eval.obj (A,B)) :=
        ⟨x,(baseRepresentation_support T M A B p v x hp).2⟩
      exact Or.inl ⟨v,xx,he,hp,Subtype.ext
        ((ConcreteNamedComparison.chosenGraph_value_iff T M coprod.inl xx z.val).mp hx)⟩
    · let yy : Obj T M (q.eval.obj (A,B)) :=
        ⟨y,(baseRepresentation_support T M A B q w y hq).2⟩
      exact Or.inr ⟨w,yy,he,hq,Subtype.ext
        ((ConcreteNamedComparison.chosenGraph_value_iff T M coprod.inr yy z.val).mp hy)⟩
  · rintro (⟨v,x,he,hp,hx⟩ | ⟨w,y,he,hq,hy⟩)
    · exact Or.inl ⟨v,x.val,he,hp,
        (ConcreteNamedComparison.chosenGraph_value_iff T M coprod.inl x z.val).mpr
          (congrArg Subtype.val hx)⟩
    · exact Or.inr ⟨w,y.val,he,hq,
        (ConcreteNamedComparison.chosenGraph_value_iff T M coprod.inr y z.val).mpr
          (congrArg Subtype.val hy)⟩
end TypedRepresentation

theorem point_surjective (p : SyntaxPolynomial I) :
    Function.Surjective (point s t c X Y X' Y' bX bY p) := by
  intro z
  refine ⟨(codeIso s t c X Y X' Y' bX bY p).inv.toFun z,?_⟩
  exact congrArg (fun f => f.toFun z) (codeIso s t c X Y X' Y' bX bY p).inv_hom_id

theorem point_injective (p : SyntaxPolynomial I) :
    Function.Injective (point s t c X Y X' Y' bX bY p) := by
  intro z w h
  have hi (x : Obj 𝗣𝗔 ℕ ((p.mapCoefficients s).eval.obj (X,Y))) :
      (codeIso s t c X Y X' Y' bX bY p).inv.toFun (point s t c X Y X' Y' bX bY p x) = x :=
    congrArg (fun f => f.toFun x) (codeIso s t c X Y X' Y' bX bY p).hom_inv_id
  exact (hi z).symm.trans ((congrArg (codeIso s t c X Y X' Y' bX bY p).inv.toFun h).trans (hi w))

variable (hX : ∀ z : Obj 𝗣𝗔 ℕ X,
  ((NumericalCoordinates.predicatePresentationIso X').hom.toFun (bX.hom.toFun z)).val = z.val)
variable (hY : ∀ z : Obj 𝗣𝗔 ℕ Y,
  ((NumericalCoordinates.predicatePresentationIso Y').hom.toFun (bY.hom.toFun z)).val = z.val)

variable (hC : ∀ i, ∀ z : Obj 𝗣𝗔 ℕ (s i),
  ((NumericalCoordinates.predicatePresentationIso (t i)).hom.toFun ((c i).hom.toFun z)).val = z.val)

include hC hX hY in
/-- The numerical polynomial code is unchanged through the product, sum and coefficient
comparisons, in both recursive sorts. -/
theorem baseRepresentation_iff (p : SyntaxPolynomial I)
    (u : ℕ) (z : Obj 𝗣𝗔 ℕ ((p.mapCoefficients s).eval.obj (X,Y))) :
    (baseRepresentation 𝗣𝗔 X Y (p.mapCoefficients s)).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 X' Y' (p.mapCoefficients t)).val.Evalb
        ![u,(point s t c X Y X' Y' bX bY p z).val] := by
  induction p generalizing u with
  | term =>
      have hv : (point s t c X Y X' Y' bX bY .term z).val = z.val := hX z
      simp only [SyntaxPolynomial.mapCoefficients,baseRepresentation_term_eval]
      constructor
      · rintro ⟨_,he⟩
        exact ⟨(point s t c X Y X' Y' bX bY .term z).property,hv.trans he⟩
      · rintro ⟨_,he⟩
        exact ⟨z.property,hv.symm.trans he⟩
  | formula =>
      have hv : (point s t c X Y X' Y' bX bY .formula z).val = z.val := hY z
      simp only [SyntaxPolynomial.mapCoefficients,baseRepresentation_formula_eval]
      constructor
      · rintro ⟨_,he⟩
        exact ⟨(point s t c X Y X' Y' bX bY .formula z).property,hv.trans he⟩
      · rintro ⟨_,he⟩
        exact ⟨z.property,hv.symm.trans he⟩
  | coefficient i =>
      have hv : (point s t c X Y X' Y' bX bY (.coefficient i) z).val = z.val := hC i z
      simp only [SyntaxPolynomial.mapCoefficients,baseRepresentation_coefficient_eval]
      exact and_congr (iff_of_true z.property
        (point s t c X Y X' Y' bX bY (.coefficient i) z).property) (by rw [hv])
  | unit =>
      simp only [SyntaxPolynomial.mapCoefficients,baseRepresentation_unit_eval]
      exact and_congr (iff_of_true z.property
        (point s t c X Y X' Y' bX bY .unit z).property) Iff.rfl
  | product p q hp hq =>
      simp only [SyntaxPolynomial.mapCoefficients]
      rw [representation_product_typed 𝗣𝗔 ℕ X Y,
        representation_product_typed 𝗧𝗔 ℕ X' Y']
      simp only [point_fst s t c X Y X' Y' bX bY,point_snd s t c X Y X' Y' bX bY]
      exact exists_congr (fun v => exists_congr (fun w =>
        and_congr Iff.rfl (and_congr (hp v ((F 𝗣𝗔 ℕ).map prod.fst z))
          (hq w ((F 𝗣𝗔 ℕ).map prod.snd z)))))
  | sum p q hp hq =>
      simp only [SyntaxPolynomial.mapCoefficients]
      rw [representation_sum_typed 𝗣𝗔 ℕ X Y,
        representation_sum_typed 𝗧𝗔 ℕ X' Y']
      constructor
      · rintro (⟨v,x,he,hp',hx⟩ | ⟨w,y,he,hq',hy⟩)
        · refine Or.inl ⟨v,point s t c X Y X' Y' bX bY p x,he,(hp v x).mp hp',?_⟩
          rw [← point_inl s t c X Y X' Y' bX bY p q,hx]
        · refine Or.inr ⟨w,point s t c X Y X' Y' bX bY q y,he,(hq w y).mp hq',?_⟩
          rw [← point_inr s t c X Y X' Y' bX bY p q,hy]
      · rintro (⟨v,x',he,hp',hx'⟩ | ⟨w,y',he,hq',hy'⟩)
        · obtain ⟨x,hx⟩ := point_surjective s t c X Y X' Y' bX bY p x'
          refine Or.inl ⟨v,x,he,(hp v x).mpr (by simpa only [hx] using hp'),?_⟩
          apply point_injective s t c X Y X' Y' bX bY (.sum p q)
          rw [point_inl s t c X Y X' Y' bX bY p q,hx]
          exact hx'
        · obtain ⟨y,hy⟩ := point_surjective s t c X Y X' Y' bX bY q y'
          refine Or.inr ⟨w,y,he,(hq w y).mpr (by simpa only [hy] using hq'),?_⟩
          apply point_injective s t c X Y X' Y' bX bY (.sum p q)
          rw [point_inr s t c X Y X' Y' bX bY p q,hy]
          exact hy'

/-- Exact coefficient scalar law for the canonical unary arithmetic
presentation; the template theorem also permits other proved charts. -/
theorem canonical_coefficient_value (C : PredicateCategory 𝗣𝗔) (z : Obj 𝗣𝗔 ℕ C) :
    ((NumericalCoordinates.predicatePresentationIso (coefficient C)).hom.toFun
      ((E.counitIso.app (K.obj C)).inv.toFun z)).val = z.val :=
  (NumericalSyntaxTreeChart.coefficient_input_code (K.obj C) z).trans
    (NumericalTuples.code_one z.val)

def normalizedIso (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁) :
    K.obj (p₀.eval.obj (X,Y)) ≅ E.functor.obj (p₁.eval.obj (X',Y')) :=
  K.mapIso (eqToIso (congrArg (fun a => a.eval.obj (X,Y)) h₀.symm)) ≪≫
    polynomialIso s t c X Y X' Y' bX bY p ≪≫
      E.functor.mapIso (eqToIso (congrArg (fun a => a.eval.obj (X',Y')) h₁))

def normalizedPoint (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (z : Obj 𝗣𝗔 ℕ (p₀.eval.obj (X,Y))) : Obj 𝗧𝗔 ℕ (p₁.eval.obj (X',Y')) :=
  (NumericalCoordinates.predicatePresentationIso (p₁.eval.obj (X',Y'))).hom.toFun
    ((normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom.toFun z)

include hC hX hY in
/-- Polynomial equalities are eliminated at the generic level before
instantiating the concrete parser or chosen carrier formulas. -/
theorem normalized_baseRepresentation_iff (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (u : ℕ) (z : Obj 𝗣𝗔 ℕ (p₀.eval.obj (X,Y))) :
    (baseRepresentation 𝗣𝗔 X Y p₀).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 X' Y' p₁).val.Evalb
        ![u,(normalizedPoint s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁ z).val] := by
  cases h₀
  cases h₁
  simpa only [normalizedPoint,normalizedIso,eqToIso_refl,Functor.mapIso_refl,
    Iso.refl_trans,Iso.trans_refl,point,codeIso,Iso.trans_hom,
    NumericalTuples.composition_apply] using
      baseRepresentation_iff s t c X Y X' Y' bX bY hX hY hC p u z

end CategoricalEssentialIncompleteness.V46.NumericalPolynomialRepresentation
