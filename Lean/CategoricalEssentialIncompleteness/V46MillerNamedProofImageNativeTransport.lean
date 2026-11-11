/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeStandard
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeNodes
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionBranches

/-! # Finite standard-point charts and actual framed operation squares

The finite polynomial and slice geometry are proved before specializing
any branch square. No preservation of initiality is used.
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

namespace Standard
section MappedData
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

def baseChart (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (F).obj (p.eval.obj X) ≅ (Syntax.Polynomial.mapped P p).eval.obj Y :=
  Syntax.Polynomial.component P p X ≪≫ (Syntax.Polynomial.mapped P p).eval.mapIso c

theorem baseChart_constructorInput (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    baseChart P X Y c p=NamedSyntaxComparison.constructorInput P X Y c p
      (Syntax.Polynomial.mapped P p) rfl := by
  apply Iso.ext
  simp only [baseChart,NamedSyntaxComparison.constructorInput,NamedSyntaxComparison.normalizedComponent,
    Iso.trans_hom,eqToIso_refl,Iso.refl_hom,Category.comp_id]

private theorem baseChart_product (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    baseChart P X Y c (.product p q)=NamedSyntaxComparison.Options.productIso (F)
      (baseChart P X Y c p) (baseChart P X Y c q) := by
  apply Iso.ext
  change ((prodComparison (F) (p.eval.obj X) (q.eval.obj X) ≫
      prod.map (Syntax.Polynomial.component P p X).hom (Syntax.Polynomial.component P q X).hom) ≫
        prod.map ((Syntax.Polynomial.mapped P p).eval.map c.hom)
          ((Syntax.Polynomial.mapped P q).eval.map c.hom))=_
  rw [Category.assoc,prod.map_map]
  rfl

private theorem baseChart_inl (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (F).map (coprod.inl : p.eval.obj X ⟶ (SyntaxPolynomial.sum p q).eval.obj X) ≫
      (baseChart P X Y c (.sum p q)).hom=(baseChart P X Y c p).hom ≫ coprod.inl := by
  change (F).map coprod.inl ≫
    ((inv (coprodComparison (F) (p.eval.obj X) (q.eval.obj X)) ≫
      coprod.map (Syntax.Polynomial.component P p X).hom (Syntax.Polynomial.component P q X).hom) ≫
        coprod.map ((Syntax.Polynomial.mapped P p).eval.map c.hom)
          ((Syntax.Polynomial.mapped P q).eval.map c.hom))=_
  simp only [Category.assoc,map_inl_inv_coprodComparison_assoc,coprod.inl_map_assoc,coprod.inl_map]
  change (Syntax.Polynomial.component P p X).hom ≫
      (Syntax.Polynomial.mapped P p).eval.map c.hom ≫ coprod.inl =
    ((Syntax.Polynomial.component P p X).hom ≫
      (Syntax.Polynomial.mapped P p).eval.map c.hom) ≫ coprod.inl
  exact (Category.assoc _ _ _).symm

private theorem baseChart_inr (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    (F).map (coprod.inr : q.eval.obj X ⟶ (SyntaxPolynomial.sum p q).eval.obj X) ≫
      (baseChart P X Y c (.sum p q)).hom=(baseChart P X Y c q).hom ≫ coprod.inr := by
  change (F).map coprod.inr ≫
    ((inv (coprodComparison (F) (p.eval.obj X) (q.eval.obj X)) ≫
      coprod.map (Syntax.Polynomial.component P p X).hom (Syntax.Polynomial.component P q X).hom) ≫
        coprod.map ((Syntax.Polynomial.mapped P p).eval.map c.hom)
          ((Syntax.Polynomial.mapped P q).eval.map c.hom))=_
  simp only [Category.assoc,map_inr_inv_coprodComparison_assoc,coprod.inr_map_assoc,coprod.inr_map]
  change (Syntax.Polynomial.component P q X).hom ≫
      (Syntax.Polynomial.mapped P q).eval.map c.hom ≫ coprod.inr =
    ((Syntax.Polynomial.component P q X).hom ≫
      (Syntax.Polynomial.mapped P q).eval.map c.hom) ≫ coprod.inr
  exact (Category.assoc _ _ _).symm

/-- At one target frame, standard recursive leaves are charted as target
points. This is finite data; it is not a new syntax or proof calculus. -/
def mappedFrameData (R : Total.TotalCategory P) (r : (U).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y) :
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) → Data X p →
      PointFrame.Data R r (constantFamily R Y.1,constantFamily R Y.2) (Syntax.Polynomial.mapped P p)
  | .term, z => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 z))
  | .formula, z => PointFrame.constant R r Y.2 ((U).map c.hom.2 (sourcePoint P X.2 z))
  | .coefficient C, z => sourcePoint P C z
  | .unit, z => z
  | .product p q, z => (mappedFrameData R r X Y c p z.1,mappedFrameData R r X Y c q z.2)
  | .sum p _, .inl z => .inl (mappedFrameData R r X Y c p z)
  | .sum _ q, .inr z => .inr (mappedFrameData R r X Y c q z)

private theorem point_value {X : Total.TotalCategory P} (x : (U).obj X) :
    (U).map (Total.underlyingPoint x) ⟨0,rfl⟩=x := by
  apply Subtype.ext
  exact Part.mem_unique (Total.totalFunction_mem (Total.underlyingPoint x) ⟨0,rfl⟩)
    (Part.eq_some_iff.mp (Total.underlyingPoint_value x 0 rfl))

/-- Ordinary source polynomial charts act on actual standard points,
before any substitution fold or slice comparison is considered. -/
theorem mappedFrameData_base (R : Total.TotalCategory P) (r : (U).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (U).map (PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P p)
      (mappedFrameData P R r X Y c p z)) ⟨0,rfl⟩=
        (U).map (baseChart P X Y c p).hom (sourcePoint P (p.eval.obj X) (realize X p z)) := by
  induction p with
  | term =>
      change (U).map (prod.lift (Total.underlyingPoint r) _ ≫ prod.snd) ⟨0,rfl⟩=_
      rw [prod.lift_snd,point_value]
      simp only [baseChart,Syntax.Polynomial.component,Syntax.Polynomial.mapped,
        SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,Iso.trans_hom,Iso.refl_hom,
        CategoryTheory.Functor.mapIso_hom,CategoryTheory.Prod.fst,Category.id_comp]
      rfl
  | formula =>
      change (U).map (prod.lift (Total.underlyingPoint r) _ ≫ prod.snd) ⟨0,rfl⟩=_
      rw [prod.lift_snd,point_value]
      simp only [baseChart,Syntax.Polynomial.component,Syntax.Polynomial.mapped,
        SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,Iso.trans_hom,Iso.refl_hom,
        CategoryTheory.Functor.mapIso_hom,CategoryTheory.Prod.snd,Category.id_comp]
      rfl
  | coefficient C =>
      change (U).map (Total.underlyingPoint (sourcePoint P C z))
        (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)=_
      rw [point_value]
      simp only [baseChart,Syntax.Polynomial.component,Syntax.Polynomial.mapped,
        SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,Iso.trans_hom,Iso.refl_hom,
        CategoryTheory.Functor.mapIso_hom,CategoryTheory.Functor.const_obj_map,
        Category.id_comp]
      rfl
  | unit =>
      exact (terminalPoint_unique P _).trans (terminalPoint_unique P _).symm
  | product p q hp hq =>
      let f := PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P p)
        (mappedFrameData P R r X Y c p z.1)
      let g := PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P q)
        (mappedFrameData P R r X Y c q z.2)
      change (U).map (prod.lift f g) (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)=_
      have hl := Points.lift_point f g (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)
      have hv := congrArg₂ Points.pairPoint (hp z.1) (hq z.2)
      have hc := congrArg (fun i : (F).obj ((SyntaxPolynomial.product p q).eval.obj X) ≅
          (Syntax.Polynomial.mapped P (.product p q)).eval.obj Y =>
        (U).map i.hom (sourcePoint P ((SyntaxPolynomial.product p q).eval.obj X)
          (realize X (.product p q) z))) (baseChart_product P X Y c p q)
      exact hl.trans (hv.trans ((Points.mapped_pair P (baseChart P X Y c p) (baseChart P X Y c q)
        (realize X p z.1) (realize X q z.2)).symm.trans hc.symm))
  | sum p q hp hq =>
      cases z with
      | inl x =>
          have h := congrArg (fun f => (U).map f (sourcePoint P (p.eval.obj X) (realize X p x)))
            (baseChart_inl P X Y c p q)
          simp only [Functor.map_comp_apply,map_sourcePoint] at h
          let f := PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P p)
            (mappedFrameData P R r X Y c p x)
          let i : (Syntax.Polynomial.mapped P p).eval.obj Y ⟶
              (Syntax.Polynomial.mapped P p).eval.obj Y ⨿ (Syntax.Polynomial.mapped P q).eval.obj Y := coprod.inl
          change (U).map (f ≫ i) (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)=_
          exact (Functor.map_comp_apply (U) f i (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)).trans
            ((congrArg ((U).map i) (hp x)).trans h.symm)
      | inr y =>
          have h := congrArg (fun f => (U).map f (sourcePoint P (q.eval.obj X) (realize X q y)))
            (baseChart_inr P X Y c p q)
          simp only [Functor.map_comp_apply,map_sourcePoint] at h
          let f := PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P q)
            (mappedFrameData P R r X Y c q y)
          let i : (Syntax.Polynomial.mapped P q).eval.obj Y ⟶
              (Syntax.Polynomial.mapped P p).eval.obj Y ⨿ (Syntax.Polynomial.mapped P q).eval.obj Y := coprod.inr
          change (U).map (f ≫ i) (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)=_
          exact (Functor.map_comp_apply (U) f i (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left)).trans
            ((congrArg ((U).map i) (hq y)).trans h.symm)

private theorem frame_parameter (R : Total.TotalCategory P) (r : (U).obj R)
    (A : Over R) (f : PointFrame.source R r ⟶ A) :
    (U).map A.hom ((U).map f.left ⟨0,rfl⟩)=r := by
  have h := congrArg (fun k : (PointFrame.source R r).left ⟶ R =>
    (U).map k ⟨0,rfl⟩) (Over.w f)
  exact (Functor.map_comp_apply (U) f.left A.hom ⟨0,rfl⟩).symm.trans (h.trans (point_value P r))

theorem mappedFrameData_comparison (R : Total.TotalCategory P) (r : (U).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (U).map (SyntaxPolynomial.parameterComparison R Y (Syntax.Polynomial.mapped P p)).left
      ((U).map (PointFrame.realize R r (constantFamily R Y.1,constantFamily R Y.2)
        (Syntax.Polynomial.mapped P p) (mappedFrameData P R r X Y c p z)).left ⟨0,rfl⟩)=
      Points.pairPoint r ((U).map (baseChart P X Y c p).hom
        (sourcePoint P (p.eval.obj X) (realize X p z))) := by
  rcases X with ⟨X₁,X₂⟩
  rcases Y with ⟨Y₁,Y₂⟩
  let X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔 := (X₁,X₂)
  let Y : Total.TotalCategory P × Total.TotalCategory P := (Y₁,Y₂)
  let f := PointFrame.realize R r (constantFamily R Y.1,constantFamily R Y.2)
    (Syntax.Polynomial.mapped P p) (mappedFrameData P R r X Y c p z)
  let k := SyntaxPolynomial.parameterComparison R Y (Syntax.Polynomial.mapped P p)
  apply Points.product_ext
  · have hs := frame_parameter P R r
      (constantFamily R ((Syntax.Polynomial.mapped P p).eval.obj Y)) (f ≫ k)
    change (U).map (prod.fst : R ⨯ (Syntax.Polynomial.mapped P p).eval.obj Y ⟶ R)
      ((U).map (f ≫ k).left (⟨0,rfl⟩ : (U).obj (PointFrame.source R r).left))=r at hs
    have ht : (U).map prod.fst ((U).map k.left ((U).map f.left ⟨0,rfl⟩))=r := by
      simpa only [Over.comp_left,Functor.map_comp_apply] using hs
    exact ht.trans (Points.pairPoint_fst r
      ((U).map (baseChart P X Y c p).hom (sourcePoint P (p.eval.obj X) (realize X p z)))).symm
  · have h := congrArg (fun arrow : (PointFrame.source R r).left ⟶
        (Syntax.Polynomial.mapped P p).eval.obj Y => (U).map arrow ⟨0,rfl⟩)
      (PointFrame.realize_parameter_value R r Y.1 Y.2 (Syntax.Polynomial.mapped P p)
        (mappedFrameData P R r X Y c p z))
    have hv := (mappedFrameData_base P R r X Y c p z).trans
      (Points.pairPoint_snd r ((U).map (baseChart P X Y c p).hom
        (sourcePoint P (p.eval.obj X) (realize X p z)))).symm
    have hh := h.trans hv
    simp only [X,Y,Over.comp_left,Functor.map_comp_apply] at hh
    convert hh using 1

/-- A known branch square is evaluated only at a standard source input
and its constructed target frame. This lemma assumes no fold comparison. -/
theorem framed_operation_transport
    (R₀ : PredicateCategory 𝗣𝗔) (R₁ : Total.TotalCategory P) (e : (F).obj R₀ ≅ R₁)
    (r₀ : (N).obj R₀)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    {W : PredicateCategory 𝗣𝗔} {Z : Total.TotalCategory P} (j : (F).obj W ≅ Z)
    (v : R₀ ⨯ p.eval.obj X ⟶ W)
    (w : R₁ ⨯ (Syntax.Polynomial.mapped P p).eval.obj Y ⟶ Z)
    (h : (F).map v ≫ j.hom=
      (NamedSyntaxComparison.Options.productIso (F) e (baseChart P X Y c p)).hom ≫ w)
    (z : Data X p) :
    let r₁ := (U).map e.hom (sourcePoint P R₀ r₀)
    (U).map (prod.snd : R₁ ⨯ Z ⟶ Z)
      ((U).map (SyntaxPolynomial.parameterComparison R₁ Y (Syntax.Polynomial.mapped P p) ≫
        parameterHom w).left
          ((U).map (PointFrame.realize R₁ r₁ (constantFamily R₁ Y.1,constantFamily R₁ Y.2)
            (Syntax.Polynomial.mapped P p) (mappedFrameData P R₁ r₁ X Y c p z)).left ⟨0,rfl⟩))=
      (U).map j.hom (sourcePoint P W ((N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (realize X p z)))) := by
  dsimp only
  let r₁ := (U).map e.hom (sourcePoint P R₀ r₀)
  let b := (U).map (baseChart P X Y c p).hom (sourcePoint P (p.eval.obj X) (realize X p z))
  have hi := mappedFrameData_comparison P R₁ r₁ X Y c p z
  have hp := Points.mapped_pair P e (baseChart P X Y c p) r₀ (realize X p z)
  have hv := congrArg
    (fun f => (U).map f (sourcePoint P (R₀ ⨯ p.eval.obj X)
      (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (realize X p z)))) h
  simp only [Functor.map_comp_apply,map_sourcePoint,hp] at hv
  have hl : (parameterHom w).left ≫ (prod.snd : R₁ ⨯ Z ⟶ Z)=w := by
    exact prod.lift_snd _ _
  let input := (U).map (PointFrame.realize R₁ r₁ (constantFamily R₁ Y.1,constantFamily R₁ Y.2)
    (Syntax.Polynomial.mapped P p) (mappedFrameData P R₁ r₁ X Y c p z)).left ⟨0,rfl⟩
  let k := SyntaxPolynomial.parameterComparison R₁ Y (Syntax.Polynomial.mapped P p)
  have hc : (k ≫ parameterHom w).left ≫ (prod.snd : R₁ ⨯ Z ⟶ Z)=k.left ≫ w := by
    change (k.left ≫ (parameterHom w).left) ≫ prod.snd=k.left ≫ w
    exact (Category.assoc _ _ _).trans (congrArg (fun arrow => k.left ≫ arrow) hl)
  have hm := (Functor.map_comp_apply (U) (k ≫ parameterHom w).left
    (prod.snd : R₁ ⨯ Z ⟶ Z) input).symm.trans
      ((congrArg (fun arrow => (U).map arrow input) hc).trans
        (Functor.map_comp_apply (U) k.left w input))
  exact hm.trans ((congrArg ((U).map w) hi).trans hv.symm)

def castFrameData {R : Total.TotalCategory P} {r : (U).obj R} {A : Over R × Over R}
    {p q : SyntaxPolynomial (Total.TotalCategory P)} (h : p=q) (z : PointFrame.Data R r A p) :
    PointFrame.Data R r A q := h ▸ z

theorem castFrameData_inl {R : Total.TotalCategory P} {r : (U).obj R} {A : Over R × Over R}
    {p q p' q' : SyntaxPolynomial (Total.TotalCategory P)} (hp : p=p') (hq : q=q')
    (z : PointFrame.Data R r A p) :
    castFrameData P (congrArg₂ SyntaxPolynomial.sum hp hq) (Sum.inl z)=
      Sum.inl (castFrameData P hp z) := by cases hp; cases hq; rfl

theorem castFrameData_inr {R : Total.TotalCategory P} {r : (U).obj R} {A : Over R × Over R}
    {p q p' q' : SyntaxPolynomial (Total.TotalCategory P)} (hp : p=p') (hq : q=q')
    (z : PointFrame.Data R r A q) :
    castFrameData P (congrArg₂ SyntaxPolynomial.sum hp hq) (Sum.inr z)=
      Sum.inr (castFrameData P hq z) := by cases hp; cases hq; rfl

theorem castFrameData_product {R : Total.TotalCategory P} {r : (U).obj R} {A : Over R × Over R}
    {p q p' q' : SyntaxPolynomial (Total.TotalCategory P)} (hp : p=p') (hq : q=q')
    (x : PointFrame.Data R r A p) (y : PointFrame.Data R r A q) :
    castFrameData P (congrArg₂ SyntaxPolynomial.product hp hq) (x,y)=
      (castFrameData P hp x,castFrameData P hq y) := by cases hp; cases hq; rfl

theorem mappedFrameData_power (R : Total.TotalCategory P) (r : (U).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (n : ℕ) (children : Fin n → (N).obj X.1) :
    castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term n)
      (mappedFrameData P R r X Y c (SyntaxPolynomial.power .term n) (powerData X n children))=
      PointFrame.powerData R r (constantFamily R Y.1,constantFamily R Y.2) n
        (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children i)))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change castFrameData P
            (congrArg₂ SyntaxPolynomial.product
              (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (n+1))
              (rfl : Syntax.Polynomial.mapped P (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔))=
                (.term : SyntaxPolynomial (Total.TotalCategory P))))
            (mappedFrameData P R r X Y c (SyntaxPolynomial.power .term (n+1))
                (powerData X (n+1) (fun i => children i.castSucc)),
              PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children (Fin.last (n+1)))))) =
            (PointFrame.powerData R r (constantFamily R Y.1,constantFamily R Y.2) (n+1)
              (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children i.castSucc)))),
              PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children (Fin.last (n+1))))))
          have hc := castFrameData_product P (R := R) (r := r)
            (A := (constantFamily R Y.1,constantFamily R Y.2))
            (p := Syntax.Polynomial.mapped P (SyntaxPolynomial.power .term (n+1)))
            (q := Syntax.Polynomial.mapped P (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔)))
            (p' := SyntaxPolynomial.power .term (n+1)) (q' := .term)
            (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (n+1)) rfl
            (mappedFrameData P R r X Y c (SyntaxPolynomial.power .term (n+1))
              (powerData X (n+1) (fun i => children i.castSucc)))
            (PointFrame.constant R r Y.1
              ((U).map c.hom.1 (sourcePoint P X.1 (children (Fin.last (n+1))))))
          exact hc.trans (congrArg (fun u => (u,PointFrame.constant R r Y.1
            ((U).map c.hom.1 (sourcePoint P X.1 (children (Fin.last (n+1)))))))
              (ih (fun i => children i.castSucc)))

theorem mappedFrameData_arity (R : Total.TotalCategory P) (r : (U).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (τ : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (k : Fin (d+1)) (label : (N).obj (τ k.val))
    (children : Fin k.val → (N).obj X.1) :
    castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj τ d)
      (mappedFrameData P R r X Y c (SyntaxPolynomial.constructors τ d)
        (arityData X τ d k label children))=
      PointFrame.arityData R r (constantFamily R Y.1,constantFamily R Y.2)
        (fun n => (F).obj (τ n)) d k (sourcePoint P (τ k.val) label)
          (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children i)))) := by
  induction d with
  | zero =>
      have hk : k=0 := Fin.eq_zero k
      subst k
      rfl
  | succ d ih =>
      revert label children
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro label children
        simp only [arityData,PointFrame.arityData,Fin.lastCases_last]
        let hp := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj τ d
        let ht : Syntax.Polynomial.mapped P (.coefficient (τ (d+1)))=
            SyntaxPolynomial.coefficient ((F).obj (τ (d+1))) := rfl
        let hq := congrArg₂ SyntaxPolynomial.product ht
          (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (d+1))
        change castFrameData P (congrArg₂ SyntaxPolynomial.sum hp hq)
          (Sum.inr (sourcePoint P (τ (d+1)) label,
            mappedFrameData P R r X Y c (SyntaxPolynomial.power .term (d+1))
              (powerData X (d+1) children))) =
          Sum.inr (sourcePoint P (τ (d+1)) label,
            PointFrame.powerData R r (constantFamily R Y.1,constantFamily R Y.2) (d+1)
              (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children i)))))
        rw [castFrameData_inr P hp hq,
          castFrameData_product P ht
            (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (d+1))]
        exact congrArg (fun u => Sum.inr (sourcePoint P (τ (d+1)) label,u))
          (mappedFrameData_power P R r X Y c (d+1) children)
      · intro label children
        simp only [arityData,PointFrame.arityData,Fin.lastCases_castSucc]
        let hp := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj τ d
        let hq := congrArg₂ SyntaxPolynomial.product
          (rfl : Syntax.Polynomial.mapped P (.coefficient (τ (d+1)))=
            SyntaxPolynomial.coefficient ((F).obj (τ (d+1))))
          (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (d+1))
        change castFrameData P (congrArg₂ SyntaxPolynomial.sum hp hq)
          (Sum.inl (mappedFrameData P R r X Y c (SyntaxPolynomial.constructors τ d)
            (arityData X τ d j label children))) =
          Sum.inl (PointFrame.arityData R r (constantFamily R Y.1,constantFamily R Y.2)
            (fun n => (F).obj (τ n)) d j (sourcePoint P (τ j.val) label)
              (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (sourcePoint P X.1 (children i)))))
        rw [castFrameData_inl P hp hq]
        exact congrArg Sum.inl (ih j label children)

/-- The same actual point calculation with the explicitly normalized
polynomial header used by the frozen branch squares. -/
theorem framed_operation_transport_normalized
    (R₀ : PredicateCategory 𝗣𝗔) (R₁ : Total.TotalCategory P) (e : (F).obj R₀ ≅ R₁)
    (r₀ : (N).obj R₀)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (q : SyntaxPolynomial (Total.TotalCategory P))
    (hq : Syntax.Polynomial.mapped P p=q)
    {W : PredicateCategory 𝗣𝗔} {Z : Total.TotalCategory P} (j : (F).obj W ≅ Z)
    (v : R₀ ⨯ p.eval.obj X ⟶ W) (w : R₁ ⨯ q.eval.obj Y ⟶ Z)
    (h : (F).map v ≫ j.hom=
      (NamedSyntaxComparison.Options.productIso (F) e
        (NamedSyntaxComparison.constructorInput P X Y c p q hq)).hom ≫ w)
    (z : Data X p) :
    let r₁ := (U).map e.hom (sourcePoint P R₀ r₀)
    (U).map (prod.snd : R₁ ⨯ Z ⟶ Z)
      ((U).map (SyntaxPolynomial.parameterComparison R₁ Y q ≫ parameterHom w).left
        ((U).map (PointFrame.realize R₁ r₁ (constantFamily R₁ Y.1,constantFamily R₁ Y.2) q
          (castFrameData P hq (mappedFrameData P R₁ r₁ X Y c p z))).left ⟨0,rfl⟩))=
      (U).map j.hom (sourcePoint P W ((N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (realize X p z)))) := by
  subst q
  have hc := congrArg (fun i => (NamedSyntaxComparison.Options.productIso (F) e i).hom ≫ w)
    (baseChart_constructorInput P X Y c p)
  have ht := framed_operation_transport P R₀ R₁ e r₀ X Y c p j v w (h.trans hc.symm) z
  simpa only [castFrameData] using ht

private theorem pure_parameterHom {R A B : Total.TotalCategory P} (v : A ⟶ B) :
    parameterHom ((prod.snd : R ⨯ A ⟶ A) ≫ v)=(constantFamilyFunctor R).map v := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp only [parameterHom,Over.homMk_left,constantFamilyFunctor,
      prod.lift_fst,prod.map_fst,Category.comp_id]
  · simp only [parameterHom,Over.homMk_left,constantFamilyFunctor,
      prod.lift_snd,prod.map_snd]

theorem pure_operation_transport_normalized
    (R₀ : PredicateCategory 𝗣𝗔) (R₁ : Total.TotalCategory P) (e : (F).obj R₀ ≅ R₁)
    (r₀ : (N).obj R₀)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (q : SyntaxPolynomial (Total.TotalCategory P))
    (hq : Syntax.Polynomial.mapped P p=q)
    {W : PredicateCategory 𝗣𝗔} {Z : Total.TotalCategory P} (j : (F).obj W ≅ Z)
    (v : p.eval.obj X ⟶ W) (w : q.eval.obj Y ⟶ Z)
    (h : (F).map v ≫ j.hom=(NamedSyntaxComparison.constructorInput P X Y c p q hq).hom ≫ w)
    (z : Data X p) :
    let r₁ := (U).map e.hom (sourcePoint P R₀ r₀)
    (U).map (prod.snd : R₁ ⨯ Z ⟶ Z)
      ((U).map (SyntaxPolynomial.parameterComparison R₁ Y q ≫ (constantFamilyFunctor R₁).map w).left
        ((U).map (PointFrame.realize R₁ r₁ (constantFamily R₁ Y.1,constantFamily R₁ Y.2) q
          (castFrameData P hq (mappedFrameData P R₁ r₁ X Y c p z))).left ⟨0,rfl⟩))=
      (U).map j.hom (sourcePoint P W ((N).map v (realize X p z))) := by
  let k := NamedSyntaxComparison.constructorInput P X Y c p q hq
  have hp : (F).map ((prod.snd : R₀ ⨯ p.eval.obj X ⟶ p.eval.obj X) ≫ v) ≫ j.hom=
      (NamedSyntaxComparison.Options.productIso (F) e k).hom ≫ prod.snd ≫ w := by
    calc
      _ = (F).map prod.snd ≫ ((F).map v ≫ j.hom) := by
        rw [Functor.map_comp,Category.assoc]
      _ = (F).map prod.snd ≫ (k.hom ≫ w) := congrArg (fun arrow => (F).map prod.snd ≫ arrow) h
      _ = _ := by rw [← Category.assoc,← NamedSyntaxComparison.Options.productIso_snd,Category.assoc]
  have ht := framed_operation_transport_normalized P R₀ R₁ e r₀ X Y c p q hq j
    (prod.snd ≫ v) (prod.snd ≫ w) hp z
  simp only [pure_parameterHom,Functor.map_comp_apply] at ht
  have hv := congrArg (fun u => (U).map j.hom (sourcePoint P W ((N).map v u)))
    (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ r₀ (realize X p z))
  exact ht.trans hv

end MappedData
end Standard

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
