/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSource
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeTransport

/-! # Native term substitution through the actual uniform fold

The fixed-frame constructor law and the verified variable/function squares
give native term induction, retaining nullary symbols and ordered children.
Formula substitution is continued separately.
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

section TermStep
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "a" => SyntaxPolynomial.termExpression (variableCarrier : PredicateCategory 𝗣𝗔) σ d
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "c" => NamedSyntaxComparison.substitutionStateIso P (V) σ π d
local notation "e" => NamedSyntaxComparison.substitutionParameterIso P (V) σ π d
local notation "j" => NamedSyntaxComparison.substitutionTermStateIso P (V) σ π d

def termStateInputData (r₀ : (N).obj (R₀)) (z : Standard.Data (S₀).substitutionCarriers (a)) :
    PointFrame.Data (R) ((U).map (e).hom (sourcePoint P (R₀) r₀)) (S).substitutionAlgebra.a (p) :=
  Standard.castFrameData P (NamedSyntaxComparison.termExpression_mapped P (V) σ d)
    (Standard.mappedFrameData P (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
      (S₀).substitutionCarriers (S).substitutionCarriers (c) (a) z)

private theorem termStateInputData_inl (r₀ : (N).obj (R₀)) (v : (N).obj (V)) :
    termStateInputData P σ π d r₀ (Sum.inl v)=Sum.inl (sourcePoint P (V) v) := by
  unfold termStateInputData
  let hV : Syntax.Polynomial.mapped P (.coefficient (V))=
      SyntaxPolynomial.coefficient ((F).obj (V)) := rfl
  let hc := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d
  change Standard.castFrameData P (congrArg₂ SyntaxPolynomial.sum hV hc)
    (Sum.inl (sourcePoint P (V) v))=Sum.inl (sourcePoint P (V) v)
  exact Standard.castFrameData_inl P hV hc (sourcePoint P (V) v)

private theorem termStateInputData_inr (r₀ : (N).obj (R₀))
    (v : Standard.Data (S₀).substitutionCarriers (SyntaxPolynomial.constructors σ d)) :
    termStateInputData P σ π d r₀ (Sum.inr v)=Sum.inr
      (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
        (Standard.mappedFrameData P (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
          (S₀).substitutionCarriers (S).substitutionCarriers (c) (SyntaxPolynomial.constructors σ d) v)) := by
  unfold termStateInputData
  let hV : Syntax.Polynomial.mapped P (.coefficient (V))=
      SyntaxPolynomial.coefficient ((F).obj (V)) := rfl
  let hc := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d
  exact Standard.castFrameData_inr P hV hc
    (Standard.mappedFrameData P (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
      (S₀).substitutionCarriers (S).substitutionCarriers (c) (SyntaxPolynomial.constructors σ d) v)

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

/-- The two term branches are the actual already proved morphism squares,
evaluated at one standard parameter and one finite ordered input. -/
theorem term_step_transport (r₀ : (N).obj (R₀))
    (z : Standard.Data (S₀).substitutionCarriers (a)) :
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
      ((U).map (S).substitutionAlgebra.str.1.left
        ((U).map (PointFrame.realize (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
          (S).substitutionAlgebra.a (p) (termStateInputData P σ π d r₀ z)).left ⟨0,rfl⟩))=
      (U).map (j).hom (sourcePoint P (S₀).substitutionCarriers.1
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _)
          ((N).map (S₀).substitutionAlgebra.str.1.left
            (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers (a) z).val))) := by
  cases z with
  | inl v =>
      let i := NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers
        (S).substitutionCarriers (c) (.coefficient (V)) (.coefficient ((F).obj (V))) rfl
      have hi : i=Iso.refl ((F).obj (V)) := by
        apply Iso.ext
        simp only [i,NamedSyntaxComparison.constructorInput,NamedSyntaxComparison.normalizedComponent,
          Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,
          Functor.mapIso_hom,SyntaxPolynomial.eval,Functor.const_obj_map,
          Category.id_comp,Category.comp_id]
      have hsq : (F).map (S₀).variableSubstitutionPair ≫ (j).hom=
          (NamedSyntaxComparison.Options.productIso (F) (e) i).hom ≫ (S).variableSubstitutionPair := by
        rw [hi]
        exact NamedSyntaxComparison.map_variableSubstitutionPair P (V) σ π d
      have ht := Standard.framed_operation_transport_normalized P (R₀) (R) (e) r₀
        (S₀).substitutionCarriers (S).substitutionCarriers (c)
        (.coefficient (V)) (.coefficient ((F).obj (V))) rfl (j)
        (S₀).variableSubstitutionPair (S).variableSubstitutionPair hsq v
      have hs := Standard.operation_value (R₀) r₀ (S₀).substitutionCarriers (.coefficient (V))
        (S₀).variableSubstitutionPair v
      have hsource := congrArg (fun q => (U).map (j).hom
        (sourcePoint P (S₀).substitutionCarriers.1 q)) hs.symm
      have hh := ht.trans hsource
      let r₁ : (U).obj (R) := (U).map (e).hom (sourcePoint P (R₀) r₀)
      have htarget := over_inl_value (U)
        (parameterHom (S).variableSubstitutionPair)
        (SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers
          (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d) ≫
            (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).functionSubstitutionPair)
        ((U).map (PointFrame.constant (R) r₁ ((F).obj (V)) (sourcePoint P (V) v)).left ⟨0,rfl⟩)
      have hsourceInput := over_inl_value (N)
        (parameterHom (S₀).variableSubstitutionPair)
        (SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers
          (SyntaxPolynomial.constructors σ d) ≫
            (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).functionSubstitutionPair)
        (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ v)
      have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)) htarget
      have hsproj := congrArg (fun q => (U).map (j).hom
        (sourcePoint P (S₀).substitutionCarriers.1
          ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _) q))) hsourceInput
      simp only [termStateInputData_inl,PointFrame.realize,Standard.liftData,Standard.fiberInl,
        CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.termExpression,
        SyntaxPolynomial.parameterComparison,Standard.castFrameData,Category.id_comp,
        Standard.mappedFrameData,
        Over.comp_left,Functor.map_comp_apply] at hh ⊢
      convert htproj.trans (hh.trans hsproj.symm) using 1
      all_goals rfl

  | inr v =>
      have ht := Standard.pure_operation_transport_normalized P (R₀) (R) (e) r₀
        (S₀).substitutionCarriers (S).substitutionCarriers (c)
        (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
        (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d) (j)
        (S₀).functionSubstitutionPair (S).functionSubstitutionPair
        (NamedSyntaxComparison.map_functionSubstitutionPair P (V) σ π d) v
      have hs := Standard.pure_operation_value (R₀) r₀ (S₀).substitutionCarriers
        (SyntaxPolynomial.constructors σ d) (S₀).functionSubstitutionPair v
      have hsource := congrArg (fun q => (U).map (j).hom
        (sourcePoint P (S₀).substitutionCarriers.1 q)) hs.symm
      have hh := ht.trans hsource
      let r₁ : (U).obj (R) := (U).map (e).hom (sourcePoint P (R₀) r₀)
      have htarget := over_inr_value (U)
        (parameterHom (S).variableSubstitutionPair)
        (SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers
          (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d) ≫
            (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).functionSubstitutionPair)
        ((U).map (PointFrame.realize (R) r₁
          (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
          (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
          (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
            (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c)
              (SyntaxPolynomial.constructors σ d) v))).left ⟨0,rfl⟩)
      have hsourceInput := over_inr_value (N)
        (parameterHom (S₀).variableSubstitutionPair)
        (SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers
          (SyntaxPolynomial.constructors σ d) ≫
            (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).functionSubstitutionPair)
        (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers
          (SyntaxPolynomial.constructors σ d) v).val
      have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)) htarget
      have hsproj := congrArg (fun q => (U).map (j).hom
        (sourcePoint P (S₀).substitutionCarriers.1
          ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _) q))) hsourceInput
      simp only [Over.comp_left,Functor.map_comp_apply] at htproj hsproj
      simp only [termStateInputData_inr,PointFrame.realize,Standard.liftData,Standard.fiberInr,
        CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.termExpression,
        Over.comp_left,Functor.map_comp_apply] at hh ⊢
      convert htproj.trans (hh.trans hsproj.symm) using 1
      all_goals rfl

end TermStep

section TermInduction
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "a" => SyntaxPolynomial.termExpression (variableCarrier : PredicateCategory 𝗣𝗔) σ d
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "c" => NamedSyntaxComparison.substitutionStateIso P (V) σ π d

private theorem braid_point {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.braiding X Y).hom (Points.pairPoint x y)=Points.pairPoint y x := by
  apply Points.product_ext
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_fst,
      Points.pairPoint_snd,Points.pairPoint_fst]
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_snd,
      Points.pairPoint_fst,Points.pairPoint_snd]

private theorem point_value {X : Total.TotalCategory P} (x : (U).obj X) :
    (U).map (Total.underlyingPoint x) ⟨0,rfl⟩=x := by
  apply Subtype.ext
  exact Part.mem_unique (Total.totalFunction_mem (Total.underlyingPoint x) ⟨0,rfl⟩)
    (Part.eq_some_iff.mp (Total.underlyingPoint_value x 0 rfl))

theorem frame_constant_comp {R₁ X₁ Y₁ : Total.TotalCategory P} (r : (U).obj R₁)
    (f : constantFamily R₁ X₁ ⟶ constantFamily R₁ Y₁) (x : (U).obj X₁) :
    PointFrame.constant R₁ r X₁ x ≫ f=PointFrame.constant R₁ r Y₁
      ((U).map (prod.snd : R₁ ⨯ Y₁ ⟶ Y₁) ((U).map f.left (Points.pairPoint r x))) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · have hf : f.left ≫ (prod.fst : R₁ ⨯ Y₁ ⟶ R₁)=(prod.fst : R₁ ⨯ X₁ ⟶ R₁) := Over.w f
    change ((PointFrame.constant R₁ r X₁ x).left ≫ f.left) ≫ prod.fst=
      (PointFrame.constant R₁ r Y₁ _).left ≫ prod.fst
    rw [Category.assoc,hf]
    exact (prod.lift_fst _ _).trans (prod.lift_fst _ _).symm
  · change ((PointFrame.constant R₁ r X₁ x).left ≫ f.left) ≫ prod.snd=
      prod.lift (Total.underlyingPoint r)
        (Total.underlyingPoint ((U).map prod.snd ((U).map f.left (Points.pairPoint r x)))) ≫ prod.snd
    rw [prod.lift_snd]
    apply (Total.pointHomEquiv Y₁).symm.injective
    change (U).map (((PointFrame.constant R₁ r X₁ x).left ≫ f.left) ≫ prod.snd) ⟨0,rfl⟩=
      (U).map (Total.underlyingPoint _) ⟨0,rfl⟩
    rw [point_value,Functor.map_comp_apply,Functor.map_comp_apply,PointFrame.constant_point]
    rfl

theorem termState_frame_value (x : ℕ) (t r : Tm) :
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
      ((U).map (S).substitutionFold.1.left
        (Points.pairPoint (parameterPoint P σ π d x t) (termPoint P σ π d r)))=
      termState P σ π d x t r := by
  simp only [termState,termInput,Functor.map_comp_apply,braid_point]
  rfl

theorem termLeaf_fold (x : ℕ) (t r : Tm) :
    termLeaf P σ π d (parameterPoint P σ π d x t) r ≫ (S).substitutionFold.1=
      PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.1
        (termState P σ π d x t r) := by
  exact (frame_constant_comp P (parameterPoint P σ π d x t) (S).substitutionFold.1
    (termPoint P σ π d r)).trans
      (congrArg (PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.1)
        (termState_frame_value P σ π d x t r))

def termStepValue (x : ℕ) (t : Tm)
    (z : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (p)) :
    (U).obj (S).substitutionCarriers.1 :=
  (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
    ((U).map (S).substitutionAlgebra.str.1.left
      ((U).map (PointFrame.realize (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (p) z).left
        ⟨0,rfl⟩))

theorem termState_step (x : ℕ) (t r : Tm) :
    termState P σ π d x t r=termStepValue P σ π d x t
      (PointFrame.mapData (R) (parameterPoint P σ π d x t) (S).substitutionFold (p)
        (termNodeInput P σ π d (parameterPoint P σ π d x t) r)) := by
  have h := term_root_framed P σ π d (parameterPoint P σ π d x t)
    (termNodeInput P σ π d (parameterPoint P σ π d x t) r)
  rw [← Category.assoc,term_node_realizes_hom P σ π d (parameterPoint P σ π d x t) r] at h
  have hv := congrArg (fun k : PointFrame.source (R) (parameterPoint P σ π d x t) ⟶
      (S).substitutionAlgebra.a.1 =>
        (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
          ((U).map k.left ⟨0,rfl⟩)) h
  simp only [Over.comp_left,Functor.map_comp_apply] at hv
  have hc := congrArg (fun q =>
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
      ((U).map (S).substitutionFold.1.left q))
    (PointFrame.constant_point (R) (parameterPoint P σ π d x t) (S).algebra.a.1 (termPoint P σ π d r))
  exact (termState_frame_value P σ π d x t r).symm.trans (hc.symm.trans hv)

def termNativeStateInputData (x : ℕ) (t r : Tm) :
    PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (p) :=
  Standard.castFrameData P (NamedSyntaxComparison.termExpression_mapped P (V) σ d)
    (Standard.mappedFrameData P (R) (parameterPoint P σ π d x t)
      (S₀).substitutionCarriers (S).substitutionCarriers (c) (a)
      (Standard.mapData
        (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
        (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
        (a) (paTermNodeData σ π d r)))

theorem expectedTermState_step (x : ℕ) (t r : Tm) :
    termStepValue P σ π d x t (termNativeStateInputData P σ π d x t r)=
      expectedTermState P σ π d x t r := by
  have h := term_step_transport P σ π d (paParameterPoint σ π d x t)
    (Standard.mapData
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
      (a) (paTermNodeData σ π d r))
  have hs := congrArg (fun q => (U).map
    (NamedSyntaxComparison.substitutionTermStateIso P (V) σ π d).hom
      (sourcePoint P (S₀).substitutionCarriers.1 q)) (paTermState_step σ π d x t r).symm
  let node := Standard.mapData
    (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
    (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
    (a) (paTermNodeData σ π d r)
  let evaluated (r₁ : (U).obj (R)) : (U).obj (S).substitutionCarriers.1 :=
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.1 ⟶ _)
      ((U).map (S).substitutionAlgebra.str.1.left
        ((U).map (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a (p)
          (Standard.castFrameData P (NamedSyntaxComparison.termExpression_mapped P (V) σ d)
            (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers
              (S).substitutionCarriers (c) (a) node))).left ⟨0,rfl⟩))
  have he := congrArg evaluated (paParameterPoint_chart P σ π d x t)
  exact he.symm.trans (h.trans hs)

private theorem term_native_input_variable (x y : ℕ) (t : Tm) :
    PointFrame.mapData (R) (parameterPoint P σ π d x t) (S).substitutionFold (p)
      (termNodeInput P σ π d (parameterPoint P σ π d x t) (.var y))=
      termNativeStateInputData P σ π d x t (.var y) := by
  let hV : Syntax.Polynomial.mapped P (.coefficient (V))=
      SyntaxPolynomial.coefficient ((F).obj (V)) := rfl
  let hc := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d
  change Sum.inl (Points.namePoint P y)=Standard.castFrameData P
    (congrArg₂ SyntaxPolynomial.sum hV hc) (Sum.inl (Points.namePoint P y))
  exact (Standard.castFrameData_inl P hV hc (Points.namePoint P y)).symm

private theorem term_native_input_function (x : ℕ) (t : Tm) (k : Fin (d+1))
    (label : Symbols σ k.val) (children : Fin k.val → Tm)
    (ih : ∀ i,termState P σ π d x t (children i)=expectedTermState P σ π d x t (children i)) :
    PointFrame.mapData (R) (parameterPoint P σ π d x t) (S).substitutionFold (p)
      (termNodeInput P σ π d (parameterPoint P σ π d x t) (.app k label children))=
      termNativeStateInputData P σ π d x t (.app k label children) := by
  rw [function_node_map P σ π d (parameterPoint P σ π d x t) k label children]
  unfold termNativeStateInputData
  let hV : Syntax.Polynomial.mapped P (.coefficient (V))=
      SyntaxPolynomial.coefficient ((F).obj (V)) := rfl
  let hc := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d
  change Sum.inr (PointFrame.arityData (R) (parameterPoint P σ π d x t)
      (S).substitutionAlgebra.a (fun n => (F).obj (σ n)) d k (sourcePoint P (σ k.val) label)
        (fun i => termLeaf P σ π d (parameterPoint P σ π d x t) (children i) ≫ (S).substitutionFold.1))=
    Standard.castFrameData P (congrArg₂ SyntaxPolynomial.sum hV hc)
      (Sum.inr (Standard.mappedFrameData P (R) (parameterPoint P σ π d x t)
        (S₀).substitutionCarriers (S).substitutionCarriers (c) (SyntaxPolynomial.constructors σ d)
        (Standard.mapData
          (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
          (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
          (SyntaxPolynomial.constructors σ d)
          (Standard.arityData (S₀).algebra.a σ d k label (fun i => SyntacticNamedHilbert.termPoint σ π d (children i))))))
  rw [Standard.castFrameData_inr P hV hc,Standard.mapData_arityData,Standard.mappedFrameData_arity]
  apply congrArg (fun f => Sum.inr (PointFrame.arityData (R) (parameterPoint P σ π d x t)
    (S).substitutionAlgebra.a (fun n => (F).obj (σ n)) d k (sourcePoint P (σ k.val) label) f))
  funext i
  rw [paTermState_leaf]
  change termLeaf P σ π d (parameterPoint P σ π d x t) (children i) ≫ (S).substitutionFold.1=
    PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.1
      (expectedTermState P σ π d x t (children i))
  rw [termLeaf_fold P σ π d x t (children i),ih i]

/-- Native term induction is performed on the actual finite named tree.
Neither an underlying preservation-of-initiality assertion nor a source
global point for the replacement is required. -/
theorem termState_comparison (x : ℕ) (t r : Tm) :
    termState P σ π d x t r=expectedTermState P σ π d x t r := by
  induction r with
  | var y =>
      exact (termState_step P σ π d x t (.var y)).trans
        ((congrArg (termStepValue P σ π d x t) (term_native_input_variable P σ π d x y t)).trans
          (expectedTermState_step P σ π d x t (.var y)))
  | app k label children ih =>
      exact (termState_step P σ π d x t (.app k label children)).trans
        ((congrArg (termStepValue P σ π d x t)
          (term_native_input_function P σ π d x t k label children ih)).trans
            (expectedTermState_step P σ π d x t (.app k label children)))

theorem termValue_eq_native (x : ℕ) (t r : Tm) :
    termValue P σ π d x t r=termPoint P σ π d (r.substitute x t) := by
  have h := congrArg ((U).map (prod.snd : (S).substitutionCarriers.1 ⟶ (S).algebra.a.1))
    ((termState_comparison P σ π d x t r).trans (expectedTermState_native P σ π d x t r))
  exact (termState_result P σ π d x t r).symm.trans (h.trans (Points.pairPoint_snd _ _))

end TermInduction

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
