/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeTransport


/-! # Statement checks in `V46MillerNamedProofImageNativeTransportChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeTransportChecks
open NamedProofImage.NativeSubstitution
open Standard
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)
variable (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
  (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)).obj X ≅ Y)

example (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Standard.baseChart P X Y c p=NamedSyntaxComparison.constructorInput P X Y c p
      (Syntax.Polynomial.mapped P p) rfl := Standard.baseChart_constructorInput P X Y c p

example (R : Total.TotalCategory P) (r : (U).obj R) (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (U).map (PointFrame.nodeBaseArrow R r Y.1 Y.2 (Syntax.Polynomial.mapped P p)
      (Standard.mappedFrameData P R r X Y c p z)) ⟨0,rfl⟩=
      (U).map (Standard.baseChart P X Y c p).hom
        (NamedProofImage.sourcePoint P (p.eval.obj X) (Standard.realize X p z)) := Standard.mappedFrameData_base P R r X Y c p z

example (R : Total.TotalCategory P) (r : (U).obj R) (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (U).map (SyntaxPolynomial.parameterComparison R Y (Syntax.Polynomial.mapped P p)).left
      ((U).map (PointFrame.realize R r (constantFamily R Y.1,constantFamily R Y.2) (Syntax.Polynomial.mapped P p)
        (Standard.mappedFrameData P R r X Y c p z)).left ⟨0,rfl⟩)=
      Points.pairPoint r ((U).map (Standard.baseChart P X Y c p).hom
        (NamedProofImage.sourcePoint P (p.eval.obj X) (Standard.realize X p z))) :=
  Standard.mappedFrameData_comparison P R r X Y c p z

example (R : Total.TotalCategory P) (r : (U).obj R) (n : ℕ) (children : Fin n → (N).obj X.1) :
    Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term n)
      (Standard.mappedFrameData P R r X Y c (SyntaxPolynomial.power .term n) (Standard.powerData X n children))=
      PointFrame.powerData R r (constantFamily R Y.1,constantFamily R Y.2) n
        (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (NamedProofImage.sourcePoint P X.1 (children i)))) :=
  Standard.mappedFrameData_power P R r X Y c n children

example (R : Total.TotalCategory P) (r : (U).obj R) (τ : ℕ → PredicateCategory 𝗣𝗔)
    (d : ℕ) (k : Fin (d+1)) (label : (N).obj (τ k.val)) (children : Fin k.val → (N).obj X.1) :
    Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj τ d)
      (Standard.mappedFrameData P R r X Y c (SyntaxPolynomial.constructors τ d) (Standard.arityData X τ d k label children))=
      PointFrame.arityData R r (constantFamily R Y.1,constantFamily R Y.2) (fun n => (F).obj (τ n)) d k
        (NamedProofImage.sourcePoint P (τ k.val) label)
        (fun i => PointFrame.constant R r Y.1 ((U).map c.hom.1 (NamedProofImage.sourcePoint P X.1 (children i)))) :=
  Standard.mappedFrameData_arity P R r X Y c τ d k label children

example (R : Total.TotalCategory P) (r : (U).obj R)
    (A : Over R × Over R) (p q p' q' : SyntaxPolynomial (Total.TotalCategory P))
    (hp : p=p') (hq : q=q') (x : PointFrame.Data R r A p) (y : PointFrame.Data R r A q) :
    Standard.castFrameData P (congrArg₂ SyntaxPolynomial.product hp hq) (x,y)=
      (Standard.castFrameData P hp x,Standard.castFrameData P hq y) := Standard.castFrameData_product P hp hq x y

example
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
      (U).map j.hom (sourcePoint P W ((N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (realize X p z)))) :=
  Standard.framed_operation_transport P R₀ R₁ e r₀ X Y c p j v w h z

example
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
      (U).map j.hom (sourcePoint P W ((N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (realize X p z)))) :=
  Standard.framed_operation_transport_normalized P R₀ R₁ e r₀ X Y c p q hq j v w h z

example
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
      (U).map j.hom (sourcePoint P W ((N).map v (realize X p z))) :=
  Standard.pure_operation_transport_normalized P R₀ R₁ e r₀ X Y c p q hq j v w h z

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeTransportChecks
