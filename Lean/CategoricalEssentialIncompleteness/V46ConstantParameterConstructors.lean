/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantParameterAlgebra

/-! # Constructor computations for constant-family reindexing -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ConstantParameterAlgebra
open SyntaxParameterChange
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P Q : D} (r : P ⟶ Q) (X : D × D)

@[reassoc] theorem component_value (p : SyntaxPolynomial D) {Y : D}
    (s : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    (component r X p s).left ≫ prod.snd =
      (polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫ s).left ≫ prod.snd := by
  simp only [component, Over.homMk_left, prod.lift_snd]

theorem component_precomp (p q : SyntaxPolynomial D) {Y : D}
    (k : (p.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
      (q.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2))
    (l : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      (q.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2))
    (h : (Over.map r).map k ≫ polynomialMap r (baseMap r X.1, baseMap r X.2) q =
      polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫ l)
    (s : (q.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    k ≫ component r X q s = component r X p (l ≫ s) := by
  apply constantFamily_hom_ext
  have hh := congrArg (fun a => (a ≫ s).left ≫ prod.snd) h
  simpa only [Over.comp_left, Category.assoc, component_value, Over.map_map_left] using hh

@[reassoc] theorem component_inl (p q : SyntaxPolynomial D) {Y : D}
    (s : ((p.sum q).withParameters Q).eval.obj
      (constantFamily Q X.1, constantFamily Q X.2) ⟶ constantFamily Q Y) :
    coprod.inl ≫ component r X (p.sum q) s = component r X p (coprod.inl ≫ s) :=
  component_precomp r X p (.sum p q) coprod.inl coprod.inl
    (polynomialMap_inl r _ p q) s

@[reassoc] theorem component_inr (p q : SyntaxPolynomial D) {Y : D}
    (s : ((p.sum q).withParameters Q).eval.obj
      (constantFamily Q X.1, constantFamily Q X.2) ⟶ constantFamily Q Y) :
    coprod.inr ≫ component r X (p.sum q) s = component r X q (coprod.inr ≫ s) :=
  component_precomp r X q (.sum p q) coprod.inr coprod.inr
    (polynomialMap_inr r _ p q) s

theorem component_coprod (p q : SyntaxPolynomial D) {Y : D}
    (s : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y)
    (t : (q.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    component r X (p.sum q) (coprod.desc s t) =
      coprod.desc (component r X p s) (component r X q t) := by
  apply coprod.hom_ext
  · simp only [component_inl, coprod.inl_desc]
  · simp only [component_inr, coprod.inr_desc]

theorem component_constant (p : SyntaxPolynomial D) {Y : D} (f : p.eval.obj X ⟶ Y) :
    component r X p
      (SyntaxPolynomial.parameterComparison Q X p ≫ (constantFamilyFunctor Q).map f) =
        SyntaxPolynomial.parameterComparison P X p ≫ (constantFamilyFunctor P).map f := by
  apply constantFamily_hom_ext
  have h := congrArg (fun a => a.left ≫ prod.snd) (parameter_algebra_str r X p f)
  simpa only [component_value, Over.comp_left, Over.map_map_left, baseMap,
    Over.homMk_left, Category.assoc, prod.map_snd, Category.comp_id] using h

theorem component_parameter (p : SyntaxPolynomial D) {Y : D} (f : Q ⨯ p.eval.obj X ⟶ Y) :
    component r X p (SyntaxPolynomial.parameterComparison Q X p ≫ parameterHom f) =
      SyntaxPolynomial.parameterComparison P X p ≫ parameterHom (prod.map r (𝟙 _) ≫ f) := by
  apply constantFamily_hom_ext
  have h := congrArg (fun a => (a ≫ parameterHom f).left ≫ prod.snd)
    (polynomialMap_comparison r X p)
  simpa only [component_value, Over.comp_left, Over.map_map_left, baseMap,
    Over.homMk_left, Category.assoc, parameterHom, prod.lift_snd] using h

end CategoricalEssentialIncompleteness.V46.ConstantParameterAlgebra
