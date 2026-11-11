/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeNodeGeometry
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitution

/-! # Literal native nodes of the actual uniform word algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding
section FramedPoints
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)

private theorem framed_comp_eq_constant (R : Total.TotalCategory P) (r : (U).obj R)
    {A : Over R} (X : Total.TotalCategory P) (f : PointFrame.source R r ⟶ A)
    (g : A ⟶ constantFamily R X) (x : (U).obj X)
    (h : (U).map g.left ((U).map f.left ⟨0,rfl⟩)=Points.pairPoint r x) :
    f ≫ g=PointFrame.constant R r X x := by
  apply Over.OverMorphism.ext
  apply (Total.pointHomEquiv (constantFamily R X).left).symm.injective
  change (U).map (f.left ≫ g.left) ⟨0,rfl⟩=
    (U).map (PointFrame.constant R r X x).left ⟨0,rfl⟩
  exact (CategoryTheory.Functor.map_comp_apply (U) f.left g.left ⟨0,rfl⟩).trans
    (h.trans (PointFrame.constant_point R r X x).symm)
end FramedPoints

variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A" => SyntaxPolynomial.algebraWithParameters p q
  (CategoricalSyntax.algebra (NamedProofImage.syntaxData P σ π d)) R

private theorem termLeaf_code (r : (U).obj (R)) (t : Tm) :
    ((U).map ((termLeaf P σ π d r t).left ≫ prod.snd) ⟨0,rfl⟩).val=termCode t := by
  rw [CategoryTheory.Functor.map_comp_apply]
  change ((U).map prod.snd ((U).map (PointFrame.constant (R) r (S).algebra.a.1
    (termPoint P σ π d t)).left ⟨0,rfl⟩)).val=_
  rw [PointFrame.constant_point,Points.pairPoint_snd]
  exact termPoint_value P σ π d t

private theorem formulaLeaf_code (r : (U).obj (R)) (φ : Fm) :
    ((U).map ((formulaLeaf P σ π d r φ).left ≫ prod.snd) ⟨0,rfl⟩).val=formulaCode φ := by
  rw [CategoryTheory.Functor.map_comp_apply]
  change ((U).map prod.snd ((U).map (PointFrame.constant (R) r (S).algebra.a.2
    (formulaPoint P σ π d φ)).left ⟨0,rfl⟩)).val=_
  rw [PointFrame.constant_point,Points.pairPoint_snd]
  exact formulaPoint_value P σ π d φ

private def nativeTermPayload : Tm → ℕ
  | .var x => Arithmetic.pair x 0
  | .app k c children => Arithmetic.pair
      (arityInput d k (Arithmetic.pair c.val (childTuple k.val (fun i => termCode (children i))))) 1

private def nativeFormulaPayload : Fm → ℕ
  | .equal u v => equalInput (termCode u) (termCode v)
  | .relation k c children => relationInput d k c.val (fun i => termCode (children i))
  | .neg body => negInput (formulaCode body)
  | .imp left right => impInput (formulaCode left) (formulaCode right)
  | .all x body => allInput x (formulaCode body)

private theorem term_node_input_code (r : (U).obj (R)) (t : Tm) :
    PointFrame.nodeInputCode (R) r (S).algebra.a.1 (S).algebra.a.2 (p)
        (termNodeInput P σ π d r t)=nativeTermPayload σ d t := by
  cases t with
  | var x =>
      change Nat.pair x 0=Arithmetic.pair x 0
      exact (Arithmetic.nat_pair_eq 0 x).symm
  | app k c children =>
      change Nat.pair (PointFrame.nodeInputCode (R) r (S).algebra.a.1 (S).algebra.a.2
        (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
        (PointFrame.arityData (R) r (constantFamily (R) (S).algebra.a.1,constantFamily (R) (S).algebra.a.2) (fun n => (F).obj (σ n)) d k
          (sourcePoint P (σ k.val) c) (fun i => termLeaf P σ π d r (children i)))) 1=_
      rw [PointFrame.nodeInputCode_arityData (R) r (S).algebra.a.1 (S).algebra.a.2
        (fun n => (F).obj (σ n)) d k (sourcePoint P (σ k.val) c)
          (fun i => termLeaf P σ π d r (children i))]
      simp only [nativeTermPayload,sourcePoint,Arithmetic.nat_pair_eq,termLeaf_code]

private theorem formula_node_input_code (r : (U).obj (R)) (φ : Fm) :
    PointFrame.nodeInputCode (R) r (S).algebra.a.1 (S).algebra.a.2 (q)
        (formulaNodeInput P σ π d r φ)=nativeFormulaPayload σ π d φ := by
  cases φ with
  | equal u v =>
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
        PointFrame.nodeInputCode,nativeFormulaPayload,
        equalInput,Arithmetic.nat_pair_eq,termLeaf_code]
  | relation k c children =>
      change Nat.pair (Nat.pair (Nat.pair (Nat.pair
        (PointFrame.nodeInputCode (R) r (S).algebra.a.1 (S).algebra.a.2
          (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d)
          (PointFrame.arityData (R) r (constantFamily (R) (S).algebra.a.1,constantFamily (R) (S).algebra.a.2) (fun n => (F).obj (π n)) d k
            (sourcePoint P (π k.val) c) (fun i => termLeaf P σ π d r (children i)))) 1) 0) 0) 0=_
      rw [PointFrame.nodeInputCode_arityData (R) r (S).algebra.a.1 (S).algebra.a.2
        (fun n => (F).obj (π n)) d k (sourcePoint P (π k.val) c)
          (fun i => termLeaf P σ π d r (children i))]
      simp only [nativeFormulaPayload,relationInput,sourcePoint,Arithmetic.nat_pair_eq,termLeaf_code]
  | neg body =>
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
        PointFrame.nodeInputCode,nativeFormulaPayload,
        negInput,Arithmetic.nat_pair_eq,formulaLeaf_code]
  | imp left right =>
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
        PointFrame.nodeInputCode,nativeFormulaPayload,
        impInput,Arithmetic.nat_pair_eq,formulaLeaf_code]
  | all x body =>
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
        PointFrame.nodeInputCode,nativeFormulaPayload,
        allInput,Arithmetic.nat_pair_eq,formulaLeaf_code,Points.namePoint,
        sourcePoint,SyntacticNamedHilbert.namePoint]

private theorem term_constructor_code (u : ℕ) :
    SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton (p)) u=
      SyntacticSyntax.Coding.constructor false (termPolynomial σ d) u := by
  have h := NamedSyntaxComparison.termExpression_mapped P
    (variableCarrier : PredicateCategory 𝗣𝗔) σ d
  have hh := congrArg (fun a => SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton a) u) h
  exact hh.symm.trans (Syntax.Raw.wordAlgebra_mapped_constructor (P := P) (termPolynomial σ d) false u)

private theorem formula_constructor_code (u : ℕ) :
    SyntacticSyntax.Coding.constructor true (Syntax.Raw.skeleton (q)) u=
      SyntacticSyntax.Coding.constructor true (formulaPolynomial π d) u := by
  have h := NamedSyntaxComparison.formulaExpression_mapped P
    (variableCarrier : PredicateCategory 𝗣𝗔) π d
  have hh := congrArg (fun a => SyntacticSyntax.Coding.constructor true (Syntax.Raw.skeleton a) u) h
  exact hh.symm.trans (Syntax.Raw.wordAlgebra_mapped_constructor (P := P) (formulaPolynomial π d) true u)

private theorem term_node_base_value (r : (U).obj (R)) (t : Tm) :
    (U).map (PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (p)
        (termNodeInput P σ π d r t) ≫ (S).algebra.str.1) ⟨0,rfl⟩=termPoint P σ π d t := by
  apply Subtype.ext
  let f := PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (p)
    (termNodeInput P σ π d r t)
  let z := (U).map (f ≫ (Syntax.Raw.baseComparison (S).algebra.a.1 (S).algebra.a.2 (p)).inv) ⟨0,rfl⟩
  have hc := (Syntax.Raw.rawWordConstructor_graph (P := P) (p) (q) false z.val
    (((U).map (Syntax.Raw.rawWordConstructor (p) (q) false) z).val)).mp
      (Total.totalFunction_mem (Syntax.Raw.rawWordConstructor (p) (q) false) z)
  have hz : z.val=nativeTermPayload σ d t :=
    (PointFrame.nodeBaseArrow_code (R) r (S).algebra.a.1 (S).algebra.a.2 (p) _).trans
      (term_node_input_code P σ π d r t)
  change ((U).map (f ≫ ((Syntax.Raw.baseComparison (S).algebra.a.1 (S).algebra.a.2 (p)).inv ≫
    Syntax.Raw.rawWordConstructor (p) (q) false)) ⟨0,rfl⟩).val=(termPoint P σ π d t).val
  rw [← Category.assoc,CategoryTheory.Functor.map_comp_apply]
  change ((U).map (Syntax.Raw.rawWordConstructor (p) (q) false) z).val=_
  rw [hc.2,hz]
  change SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton (p))
    (nativeTermPayload σ d t)=(termPoint P σ π d t).val
  rw [term_constructor_code P σ d,termPoint_value P σ π d]
  cases t <;> rfl

private theorem formula_node_base_value (r : (U).obj (R)) (φ : Fm) :
    (U).map (PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (q)
        (formulaNodeInput P σ π d r φ) ≫ (S).algebra.str.2) ⟨0,rfl⟩=formulaPoint P σ π d φ := by
  apply Subtype.ext
  let f := PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (q)
    (formulaNodeInput P σ π d r φ)
  let z := (U).map (f ≫ (Syntax.Raw.baseComparison (S).algebra.a.1 (S).algebra.a.2 (q)).inv) ⟨0,rfl⟩
  have hc := (Syntax.Raw.rawWordConstructor_graph (P := P) (p) (q) true z.val
    (((U).map (Syntax.Raw.rawWordConstructor (p) (q) true) z).val)).mp
      (Total.totalFunction_mem (Syntax.Raw.rawWordConstructor (p) (q) true) z)
  have hz : z.val=nativeFormulaPayload σ π d φ :=
    (PointFrame.nodeBaseArrow_code (R) r (S).algebra.a.1 (S).algebra.a.2 (q) _).trans
      (formula_node_input_code P σ π d r φ)
  change ((U).map (f ≫ ((Syntax.Raw.baseComparison (S).algebra.a.1 (S).algebra.a.2 (q)).inv ≫
    Syntax.Raw.rawWordConstructor (p) (q) true)) ⟨0,rfl⟩).val=(formulaPoint P σ π d φ).val
  rw [← Category.assoc,CategoryTheory.Functor.map_comp_apply]
  change ((U).map (Syntax.Raw.rawWordConstructor (p) (q) true) z).val=_
  rw [hc.2,hz]
  change SyntacticSyntax.Coding.constructor true (Syntax.Raw.skeleton (q))
    (nativeFormulaPayload σ π d φ)=(formulaPoint P σ π d φ).val
  rw [formula_constructor_code P π d,formulaPoint_value P σ π d]
  cases φ <;> rfl

private theorem nodeFrame_point {R₁ X : Total.TotalCategory P} (r : (U).obj R₁)
    (f : (PointFrame.source R₁ r).left ⟶ X) :
    (U).map (nodeFrame (Total.underlyingPoint r) f).left ⟨0,rfl⟩=
      Points.pairPoint r ((U).map f ⟨0,rfl⟩) := by
  change (U).map (prod.lift (Total.underlyingPoint r) f) ⟨0,rfl⟩=_
  exact (Points.lift_point _ _ _).trans
    (congrArg (fun x => Points.pairPoint x ((U).map f ⟨0,rfl⟩))
      ((Total.pointHomEquiv R₁).left_inv r))

/-- Every native term node realizes its exact frame and original term. -/
theorem term_node_realizes (r : (U).obj (R)) (t : Tm) :
    (U).map (A).str.1.left
        ((U).map (PointFrame.realize (R) r (A).a (p) (termNodeInput P σ π d r t)).left ⟨0,rfl⟩)=
      Points.pairPoint r (termPoint P σ π d t) := by
  have h := congrArg (fun f : PointFrame.source (R) r ⟶ (A).a.1 => (U).map f.left ⟨0,rfl⟩)
    (PointFrame.realize_parameterTerm (R) r (p) (q) (S).algebra (termNodeInput P σ π d r t))
  change (U).map ((PointFrame.realize (R) r (A).a (p)
    (termNodeInput P σ π d r t)).left ≫ (A).str.1.left) ⟨0,rfl⟩=_ at h
  rw [CategoryTheory.Functor.map_comp_apply] at h
  exact h.trans ((nodeFrame_point P r
    (PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (p)
      (termNodeInput P σ π d r t) ≫ (S).algebra.str.1)).trans
        (congrArg (Points.pairPoint r) (term_node_base_value P σ π d r t)))

/-- Every native formula node realizes its exact frame and original formula. -/
theorem formula_node_realizes (r : (U).obj (R)) (φ : Fm) :
    (U).map (A).str.2.left
        ((U).map (PointFrame.realize (R) r (A).a (q) (formulaNodeInput P σ π d r φ)).left ⟨0,rfl⟩)=
      Points.pairPoint r (formulaPoint P σ π d φ) := by
  have h := congrArg (fun f : PointFrame.source (R) r ⟶ (A).a.2 => (U).map f.left ⟨0,rfl⟩)
    (PointFrame.realize_parameterFormula (R) r (p) (q) (S).algebra (formulaNodeInput P σ π d r φ))
  change (U).map ((PointFrame.realize (R) r (A).a (q)
    (formulaNodeInput P σ π d r φ)).left ≫ (A).str.2.left) ⟨0,rfl⟩=_ at h
  rw [CategoryTheory.Functor.map_comp_apply] at h
  exact h.trans ((nodeFrame_point P r
    (PointFrame.nodeBaseArrow (R) r (S).algebra.a.1 (S).algebra.a.2 (q)
      (formulaNodeInput P σ π d r φ) ≫ (S).algebra.str.2)).trans
        (congrArg (Points.pairPoint r) (formula_node_base_value P σ π d r φ)))

/-- The point equation determines the actual morphism from the frame. -/
theorem term_node_realizes_hom (r : (U).obj (R)) (t : Tm) :
    PointFrame.realize (R) r (A).a (p) (termNodeInput P σ π d r t) ≫ (A).str.1=
      PointFrame.constant (R) r (S).algebra.a.1 (termPoint P σ π d t) := by
  exact framed_comp_eq_constant (R) r (S).algebra.a.1
    (PointFrame.realize (R) r (A).a (p) (termNodeInput P σ π d r t))
    (A).str.1 (termPoint P σ π d t) (term_node_realizes P σ π d r t)

theorem formula_node_realizes_hom (r : (U).obj (R)) (φ : Fm) :
    PointFrame.realize (R) r (A).a (q) (formulaNodeInput P σ π d r φ) ≫ (A).str.2=
      PointFrame.constant (R) r (S).algebra.a.2 (formulaPoint P σ π d φ) := by
  exact framed_comp_eq_constant (R) r (S).algebra.a.2
    (PointFrame.realize (R) r (A).a (q) (formulaNodeInput P σ π d r φ))
    (A).str.2 (formulaPoint P σ π d φ) (formula_node_realizes P σ π d r φ)

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
