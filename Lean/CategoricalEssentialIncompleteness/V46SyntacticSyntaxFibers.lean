/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry

/-! # Sigma-one coordinates of actual polynomial objects in parameter slices -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax

/-- Extend two input-fiber predicates through the exact syntax polynomial.
This permits tree-word coordinates in constant source families and underlying
value coordinates in arbitrary target families, without identifying them. -/
def fiberInput (P : Carrier) (t f : 𝚺₁.Semisentence 2) :
    RawPolynomial → 𝚺₁.Semisentence 2
  | .term => t
  | .formula => f
  | .coefficient C => .mkSigma “p u. !P.val p ∧ !C.val u”
  | .unit => .mkSigma “p u. !P.val p ∧ u = 0”
  | .product a b =>
      let A := fiberInput P t f a
      let B := fiberInput P t f b
      .mkSigma “p u. ∃ v w, !pairDef.val u v w ∧ !A.val p v ∧ !B.val p w”
  | .sum a b =>
      let A := fiberInput P t f a
      let B := fiberInput P t f b
      .mkSigma “p u. (∃ v, !pairDef.val u v 0 ∧ !A.val p v) ∨
        (∃ w, !pairDef.val u w 1 ∧ !B.val p w)”

theorem fiberInput_rawFiber (P X Y : Carrier) (ξ υ : Graph) (a : RawPolynomial) :
    fiberInput P (rawFiber P X Y ξ υ .term) (rawFiber P X Y ξ υ .formula) a =
      rawFiber P X Y ξ υ a := by
  induction a with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product a b ia ib =>
      simp only [fiberInput, ia, ib]
      rfl
  | sum a b ia ib =>
      simp only [fiberInput, ia, ib]
      rfl

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- A coordinate graph for each term/formula leaf is extended through
actual products and coproducts of the slice. Coefficients always use the
second projection from their constant family. -/
def representation (P : PredicateCategory T) (X : Over P × Over P)
    (rT rF : TernaryGraph) : SyntaxPolynomial (PredicateCategory T) → TernaryGraph
  | .term => rT
  | .formula => rF
  | .coefficient C =>
      let f := (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph
      let g := (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph
      .mkSigma “p u z. !f.val z p ∧ !g.val z u”
  | .unit =>
      let f := (chosenGraph T (⊤_ (Over P)).hom).graph
      .mkSigma “p u z. !f.val z p ∧ u = 0”
  | .product a b =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      let r := representation P X rT rF a
      let s := representation P X rT rF b
      let f := (chosenGraph T (prod.fst : A ⨯ B ⟶ A).left).graph
      let g := (chosenGraph T (prod.snd : A ⨯ B ⟶ B).left).graph
      .mkSigma “p u z. ∃ v w x y,
        !pairDef.val u v w ∧ !r.val p v x ∧ !s.val p w y ∧ !f.val z x ∧ !g.val z y”
  | .sum a b =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      let r := representation P X rT rF a
      let s := representation P X rT rF b
      let f := (chosenGraph T (coprod.inl : A ⟶ A ⨿ B).left).graph
      let g := (chosenGraph T (coprod.inr : B ⟶ A ⨿ B).left).graph
      .mkSigma “p u z. (∃ v x,
        !pairDef.val u v 0 ∧ !r.val p v x ∧ !f.val x z) ∨
        (∃ w y, !pairDef.val u w 1 ∧ !s.val p w y ∧ !g.val y z)”

def fiberLeaf (P : PredicateCategory T) (X : Over P) : TernaryGraph :=
  let f := (chosenGraph T X.hom).graph
  .mkSigma “p u z. !f.val z p ∧ z = u”

def constantLeaf (P C : PredicateCategory T) : TernaryGraph :=
  let f := (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph
  let g := (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph
  .mkSigma “p u z. !f.val z p ∧ !g.val z u”

def fiberRepresentation (P : PredicateCategory T) (X : Over P × Over P)
    (a : SyntaxPolynomial (PredicateCategory T)) : TernaryGraph :=
  representation T P X (fiberLeaf T P X.1) (fiberLeaf T P X.2) a

def constantRepresentation (P X Y : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) : TernaryGraph :=
  representation T P (constantFamily P X, constantFamily P Y)
    (constantLeaf T P X) (constantLeaf T P Y) a

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P : PredicateCategory T) (X : Over P × Over P) (rT rF : TernaryGraph)

omit [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem representation_coefficient_eval (C : PredicateCategory T) (p u z : M) :
    (representation T P X rT rF (.coefficient C)).val.Evalb ![p, u, z] ↔
      (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z, u] := by
  simp [representation]

omit [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem representation_unit_eval (p u z : M) :
    (representation T P X rT rF .unit).val.Evalb ![p, u, z] ↔
      (chosenGraph T (⊤_ (Over P)).hom).graph.val.Evalb ![z, p] ∧ u = 0 := by
  simp [representation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem representation_product_eval
    (a b : SyntaxPolynomial (PredicateCategory T)) (p u z : M) :
    (representation T P X rT rF (.product a b)).val.Evalb ![p, u, z] ↔
      ∃ v w x y : M, u = Arithmetic.pair v w ∧
        (representation T P X rT rF a).val.Evalb ![p, v, x] ∧
        (representation T P X rT rF b).val.Evalb ![p, w, y] ∧
        (chosenGraph T (prod.fst : (a.withParameters P).eval.obj X ⨯
          (b.withParameters P).eval.obj X ⟶ (a.withParameters P).eval.obj X).left).graph.val.Evalb
            ![z, x] ∧
        (chosenGraph T (prod.snd : (a.withParameters P).eval.obj X ⨯
          (b.withParameters P).eval.obj X ⟶ (b.withParameters P).eval.obj X).left).graph.val.Evalb
            ![z, y] := by simp [representation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem representation_sum_eval
    (a b : SyntaxPolynomial (PredicateCategory T)) (p u z : M) :
    (representation T P X rT rF (.sum a b)).val.Evalb ![p, u, z] ↔
      (∃ v x : M, u = Arithmetic.pair v 0 ∧
        (representation T P X rT rF a).val.Evalb ![p, v, x] ∧
        (chosenGraph T (coprod.inl : (a.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).graph.val.Evalb
            ![x, z]) ∨
      (∃ w y : M, u = Arithmetic.pair w 1 ∧
        (representation T P X rT rF b).val.Evalb ![p, w, y] ∧
        (chosenGraph T (coprod.inr : (b.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).graph.val.Evalb
            ![y, z]) := by simp [representation]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem fiberInput_product_eval (t f : 𝚺₁.Semisentence 2)
    (a b : RawPolynomial) (p u : M) :
    (fiberInput P t f (.product a b)).val.Evalb ![p, u] ↔
      ∃ v w : M, u = Arithmetic.pair v w ∧
        (fiberInput P t f a).val.Evalb ![p, v] ∧
          (fiberInput P t f b).val.Evalb ![p, w] := by simp [fiberInput]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem fiberInput_sum_eval (t f : 𝚺₁.Semisentence 2)
    (a b : RawPolynomial) (p u : M) :
    (fiberInput P t f (.sum a b)).val.Evalb ![p, u] ↔
      (∃ v : M, u = Arithmetic.pair v 0 ∧ (fiberInput P t f a).val.Evalb ![p, v]) ∨
      (∃ w : M, u = Arithmetic.pair w 1 ∧ (fiberInput P t f b).val.Evalb ![p, w]) := by
  simp [fiberInput]

theorem representation_support (t f : 𝚺₁.Semisentence 2)
    (ht : ∀ p u z : M, rT.val.Evalb ![p, u, z] → t.val.Evalb ![p, u] ∧
      X.1.left.val.Evalb ![z] ∧ (chosenGraph T X.1.hom).graph.val.Evalb ![z, p])
    (hf : ∀ p u z : M, rF.val.Evalb ![p, u, z] → f.val.Evalb ![p, u] ∧
      X.2.left.val.Evalb ![z] ∧ (chosenGraph T X.2.hom).graph.val.Evalb ![z, p])
    (a : SyntaxPolynomial (PredicateCategory T)) (p u z : M)
    (h : (representation T P X rT rF a).val.Evalb ![p, u, z]) :
    (fiberInput P t f a).val.Evalb ![p, u] ∧
      ((a.withParameters P).eval.obj X).left.val.Evalb ![z] ∧
        (chosenGraph T ((a.withParameters P).eval.obj X).hom).graph.val.Evalb ![z, p] := by
  induction a generalizing u z with
  | term => exact ht p u z h
  | formula => exact hf p u z h
  | coefficient C =>
      obtain ⟨hzp, hzu⟩ := (representation_coefficient_eval T M P X rT rF C p u z).mp h
      have hs₁ := (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).support_model M z p hzp
      have hs₂ := (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).support_model M z u hzu
      exact ⟨by simpa [fiberInput] using And.intro hs₁.2 hs₂.2, hs₁.1, hzp⟩
  | unit =>
      obtain ⟨hzp, hu⟩ := (representation_unit_eval T M P X rT rF p u z).mp h
      have hs := (chosenGraph T (⊤_ (Over P)).hom).support_model M z p hzp
      exact ⟨by simpa [fiberInput] using And.intro hs.2 hu, hs.1, hzp⟩
  | product a b ia ib =>
      obtain ⟨v, w, x, y, he, hx, hy, hzx, _⟩ :=
        (representation_product_eval T M P X rT rF a b p u z).mp h
      obtain ⟨hv, _, hxp⟩ := ia v x hx
      obtain ⟨hw, _, _⟩ := ib w y hy
      have hz := ((chosenGraph T (prod.fst : (a.withParameters P).eval.obj X ⨯
        (b.withParameters P).eval.obj X ⟶ (a.withParameters P).eval.obj X).left).support_model
          M z x hzx).1
      exact ⟨(fiberInput_product_eval T M P t f a b p u).mpr ⟨v, w, he, hv, hw⟩,
        hz, overGraph_source T M prod.fst z x p hzx hxp⟩
  | sum a b ia ib =>
      rcases (representation_sum_eval T M P X rT rF a b p u z).mp h with
        ⟨v, x, he, hx, hxz⟩ | ⟨w, y, he, hy, hyz⟩
      · obtain ⟨hv, _, hxp⟩ := ia v x hx
        have hz := ((chosenGraph T (coprod.inl : (a.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).support_model
            M x z hxz).2
        exact ⟨(fiberInput_sum_eval T M P t f a b p u).mpr (Or.inl ⟨v, he, hv⟩), hz,
          overGraph_target T M coprod.inl x z p hxz hxp⟩
      · obtain ⟨hw, _, hyp⟩ := ib w y hy
        have hz := ((chosenGraph T (coprod.inr : (b.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).support_model
            M y z hyz).2
        exact ⟨(fiberInput_sum_eval T M P t f a b p u).mpr (Or.inr ⟨w, he, hw⟩), hz,
          overGraph_target T M coprod.inr y z p hyz hyp⟩

theorem fiberRepresentation_support (a : SyntaxPolynomial (PredicateCategory T))
    (p u z : M) (h : (fiberRepresentation T P X a).val.Evalb ![p, u, z]) :
    (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
      (chosenGraph T X.2.hom).graph a).val.Evalb ![p, u] ∧
      ((a.withParameters P).eval.obj X).left.val.Evalb ![z] ∧
        (chosenGraph T ((a.withParameters P).eval.obj X).hom).graph.val.Evalb ![z, p] := by
  let t := rawFiber P X.1.left X.2.left
    (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph .term
  let f := rawFiber P X.1.left X.2.left
    (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph .formula
  have ht : ∀ p u z : M, (fiberLeaf T P X.1).val.Evalb ![p, u, z] →
      t.val.Evalb ![p, u] ∧ X.1.left.val.Evalb ![z] ∧
        (chosenGraph T X.1.hom).graph.val.Evalb ![z, p] := by
    intro p u z h
    have hh : (chosenGraph T X.1.hom).graph.val.Evalb ![z, p] ∧ z = u := by
      simpa [fiberLeaf] using h
    obtain ⟨hzp, hzu⟩ := hh
    subst u
    have hs := (chosenGraph T X.1.hom).support_model M z p hzp
    exact ⟨(rawFiber_term_eval P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph p z).mpr
        ⟨hs.2, hs.1, hzp⟩, hs.1, hzp⟩
  have hf : ∀ p u z : M, (fiberLeaf T P X.2).val.Evalb ![p, u, z] →
      f.val.Evalb ![p, u] ∧ X.2.left.val.Evalb ![z] ∧
        (chosenGraph T X.2.hom).graph.val.Evalb ![z, p] := by
    intro p u z h
    have hh : (chosenGraph T X.2.hom).graph.val.Evalb ![z, p] ∧ z = u := by
      simpa [fiberLeaf] using h
    obtain ⟨hzp, hzu⟩ := hh
    subst u
    have hs := (chosenGraph T X.2.hom).support_model M z p hzp
    exact ⟨(rawFiber_formula_eval P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph p z).mpr
        ⟨hs.2, hs.1, hzp⟩, hs.1, hzp⟩
  have hs := representation_support T M P X (fiberLeaf T P X.1) (fiberLeaf T P X.2)
    t f ht hf a p u z h
  change (fiberInput P
    (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
      (chosenGraph T X.2.hom).graph .term)
    (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
      (chosenGraph T X.2.hom).graph .formula) a).val.Evalb ![p, u] ∧ _ at hs
  rw [fiberInput_rawFiber] at hs
  exact hs

end Models

section LeafModels
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem fiberLeaf_model (P : PredicateCategory T) (X : Over P)
    (p : Obj T M P) (u z : Obj T M X.left) :
    (fiberLeaf T P X).val.Evalb ![p.val, u.val, z.val] ↔
      z = u ∧ (F T M).map X.hom z = p := by
  have h : (fiberLeaf T P X).val.Evalb ![p.val, u.val, z.val] ↔
      (chosenGraph T X.hom).graph.val.Evalb ![z.val, p.val] ∧ z.val = u.val := by
    simp [fiberLeaf]
  rw [h, chosenGraph_map_iff T M X.hom z p]
  constructor
  · rintro ⟨hz, he⟩
    exact ⟨Subtype.ext he, hz⟩
  · rintro ⟨rfl, hu⟩
    exact ⟨hu, rfl⟩

@[simp] theorem constantLeaf_model (P C : PredicateCategory T)
    (p : Obj T M P) (u : Obj T M C) (z : Obj T M (P ⨯ C)) :
    (constantLeaf T P C).val.Evalb ![p.val, u.val, z.val] ↔
      (F T M).map (prod.fst : P ⨯ C ⟶ P) z = p ∧
        (F T M).map (prod.snd : P ⨯ C ⟶ C) z = u := by
  have h : (constantLeaf T P C).val.Evalb ![p.val, u.val, z.val] ↔
      (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z.val, p.val] ∧
        (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z.val, u.val] := by
    simp [constantLeaf]
  exact h.trans (and_congr (chosenGraph_map_iff T M prod.fst z p)
    (chosenGraph_map_iff T M prod.snd z u))

theorem fiberLeaf_existsUnique (P : PredicateCategory T) (X : Over P)
    (p : Obj T M P) (u : Obj T M X.left) (hu : (F T M).map X.hom u = p) :
    ∃! z : Obj T M X.left, (fiberLeaf T P X).val.Evalb ![p.val, u.val, z.val] ∧
      (F T M).map X.hom z = p := by
  refine ⟨u, ⟨(fiberLeaf_model T M P X p u u).mpr ⟨rfl, hu⟩, hu⟩, ?_⟩
  intro z hz
  exact ((fiberLeaf_model T M P X p u z).mp hz.1).1

theorem constantLeaf_existsUnique (P C : PredicateCategory T)
    (p : Obj T M P) (u : Obj T M C) :
    ∃! z : Obj T M (P ⨯ C), (constantLeaf T P C).val.Evalb ![p.val, u.val, z.val] ∧
      (F T M).map (prod.fst : P ⨯ C ⟶ P) z = p := by
  obtain ⟨z, hz₁, hz₂⟩ := modelProduct_exists T M P C p u
  refine ⟨z, ⟨(constantLeaf_model T M P C p u z).mpr ⟨hz₁, hz₂⟩, hz₁⟩, ?_⟩
  intro z' hz'
  obtain ⟨h₁, h₂⟩ := (constantLeaf_model T M P C p u z').mp hz'.1
  exact modelProduct_ext T M (h₁.trans hz₁.symm) (h₂.trans hz₂.symm)

omit [M↓[ℒₒᵣ] ⊧* T] in
theorem fiberLeaf_code_unique (P : PredicateCategory T) (X : Over P)
    (p u v z : M) (h : (fiberLeaf T P X).val.Evalb ![p, u, z])
    (h' : (fiberLeaf T P X).val.Evalb ![p, v, z]) : u = v := by
  have hh : (chosenGraph T X.hom).graph.val.Evalb ![z, p] ∧ z = u := by
    simpa [fiberLeaf] using h
  have hh' : (chosenGraph T X.hom).graph.val.Evalb ![z, p] ∧ z = v := by
    simpa [fiberLeaf] using h'
  have hu := hh.2
  have hv := hh'.2
  exact hu.symm.trans hv

theorem constantLeaf_code_unique (P C : PredicateCategory T)
    (p u v z : M) (h : (constantLeaf T P C).val.Evalb ![p, u, z])
    (h' : (constantLeaf T P C).val.Evalb ![p, v, z]) : u = v := by
  have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z, u] := by
    simpa [constantLeaf] using h
  have hh' : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z, v] := by
    simpa [constantLeaf] using h'
  have hu := hh.2
  have hv := hh'.2
  exact graph_functional_model (chosenGraph T (prod.snd : P ⨯ C ⟶ C)) z u v hu hv

end LeafModels


section CoordinateModels
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P : PredicateCategory T) (X : Over P × Over P) (rT rF : TernaryGraph)

/-- Each valid raw input supplies an actual polynomial point in its parameter
fiber. Only the two leaf-coordinate existence statements are used. -/
theorem representation_exists (t f : 𝚺₁.Semisentence 2)
    (ht : ∀ (p : Obj T M P) (u : M), t.val.Evalb ![p.val, u] →
      ∃ z : Obj T M X.1.left, rT.val.Evalb ![p.val, u, z.val] ∧
        (F T M).map X.1.hom z = p)
    (hf : ∀ (p : Obj T M P) (u : M), f.val.Evalb ![p.val, u] →
      ∃ z : Obj T M X.2.left, rF.val.Evalb ![p.val, u, z.val] ∧
        (F T M).map X.2.hom z = p)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (h : (fiberInput P t f a).val.Evalb ![p.val, u]) :
    ∃ z : Obj T M ((a.withParameters P).eval.obj X).left,
      (representation T P X rT rF a).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map ((a.withParameters P).eval.obj X).hom z = p := by
  induction a generalizing u with
  | term => exact ht p u h
  | formula => exact hf p u h
  | coefficient C =>
      have hh : P.val.Evalb ![p.val] ∧ C.val.Evalb ![u] := by
        simpa [fiberInput] using h
      obtain ⟨z, hz₁, hz₂⟩ := modelProduct_exists T M P C p ⟨u, hh.2⟩
      exact ⟨z, (representation_coefficient_eval T M P X rT rF C p.val u z.val).mpr
        ⟨(chosenGraph_map_iff T M prod.fst z p).mpr hz₁,
          (chosenGraph_map_iff T M prod.snd z ⟨u, hh.2⟩).mpr hz₂⟩, hz₁⟩
  | unit =>
      have hh : P.val.Evalb ![p.val] ∧ u = 0 := by simpa [fiberInput] using h
      obtain ⟨z, hz, _⟩ := modelOverTerminal_existsUnique T M P p
      exact ⟨z, (representation_unit_eval T M P X rT rF p.val u z.val).mpr
        ⟨(chosenGraph_map_iff T M (⊤_ (Over P)).hom z p).mpr hz, hh.2⟩, hz⟩
  | product a b ia ib =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      obtain ⟨v, w, he, hv, hw⟩ := (fiberInput_product_eval T M P t f a b p.val u).mp h
      obtain ⟨x, hx, hxp⟩ := ia v hv
      obtain ⟨y, hy, hyp⟩ := ib w hw
      obtain ⟨z, hz₁, hz₂⟩ := modelOverProduct_exists T M _ _ x y (hxp.trans hyp.symm)
      have hzp := over_value T M (prod.fst : (a.withParameters P).eval.obj X ⨯
        (b.withParameters P).eval.obj X ⟶ (a.withParameters P).eval.obj X) z
      rw [hz₁, hxp] at hzp
      exact ⟨z, (representation_product_eval T M P X rT rF a b p.val u z.val).mpr
        ⟨v, w, x.val, y.val, he, hx, hy,
          (chosenGraph_map_iff T M (prod.fst : A ⨯ B ⟶ A).left z x).mpr hz₁,
          (chosenGraph_map_iff T M (prod.snd : A ⨯ B ⟶ B).left z y).mpr hz₂⟩, hzp.symm⟩
  | sum a b ia ib =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      rcases (fiberInput_sum_eval T M P t f a b p.val u).mp h with
        ⟨v, he, hv⟩ | ⟨w, he, hw⟩
      · obtain ⟨x, hx, hxp⟩ := ia v hv
        let z := (F T M).map (coprod.inl : (a.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left x
        refine ⟨z, (representation_sum_eval T M P X rT rF a b p.val u z.val).mpr
          (Or.inl ⟨v, x.val, he, hx,
            (chosenGraph_map_iff T M (coprod.inl : A ⟶ A ⨿ B).left x z).mpr rfl⟩), ?_⟩
        exact (over_value T M coprod.inl x).trans hxp
      · obtain ⟨y, hy, hyp⟩ := ib w hw
        let z := (F T M).map (coprod.inr : (b.withParameters P).eval.obj X ⟶
          (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left y
        refine ⟨z, (representation_sum_eval T M P X rT rF a b p.val u z.val).mpr
          (Or.inr ⟨w, y.val, he, hy,
            (chosenGraph_map_iff T M (coprod.inr : B ⟶ A ⨿ B).left y z).mpr rfl⟩), ?_⟩
        exact (over_value T M coprod.inr y).trans hyp

/-- A fixed raw coordinate denotes at most one actual polynomial point.
This is proved through the preserved slice products and coproducts. -/
theorem representation_point_unique
    (ht : ∀ (p u : M) (z z' : Obj T M X.1.left),
      rT.val.Evalb ![p, u, z.val] → rT.val.Evalb ![p, u, z'.val] → z = z')
    (hf : ∀ (p u : M) (z z' : Obj T M X.2.left),
      rF.val.Evalb ![p, u, z.val] → rF.val.Evalb ![p, u, z'.val] → z = z')
    (a : SyntaxPolynomial (PredicateCategory T)) (p u : M)
    (z z' : Obj T M ((a.withParameters P).eval.obj X).left)
    (h : (representation T P X rT rF a).val.Evalb ![p, u, z.val])
    (h' : (representation T P X rT rF a).val.Evalb ![p, u, z'.val]) : z = z' := by
  induction a generalizing u with
  | term => exact ht p u z z' h h'
  | formula => exact hf p u z z' h h'
  | coefficient C =>
      obtain ⟨hz₁, hz₂⟩ := (representation_coefficient_eval T M P X rT rF C p u z.val).mp h
      obtain ⟨hz₁', hz₂'⟩ :=
        (representation_coefficient_eval T M P X rT rF C p u z'.val).mp h'
      let pp : Obj T M P := ⟨p, ((chosenGraph T prod.fst).support_model M z.val p hz₁).2⟩
      let uu : Obj T M C := ⟨u, ((chosenGraph T prod.snd).support_model M z.val u hz₂).2⟩
      exact modelProduct_ext T M
        (((chosenGraph_map_iff T M prod.fst z pp).mp hz₁).trans
          ((chosenGraph_map_iff T M prod.fst z' pp).mp hz₁').symm)
        (((chosenGraph_map_iff T M prod.snd z uu).mp hz₂).trans
          ((chosenGraph_map_iff T M prod.snd z' uu).mp hz₂').symm)
  | unit =>
      have hz := ((representation_unit_eval T M P X rT rF p u z.val).mp h).1
      have hz' := ((representation_unit_eval T M P X rT rF p u z'.val).mp h').1
      let pp : Obj T M P :=
        ⟨p, ((chosenGraph T (⊤_ (Over P)).hom).support_model M z.val p hz).2⟩
      obtain ⟨v, _, hv⟩ := modelOverTerminal_existsUnique T M P pp
      exact (hv z ((chosenGraph_map_iff T M (⊤_ (Over P)).hom z pp).mp hz)).trans
        (hv z' ((chosenGraph_map_iff T M (⊤_ (Over P)).hom z' pp).mp hz')).symm
  | product a b ia ib =>
      obtain ⟨v, w, x, y, he, hx, hy, hzx, hzy⟩ :=
        (representation_product_eval T M P X rT rF a b p u z.val).mp h
      obtain ⟨v', w', x', y', he', hx', hy', hzx', hzy'⟩ :=
        (representation_product_eval T M P X rT rF a b p u z'.val).mp h'
      obtain ⟨hv, hw⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he')
      subst v'
      subst w'
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      let xx : Obj T M A.left :=
        ⟨x, ((chosenGraph T (prod.fst : A ⨯ B ⟶ A).left).support_model M z.val x hzx).2⟩
      let xx' : Obj T M A.left :=
        ⟨x', ((chosenGraph T (prod.fst : A ⨯ B ⟶ A).left).support_model M z'.val x' hzx').2⟩
      let yy : Obj T M B.left :=
        ⟨y, ((chosenGraph T (prod.snd : A ⨯ B ⟶ B).left).support_model M z.val y hzy).2⟩
      let yy' : Obj T M B.left :=
        ⟨y', ((chosenGraph T (prod.snd : A ⨯ B ⟶ B).left).support_model M z'.val y' hzy').2⟩
      have hxx := ia v xx xx' hx hx'
      have hyy := ib w yy yy' hy hy'
      exact modelOverProduct_ext T M A B
        (((chosenGraph_map_iff T M (prod.fst : A ⨯ B ⟶ A).left z xx).mp hzx).trans
          (hxx.trans
            ((chosenGraph_map_iff T M (prod.fst : A ⨯ B ⟶ A).left z' xx').mp hzx').symm))
        (((chosenGraph_map_iff T M (prod.snd : A ⨯ B ⟶ B).left z yy).mp hzy).trans
          (hyy.trans
            ((chosenGraph_map_iff T M (prod.snd : A ⨯ B ⟶ B).left z' yy').mp hzy').symm))
  | sum a b ia ib =>
      rcases (representation_sum_eval T M P X rT rF a b p u z.val).mp h with
        ⟨v, x, he, hx, hxz⟩ | ⟨w, y, he, hy, hyz⟩
      · rcases (representation_sum_eval T M P X rT rF a b p u z'.val).mp h' with
          ⟨v', x', he', hx', hxz'⟩ | ⟨w', y', he', _, _⟩
        · have hv := ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he')).1
          subst v'
          let A := (a.withParameters P).eval.obj X
          let B := (b.withParameters P).eval.obj X
          let xx : Obj T M A.left :=
            ⟨x, ((chosenGraph T (coprod.inl : A ⟶ A ⨿ B).left).support_model
              M x z.val hxz).1⟩
          let xx' : Obj T M A.left :=
            ⟨x', ((chosenGraph T (coprod.inl : A ⟶ A ⨿ B).left).support_model
              M x' z'.val hxz').1⟩
          exact ((chosenGraph_map_iff T M (coprod.inl : A ⟶ A ⨿ B).left xx z).mp hxz).symm.trans
            ((congrArg ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left) (ia v xx xx' hx hx')).trans
              ((chosenGraph_map_iff T M (coprod.inl : A ⟶ A ⨿ B).left xx' z').mp hxz'))
        · exact (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he')).2).elim
      · rcases (representation_sum_eval T M P X rT rF a b p u z'.val).mp h' with
          ⟨v', x', he', _, _⟩ | ⟨w', y', he', hy', hyz'⟩
        · exact (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)).2).elim
        · have hw := ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he')).1
          subst w'
          let A := (a.withParameters P).eval.obj X
          let B := (b.withParameters P).eval.obj X
          let yy : Obj T M B.left :=
            ⟨y, ((chosenGraph T (coprod.inr : B ⟶ A ⨿ B).left).support_model
              M y z.val hyz).1⟩
          let yy' : Obj T M B.left :=
            ⟨y', ((chosenGraph T (coprod.inr : B ⟶ A ⨿ B).left).support_model
              M y' z'.val hyz').1⟩
          exact ((chosenGraph_map_iff T M (coprod.inr : B ⟶ A ⨿ B).left yy z).mp hyz).symm.trans
            ((congrArg ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left) (ib w yy yy' hy hy')).trans
              ((chosenGraph_map_iff T M (coprod.inr : B ⟶ A ⨿ B).left yy' z').mp hyz'))


/-- The underlying-value leaf coordinates used for an arbitrary target
family give a unique point for every valid raw fiber input. -/
theorem fiberRepresentation_existsUnique
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (h : (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
      (chosenGraph T X.2.hom).graph a).val.Evalb ![p.val, u]) :
    ∃! z : Obj T M ((a.withParameters P).eval.obj X).left,
      (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val] := by
  let t := rawFiber P X.1.left X.2.left
    (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph .term
  let f := rawFiber P X.1.left X.2.left
    (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph .formula
  have ht : ∀ (p : Obj T M P) (u : M), t.val.Evalb ![p.val, u] →
      ∃ z : Obj T M X.1.left, (fiberLeaf T P X.1).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map X.1.hom z = p := by
    intro p u hu
    obtain ⟨_, hu, hup⟩ := (rawFiber_term_eval P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph p.val u).mp hu
    let uu : Obj T M X.1.left := ⟨u, hu⟩
    have hp := (chosenGraph_map_iff T M X.1.hom uu p).mp hup
    exact ⟨uu, (fiberLeaf_model T M P X.1 p uu uu).mpr ⟨rfl, hp⟩, hp⟩
  have hf : ∀ (p : Obj T M P) (u : M), f.val.Evalb ![p.val, u] →
      ∃ z : Obj T M X.2.left, (fiberLeaf T P X.2).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map X.2.hom z = p := by
    intro p u hu
    obtain ⟨_, hu, hup⟩ := (rawFiber_formula_eval P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph p.val u).mp hu
    let uu : Obj T M X.2.left := ⟨u, hu⟩
    have hp := (chosenGraph_map_iff T M X.2.hom uu p).mp hup
    exact ⟨uu, (fiberLeaf_model T M P X.2 p uu uu).mpr ⟨rfl, hp⟩, hp⟩
  have hi : (fiberInput P t f a).val.Evalb ![p.val, u] := by
    change (fiberInput P (rawFiber P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph .term)
      (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
        (chosenGraph T X.2.hom).graph .formula) a).val.Evalb ![p.val, u]
    rw [fiberInput_rawFiber]
    exact h
  obtain ⟨z, hz, _⟩ := representation_exists T M P X
    (fiberLeaf T P X.1) (fiberLeaf T P X.2) t f ht hf a p u hi
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  apply representation_point_unique T M P X (fiberLeaf T P X.1) (fiberLeaf T P X.2)
    (a := a) (p := p.val) (u := u) (z := z') (z' := z) _ _ hz' hz
  · intro p u z z' h h'
    have hz : z.val = u := by
      have hh : (chosenGraph T X.1.hom).graph.val.Evalb ![z.val, p] ∧ z.val = u := by
        simpa [fiberLeaf] using h
      exact hh.2
    have hz' : z'.val = u := by
      have hh : (chosenGraph T X.1.hom).graph.val.Evalb ![z'.val, p] ∧ z'.val = u := by
        simpa [fiberLeaf] using h'
      exact hh.2
    exact Subtype.ext (hz.trans hz'.symm)
  · intro p u z z' h h'
    have hz : z.val = u := by
      have hh : (chosenGraph T X.2.hom).graph.val.Evalb ![z.val, p] ∧ z.val = u := by
        simpa [fiberLeaf] using h
      exact hh.2
    have hz' : z'.val = u := by
      have hh : (chosenGraph T X.2.hom).graph.val.Evalb ![z'.val, p] ∧ z'.val = u := by
        simpa [fiberLeaf] using h'
      exact hh.2
    exact Subtype.ext (hz.trans hz'.symm)

end CoordinateModels

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
