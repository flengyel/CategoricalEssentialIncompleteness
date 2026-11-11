/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry

/-! # Sigma-one representations of chosen categorical polynomial points -/

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
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Input is the canonical numerical polynomial code, output a point of
the actual chosen categorical polynomial object. No syntax parser is used. -/
def baseRepresentation (X Y : PredicateCategory T) :
    SyntaxPolynomial (PredicateCategory T) → Graph
  | .term => .mkSigma “u z. !X.val z ∧ z = u”
  | .formula => .mkSigma “u z. !Y.val z ∧ z = u”
  | .coefficient C => .mkSigma “u z. !C.val z ∧ z = u”
  | .unit =>
      let C := (⊤_ (PredicateCategory T))
      .mkSigma “u z. !C.val z ∧ u = 0”
  | .product a b =>
      let A := a.eval.obj (X, Y)
      let B := b.eval.obj (X, Y)
      let r := baseRepresentation X Y a
      let s := baseRepresentation X Y b
      let f := (chosenGraph T (prod.fst : A ⨯ B ⟶ A)).graph
      let g := (chosenGraph T (prod.snd : A ⨯ B ⟶ B)).graph
      .mkSigma “u z. ∃ v w x y,
        !pairDef.val u v w ∧ !r.val v x ∧ !s.val w y ∧ !f.val z x ∧ !g.val z y”
  | .sum a b =>
      let A := a.eval.obj (X, Y)
      let B := b.eval.obj (X, Y)
      let r := baseRepresentation X Y a
      let s := baseRepresentation X Y b
      let f := (chosenGraph T (coprod.inl : A ⟶ A ⨿ B)).graph
      let g := (chosenGraph T (coprod.inr : B ⟶ A ⨿ B)).graph
      .mkSigma “u z. (∃ v x, !pairDef.val u v 0 ∧ !r.val v x ∧ !f.val x z) ∨
        (∃ w y, !pairDef.val u w 1 ∧ !s.val w y ∧ !g.val y z)”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable (X Y : PredicateCategory T)

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_term_eval (u z : M) :
    (baseRepresentation T X Y .term).val.Evalb ![u, z] ↔ X.val.Evalb ![z] ∧ z = u := by
  simp [baseRepresentation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_formula_eval (u z : M) :
    (baseRepresentation T X Y .formula).val.Evalb ![u, z] ↔ Y.val.Evalb ![z] ∧ z = u := by
  simp [baseRepresentation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_coefficient_eval (C : PredicateCategory T) (u z : M) :
    (baseRepresentation T X Y (.coefficient C)).val.Evalb ![u, z] ↔
      C.val.Evalb ![z] ∧ z = u := by simp [baseRepresentation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_unit_eval (u z : M) :
    (baseRepresentation T X Y .unit).val.Evalb ![u, z] ↔
      (⊤_ (PredicateCategory T)).val.Evalb ![z] ∧ u = 0 := by simp [baseRepresentation]

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_product_eval
    (a b : SyntaxPolynomial (PredicateCategory T)) (u z : M) :
    (baseRepresentation T X Y (.product a b)).val.Evalb ![u, z] ↔
      ∃ v w x y : M, u = Arithmetic.pair v w ∧
        (baseRepresentation T X Y a).val.Evalb ![v, x] ∧
        (baseRepresentation T X Y b).val.Evalb ![w, y] ∧
        (chosenGraph T (prod.fst : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y))).graph.val.Evalb ![z, x] ∧
        (chosenGraph T (prod.snd : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
          b.eval.obj (X, Y))).graph.val.Evalb ![z, y] := by simp [baseRepresentation]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem baseRepresentation_sum_eval
    (a b : SyntaxPolynomial (PredicateCategory T)) (u z : M) :
    (baseRepresentation T X Y (.sum a b)).val.Evalb ![u, z] ↔
      (∃ v x : M, u = Arithmetic.pair v 0 ∧
        (baseRepresentation T X Y a).val.Evalb ![v, x] ∧
        (chosenGraph T (coprod.inl : a.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))).graph.val.Evalb ![x, z]) ∨
      (∃ w y : M, u = Arithmetic.pair w 1 ∧
        (baseRepresentation T X Y b).val.Evalb ![w, y] ∧
        (chosenGraph T (coprod.inr : b.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))).graph.val.Evalb ![y, z]) := by
  simp [baseRepresentation]

theorem baseRepresentation_support (a : SyntaxPolynomial (PredicateCategory T))
    (u z : M) (h : (baseRepresentation T X Y a).val.Evalb ![u, z]) :
    (rawCarrier X Y a).val.Evalb ![u] ∧ (a.eval.obj (X, Y)).val.Evalb ![z] := by
  induction a generalizing u z with
  | term =>
      obtain ⟨hz, rfl⟩ := (baseRepresentation_term_eval T M X Y u z).mp h
      exact ⟨hz, hz⟩
  | formula =>
      obtain ⟨hz, rfl⟩ := (baseRepresentation_formula_eval T M X Y u z).mp h
      exact ⟨hz, hz⟩
  | coefficient C =>
      obtain ⟨hz, rfl⟩ := (baseRepresentation_coefficient_eval T M X Y C u z).mp h
      exact ⟨hz, hz⟩
  | unit =>
      obtain ⟨hz, hu⟩ := (baseRepresentation_unit_eval T M X Y u z).mp h
      exact ⟨by simpa [rawCarrier] using hu, hz⟩
  | product a b ia ib =>
      obtain ⟨v, w, x, y, he, hx, hy, hf, _⟩ :=
        (baseRepresentation_product_eval T M X Y a b u z).mp h
      refine ⟨(rawCarrier_product_eval X Y a b u).mpr
        ⟨v, w, he, (ia v x hx).1, (ib w y hy).1⟩, ?_⟩
      exact ((chosenGraph T (prod.fst : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
        a.eval.obj (X, Y))).support_model M z x hf).1
  | sum a b ia ib =>
      rcases (baseRepresentation_sum_eval T M X Y a b u z).mp h with
        ⟨v, x, he, hx, hf⟩ | ⟨w, y, he, hy, hg⟩
      · exact ⟨(rawCarrier_sum_eval X Y a b u).mpr (Or.inl ⟨v, he, (ia v x hx).1⟩),
          ((chosenGraph T (coprod.inl : a.eval.obj (X, Y) ⟶
            a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))).support_model M x z hf).2⟩
      · exact ⟨(rawCarrier_sum_eval X Y a b u).mpr (Or.inr ⟨w, he, (ib w y hy).1⟩),
          ((chosenGraph T (coprod.inr : b.eval.obj (X, Y) ⟶
            a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))).support_model M y z hg).2⟩

/-- Every literal polynomial input has a point in the actual chosen
categorical polynomial object, including zero-arity unit inputs. -/
theorem baseRepresentation_exists (a : SyntaxPolynomial (PredicateCategory T))
    (u : M) (hu : (rawCarrier X Y a).val.Evalb ![u]) :
    ∃ z : Obj T M (a.eval.obj (X, Y)),
      (baseRepresentation T X Y a).val.Evalb ![u, z.val] := by
  induction a generalizing u with
  | term =>
      exact ⟨⟨u, hu⟩, (baseRepresentation_term_eval T M X Y u u).mpr ⟨hu, rfl⟩⟩
  | formula =>
      exact ⟨⟨u, hu⟩, (baseRepresentation_formula_eval T M X Y u u).mpr ⟨hu, rfl⟩⟩
  | coefficient C =>
      exact ⟨⟨u, hu⟩, (baseRepresentation_coefficient_eval T M X Y C u u).mpr ⟨hu, rfl⟩⟩
  | unit =>
      let z := modelTerminalPoint T M
      exact ⟨z, (baseRepresentation_unit_eval T M X Y u z.val).mpr
        ⟨z.property, by simpa [rawCarrier] using hu⟩⟩
  | product a b ia ib =>
      obtain ⟨v, w, he, hv, hw⟩ := (rawCarrier_product_eval X Y a b u).mp hu
      obtain ⟨x, hx⟩ := ia v hv
      obtain ⟨y, hy⟩ := ib w hw
      obtain ⟨z, hz₁, hz₂⟩ := modelProduct_exists T M
        (a.eval.obj (X, Y)) (b.eval.obj (X, Y)) x y
      exact ⟨z, (baseRepresentation_product_eval T M X Y a b u z.val).mpr
        ⟨v, w, x.val, y.val, he, hx, hy,
          (chosenGraph_map_iff T M prod.fst z x).mpr hz₁,
          (chosenGraph_map_iff T M prod.snd z y).mpr hz₂⟩⟩
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval X Y a b u).mp hu with
        ⟨v, he, hv⟩ | ⟨w, he, hw⟩
      · obtain ⟨x, hx⟩ := ia v hv
        let z := (F T M).map (coprod.inl : a.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y)) x
        exact ⟨z, (baseRepresentation_sum_eval T M X Y a b u z.val).mpr
          (Or.inl ⟨v, x.val, he, hx, (chosenGraph_map_iff T M coprod.inl x z).mpr rfl⟩)⟩
      · obtain ⟨y, hy⟩ := ib w hw
        let z := (F T M).map (coprod.inr : b.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y)) y
        exact ⟨z, (baseRepresentation_sum_eval T M X Y a b u z.val).mpr
          (Or.inr ⟨w, y.val, he, hy, (chosenGraph_map_iff T M coprod.inr y z).mpr rfl⟩)⟩

/-- Every interpreted categorical point is represented, rather than only
points obtained from standard external numerals. -/
theorem baseRepresentation_cover (a : SyntaxPolynomial (PredicateCategory T))
    (z : Obj T M (a.eval.obj (X, Y))) :
    ∃ u : M, (baseRepresentation T X Y a).val.Evalb ![u, z.val] := by
  induction a with
  | term => exact ⟨z.val, (baseRepresentation_term_eval T M X Y _ _).mpr ⟨z.property, rfl⟩⟩
  | formula =>
      exact ⟨z.val, (baseRepresentation_formula_eval T M X Y _ _).mpr ⟨z.property, rfl⟩⟩
  | coefficient C =>
      exact ⟨z.val, (baseRepresentation_coefficient_eval T M X Y C _ _).mpr
        ⟨z.property, rfl⟩⟩
  | unit => exact ⟨0, (baseRepresentation_unit_eval T M X Y _ _).mpr ⟨z.property, rfl⟩⟩
  | product a b ia ib =>
      let x := (F T M).map (prod.fst : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
        a.eval.obj (X, Y)) z
      let y := (F T M).map (prod.snd : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
        b.eval.obj (X, Y)) z
      obtain ⟨v, hv⟩ := ia x
      obtain ⟨w, hw⟩ := ib y
      exact ⟨Arithmetic.pair v w,
        (baseRepresentation_product_eval T M X Y a b _ z.val).mpr
          ⟨v, w, x.val, y.val, rfl, hv, hw,
            (chosenGraph_map_iff T M prod.fst z x).mpr rfl,
            (chosenGraph_map_iff T M prod.snd z y).mpr rfl⟩⟩
  | sum a b ia ib =>
      rcases modelSum_cases T M (a.eval.obj (X, Y)) (b.eval.obj (X, Y)) z with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · obtain ⟨v, hv⟩ := ia x
        exact ⟨Arithmetic.pair v 0, (baseRepresentation_sum_eval T M X Y a b _ z.val).mpr
          (Or.inl ⟨v, x.val, rfl, hv, (chosenGraph_map_iff T M coprod.inl x z).mpr hx⟩)⟩
      · obtain ⟨w, hw⟩ := ib y
        exact ⟨Arithmetic.pair w 1, (baseRepresentation_sum_eval T M X Y a b _ z.val).mpr
          (Or.inr ⟨w, y.val, rfl, hw, (chosenGraph_map_iff T M coprod.inr y z).mpr hy⟩)⟩

theorem baseRepresentation_code_unique (a : SyntaxPolynomial (PredicateCategory T))
    (u v z : M) (h : (baseRepresentation T X Y a).val.Evalb ![u, z])
    (h' : (baseRepresentation T X Y a).val.Evalb ![v, z]) : u = v := by
  induction a generalizing u v z with
  | term =>
      exact ((baseRepresentation_term_eval T M X Y u z).mp h).2.symm.trans
        ((baseRepresentation_term_eval T M X Y v z).mp h').2
  | formula =>
      exact ((baseRepresentation_formula_eval T M X Y u z).mp h).2.symm.trans
        ((baseRepresentation_formula_eval T M X Y v z).mp h').2
  | coefficient C =>
      exact ((baseRepresentation_coefficient_eval T M X Y C u z).mp h).2.symm.trans
        ((baseRepresentation_coefficient_eval T M X Y C v z).mp h').2
  | unit =>
      exact ((baseRepresentation_unit_eval T M X Y u z).mp h).2.trans
        ((baseRepresentation_unit_eval T M X Y v z).mp h').2.symm
  | product a b ia ib =>
      obtain ⟨u₁, u₂, x, y, hu, hx, hy, hf, hg⟩ :=
        (baseRepresentation_product_eval T M X Y a b u z).mp h
      obtain ⟨v₁, v₂, x', y', hv, hx', hy', hf', hg'⟩ :=
        (baseRepresentation_product_eval T M X Y a b v z).mp h'
      have hxx := graph_functional_model (chosenGraph T
        (prod.fst : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶ a.eval.obj (X, Y)))
          z x x' hf hf'
      have hyy := graph_functional_model (chosenGraph T
        (prod.snd : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶ b.eval.obj (X, Y)))
          z y y' hg hg'
      subst x'
      subst y'
      exact hu.trans ((congrArg₂ Arithmetic.pair (ia u₁ v₁ x hx hx')
        (ib u₂ v₂ y hy hy')).trans hv.symm)
  | sum a b ia ib =>
      rcases (baseRepresentation_sum_eval T M X Y a b u z).mp h with
        ⟨u₁, x, hu, hx, hf⟩ | ⟨u₂, y, hu, hy, hg⟩
      · rcases (baseRepresentation_sum_eval T M X Y a b v z).mp h' with
          ⟨v₁, x', hv, hx', hf'⟩ | ⟨v₂, y', hv, hy', hg'⟩
        · have hxx := chosenGraph_input_unique T M
            (coprod.inl : a.eval.obj (X, Y) ⟶ a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))
            (preservedSum_properties (F T M) (a.eval.obj (X, Y))
              (b.eval.obj (X, Y))).1 x x' z hf hf'
          subst x'
          exact hu.trans ((congrArg (fun q => Arithmetic.pair q 0)
            (ia u₁ v₁ x hx hx')).trans hv.symm)
        · exact (modelSum_graph_disjoint T M (a.eval.obj (X, Y))
            (b.eval.obj (X, Y)) x y' z hf hg').elim
      · rcases (baseRepresentation_sum_eval T M X Y a b v z).mp h' with
          ⟨v₁, x', hv, hx', hf'⟩ | ⟨v₂, y', hv, hy', hg'⟩
        · exact (modelSum_graph_disjoint T M (a.eval.obj (X, Y))
            (b.eval.obj (X, Y)) x' y z hf' hg).elim
        · have hyy := chosenGraph_input_unique T M
            (coprod.inr : b.eval.obj (X, Y) ⟶ a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y))
            (preservedSum_properties (F T M) (a.eval.obj (X, Y))
              (b.eval.obj (X, Y))).2.1 y y' z hg hg'
          subst y'
          exact hu.trans ((congrArg (fun q => Arithmetic.pair q 1)
            (ib u₂ v₂ y hy hy')).trans hv.symm)

end Models

/-- The numerical encoding is a genuine T-provably total morphism from
the chosen polynomial object, constructed from its Sigma-one relation. -/
def encodePolynomial (X Y : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) :
    GraphMorphism T (a.eval.obj (X, Y)) (rawCarrier X Y a) where
  graph := let R := baseRepresentation T X Y a; .mkSigma “z u. !R.val u z”
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z u h
    have h' : (baseRepresentation T X Y a).val.Evalb ![u, z] := by simpa using h
    exact (baseRepresentation_support T M X Y a u z h').symm
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    obtain ⟨u, hu⟩ := baseRepresentation_cover T M X Y a ⟨z, hz⟩
    refine ⟨u, by simpa using hu, ?_⟩
    intro v hv
    have hv' : (baseRepresentation T X Y a).val.Evalb ![v, z] := by simpa using hv
    exact baseRepresentation_code_unique T M X Y a v u z hv' hu

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
