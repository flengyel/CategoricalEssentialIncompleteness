/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoordinates
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation

/-! # The canonical parameter comparison preserves the raw syntax coordinates -/

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

/-- The value projection of the canonical constant-product comparison
is the pair of the two child value projections. -/
theorem constantProduct_value {P U W : PredicateCategory T} {X Y : Over P}
    (f : X ⟶ constantFamily P U) (g : Y ⟶ constantFamily P W) :
    (prod.map f g ≫ constantProductComparison P U W).left ≫ prod.snd =
      prod.lift ((prod.fst : X ⨯ Y ⟶ X).left ≫ f.left ≫ prod.snd)
        ((prod.snd : X ⨯ Y ⟶ Y).left ≫ g.left ≫ prod.snd) := by
  have hf := congrArg (fun h => h.left ≫ prod.snd) (prod.map_fst f g)
  have hg := congrArg (fun h => h.left ≫ prod.snd) (prod.map_snd f g)
  simp only [Over.comp_left, Category.assoc] at hf hg
  simp only [Over.comp_left, constantProductComparison, Over.homMk_left,
    prod.lift_snd, prod.comp_lift]
  exact congrArg₂ prod.lift hf hg

/-- The base polynomial value of a point of its parameterized polynomial.
Only the value projection is erased; the actual parameterized source and
its chosen product/coproduct objects are retained. -/
def parameterValueMap (P : PredicateCategory T) (X Y : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) :
    ((a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)).left ⟶
      a.eval.obj (X, Y) :=
  (SyntaxPolynomial.parameterComparison P (X, Y) a).left ≫ prod.snd

@[simp] theorem parameterValueMap_term (P X Y : PredicateCategory T) :
    parameterValueMap T P X Y .term = (prod.snd : P ⨯ X ⟶ X) := by
  simp only [parameterValueMap, SyntaxPolynomial.parameterComparison,
    Over.id_left, Category.id_comp]
  rfl

@[simp] theorem parameterValueMap_formula (P X Y : PredicateCategory T) :
    parameterValueMap T P X Y .formula = (prod.snd : P ⨯ Y ⟶ Y) := by
  simp only [parameterValueMap, SyntaxPolynomial.parameterComparison,
    Over.id_left, Category.id_comp]
  rfl

@[simp] theorem parameterValueMap_coefficient (P X Y C : PredicateCategory T) :
    parameterValueMap T P X Y (.coefficient C) = (prod.snd : P ⨯ C ⟶ C) := by
  simp only [parameterValueMap, SyntaxPolynomial.parameterComparison,
    Over.id_left, Category.id_comp]
  rfl

theorem parameterValueMap_product_fst (P X Y : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) :
    parameterValueMap T P X Y (.product a b) ≫ prod.fst =
      (prod.fst : (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⨯
        (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⟶
          (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)).left ≫
            parameterValueMap T P X Y a := by
  unfold parameterValueMap
  change ((prod.map _ _ ≫ constantProductComparison P _ _).left ≫ prod.snd) ≫
    prod.fst = _
  rw [constantProduct_value, prod.lift_fst]

theorem parameterValueMap_product_snd (P X Y : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) :
    parameterValueMap T P X Y (.product a b) ≫ prod.snd =
      (prod.snd : (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⨯
        (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⟶
          (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)).left ≫
            parameterValueMap T P X Y b := by
  unfold parameterValueMap
  change ((prod.map _ _ ≫ constantProductComparison P _ _).left ≫ prod.snd) ≫
    prod.snd = _
  rw [constantProduct_value, prod.lift_snd]

theorem parameterValueMap_sum_inl (P X Y : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) :
    (coprod.inl : (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⟶
      (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⨿
        (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)).left ≫
          parameterValueMap T P X Y (.sum a b) =
            parameterValueMap T P X Y a ≫ coprod.inl := by
  have hh : coprod.inl ≫ SyntaxPolynomial.parameterComparison P (X, Y) (.sum a b) =
      SyntaxPolynomial.parameterComparison P (X, Y) a ≫
        (constantFamilyFunctor P).map coprod.inl := by
    simp [SyntaxPolynomial.parameterComparison, constantCoproductComparison]
  have hv := congrArg (fun h => h.left ≫
    (prod.snd : P ⨯ (SyntaxPolynomial.sum a b).eval.obj (X, Y) ⟶ (SyntaxPolynomial.sum a b).eval.obj (X, Y))) hh
  simp only [Over.comp_left, Category.assoc, constantFamilyFunctor, Over.homMk_left,
    prod.map_snd] at hv
  simpa only [parameterValueMap, Category.assoc] using hv

theorem parameterValueMap_sum_inr (P X Y : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) :
    (coprod.inr : (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⟶
      (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y) ⨿
        (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)).left ≫
          parameterValueMap T P X Y (.sum a b) =
            parameterValueMap T P X Y b ≫ coprod.inr := by
  have hh : coprod.inr ≫ SyntaxPolynomial.parameterComparison P (X, Y) (.sum a b) =
      SyntaxPolynomial.parameterComparison P (X, Y) b ≫
        (constantFamilyFunctor P).map coprod.inr := by
    simp [SyntaxPolynomial.parameterComparison, constantCoproductComparison]
  have hv := congrArg (fun h => h.left ≫
    (prod.snd : P ⨯ (SyntaxPolynomial.sum a b).eval.obj (X, Y) ⟶ (SyntaxPolynomial.sum a b).eval.obj (X, Y))) hh
  simp only [Over.comp_left, Category.assoc, constantFamilyFunctor, Over.homMk_left,
    prod.map_snd] at hv
  simpa only [parameterValueMap, Category.assoc] using hv


section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Every valid raw input has an actual point of the parameterized
polynomial. This supplies the domain point when extracting a guarded
constructor equation from an actual categorical algebra-hom equation. -/
theorem constantRepresentation_exists (P C D : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (h : (rawCarrier C D a).val.Evalb ![u]) :
    ∃ z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left,
      (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map ((a.withParameters P).eval.obj
          (constantFamily P C, constantFamily P D)).hom z = p := by
  let t : 𝚺₁.Semisentence 2 := .mkSigma “p u. !P.val p ∧ !C.val u”
  let f : 𝚺₁.Semisentence 2 := .mkSigma “p u. !P.val p ∧ !D.val u”
  have ht : ∀ (p : Obj T M P) (u : M), t.val.Evalb ![p.val, u] →
      ∃ z : Obj T M (P ⨯ C), (constantLeaf T P C).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map (prod.fst : P ⨯ C ⟶ P) z = p := by
    intro p u hu
    have hh : P.val.Evalb ![p.val] ∧ C.val.Evalb ![u] := by simpa [t] using hu
    obtain ⟨z, hz, _⟩ := constantLeaf_existsUnique T M P C p ⟨u, hh.2⟩
    exact ⟨z, hz⟩
  have hf : ∀ (p : Obj T M P) (u : M), f.val.Evalb ![p.val, u] →
      ∃ z : Obj T M (P ⨯ D), (constantLeaf T P D).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map (prod.fst : P ⨯ D ⟶ P) z = p := by
    intro p u hu
    have hh : P.val.Evalb ![p.val] ∧ D.val.Evalb ![u] := by simpa [f] using hu
    obtain ⟨z, hz, _⟩ := constantLeaf_existsUnique T M P D p ⟨u, hh.2⟩
    exact ⟨z, hz⟩
  have hi : (fiberInput P t f a).val.Evalb ![p.val, u] :=
    (constantInput_eval T M P C D a p.val u).mpr ⟨p.property, h⟩
  exact representation_exists T M P (constantFamily P C, constantFamily P D)
    (constantLeaf T P C) (constantLeaf T P D) t f ht hf a p u hi

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem constantLeaf_value (P C : PredicateCategory T) (p u : M)
    (z : Obj T M (P ⨯ C)) (h : (constantLeaf T P C).val.Evalb ![p, u, z.val]) :
    ((F T M).map (prod.snd : P ⨯ C ⟶ C) z).val = u := by
  have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z.val, p] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z.val, u] := by
    simpa [constantLeaf] using h
  let y := (F T M).map (prod.snd : P ⨯ C ⟶ C) z
  exact graph_functional_model (chosenGraph T (prod.snd : P ⨯ C ⟶ C)) z.val y.val u
    ((chosenGraph_map_iff T M prod.snd z y).mpr rfl) hh.2

/-- The exact parameter-comparison arrow sends a raw constant-family
coordinate to the same base-polynomial coordinate. No inverse to the
constant coproduct comparison is assumed. -/
theorem parameterValueMap_representation (P X Y : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P X, constantFamily P Y)).left)
    (h : (constantRepresentation T P X Y a).val.Evalb ![p.val, u, z.val]) :
    (baseRepresentation T X Y a).val.Evalb
      ![u, ((F T M).map (parameterValueMap T P X Y a) z).val] := by
  induction a generalizing u with
  | term =>
      apply (baseRepresentation_term_eval T M X Y _ _).mpr
      refine ⟨((F T M).map (parameterValueMap T P X Y .term) z).property, ?_⟩
      erw [parameterValueMap_term T P X Y]
      exact constantLeaf_value T M P X p.val u z h
  | formula =>
      apply (baseRepresentation_formula_eval T M X Y _ _).mpr
      refine ⟨((F T M).map (parameterValueMap T P X Y .formula) z).property, ?_⟩
      erw [parameterValueMap_formula T P X Y]
      exact constantLeaf_value T M P Y p.val u z h
  | coefficient C =>
      apply (baseRepresentation_coefficient_eval T M X Y C _ _).mpr
      refine ⟨((F T M).map (parameterValueMap T P X Y (.coefficient C)) z).property, ?_⟩
      erw [parameterValueMap_coefficient T P X Y C]
      exact constantLeaf_value T M P C p.val u z h
  | unit =>
      have hh := (representation_unit_eval T M P
        (constantFamily P X, constantFamily P Y) (constantLeaf T P X)
          (constantLeaf T P Y) p.val u z.val).mp h
      exact (baseRepresentation_unit_eval T M X Y _ _).mpr
        ⟨((F T M).map (parameterValueMap T P X Y .unit) z).property, hh.2⟩
  | product a b ia ib =>
      let A := (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)
      let B := (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)
      obtain ⟨v, w, x, y, he, hx, hy, hzx, hzy⟩ :=
        (representation_product_eval T M P (constantFamily P X, constantFamily P Y)
          (constantLeaf T P X) (constantLeaf T P Y) a b p.val u z.val).mp h
      let xx : Obj T M A.left :=
        ⟨x, ((chosenGraph T (prod.fst : A ⨯ B ⟶ A).left).support_model M z.val x hzx).2⟩
      let yy : Obj T M B.left :=
        ⟨y, ((chosenGraph T (prod.snd : A ⨯ B ⟶ B).left).support_model M z.val y hzy).2⟩
      let out := (F T M).map (parameterValueMap T P X Y (.product a b)) z
      let outA := (F T M).map (parameterValueMap T P X Y a) xx
      let outB := (F T M).map (parameterValueMap T P X Y b) yy
      have hf : (F T M).map (prod.fst : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
          a.eval.obj (X, Y)) out = outA := by
        have hh := congrArg (F T M).map (parameterValueMap_product_fst T P X Y a b)
        rw [Functor.map_comp, Functor.map_comp] at hh
        have hv := ConcreteCategory.congr_hom hh z
        change (F T M).map prod.fst out =
          (F T M).map (parameterValueMap T P X Y a)
            ((F T M).map (prod.fst : A ⨯ B ⟶ A).left z) at hv
        rw [(chosenGraph_map_iff T M (prod.fst : A ⨯ B ⟶ A).left z xx).mp hzx] at hv
        exact hv
      have hg : (F T M).map (prod.snd : a.eval.obj (X, Y) ⨯ b.eval.obj (X, Y) ⟶
          b.eval.obj (X, Y)) out = outB := by
        have hh := congrArg (F T M).map (parameterValueMap_product_snd T P X Y a b)
        rw [Functor.map_comp, Functor.map_comp] at hh
        have hv := ConcreteCategory.congr_hom hh z
        change (F T M).map prod.snd out =
          (F T M).map (parameterValueMap T P X Y b)
            ((F T M).map (prod.snd : A ⨯ B ⟶ B).left z) at hv
        rw [(chosenGraph_map_iff T M (prod.snd : A ⨯ B ⟶ B).left z yy).mp hzy] at hv
        exact hv
      exact (baseRepresentation_product_eval T M X Y a b u out.val).mpr
        ⟨v, w, outA.val, outB.val, he, ia v xx hx, ib w yy hy,
          (chosenGraph_map_iff T M prod.fst out outA).mpr hf,
          (chosenGraph_map_iff T M prod.snd out outB).mpr hg⟩
  | sum a b ia ib =>
      let A := (a.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)
      let B := (b.withParameters P).eval.obj (constantFamily P X, constantFamily P Y)
      let out := (F T M).map (parameterValueMap T P X Y (.sum a b)) z
      rcases (representation_sum_eval T M P (constantFamily P X, constantFamily P Y)
        (constantLeaf T P X) (constantLeaf T P Y) a b p.val u z.val).mp h with
          ⟨v, x, he, hx, hxz⟩ | ⟨w, y, he, hy, hyz⟩
      · let xx : Obj T M A.left :=
          ⟨x, ((chosenGraph T (coprod.inl : A ⟶ A ⨿ B).left).support_model M x z.val hxz).1⟩
        let outA := (F T M).map (parameterValueMap T P X Y a) xx
        have hf : (F T M).map (coprod.inl : a.eval.obj (X, Y) ⟶
            a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y)) outA = out := by
          have hh := congrArg (F T M).map (parameterValueMap_sum_inl T P X Y a b)
          rw [Functor.map_comp, Functor.map_comp] at hh
          have hv := ConcreteCategory.congr_hom hh xx
          change (F T M).map (parameterValueMap T P X Y (.sum a b))
            ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left xx) =
              (F T M).map coprod.inl outA at hv
          rw [(chosenGraph_map_iff T M (coprod.inl : A ⟶ A ⨿ B).left xx z).mp hxz] at hv
          exact hv.symm
        exact (baseRepresentation_sum_eval T M X Y a b u out.val).mpr
          (Or.inl ⟨v, outA.val, he, ia v xx hx,
            (chosenGraph_map_iff T M coprod.inl outA out).mpr hf⟩)
      · let yy : Obj T M B.left :=
          ⟨y, ((chosenGraph T (coprod.inr : B ⟶ A ⨿ B).left).support_model M y z.val hyz).1⟩
        let outB := (F T M).map (parameterValueMap T P X Y b) yy
        have hf : (F T M).map (coprod.inr : b.eval.obj (X, Y) ⟶
            a.eval.obj (X, Y) ⨿ b.eval.obj (X, Y)) outB = out := by
          have hh := congrArg (F T M).map (parameterValueMap_sum_inr T P X Y a b)
          rw [Functor.map_comp, Functor.map_comp] at hh
          have hv := ConcreteCategory.congr_hom hh yy
          change (F T M).map (parameterValueMap T P X Y (.sum a b))
            ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left yy) =
              (F T M).map coprod.inr outB at hv
          rw [(chosenGraph_map_iff T M (coprod.inr : B ⟶ A ⨿ B).left yy z).mp hyz] at hv
          exact hv.symm
        exact (baseRepresentation_sum_eval T M X Y a b u out.val).mpr
          (Or.inr ⟨w, outB.val, he, ib w yy hy,
            (chosenGraph_map_iff T M coprod.inr outB out).mpr hf⟩)

end Models

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
