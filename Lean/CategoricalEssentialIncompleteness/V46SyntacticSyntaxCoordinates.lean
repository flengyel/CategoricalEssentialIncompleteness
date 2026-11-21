/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFibers

/-! # Coordinates cover every point of the syntax polynomial -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P : PredicateCategory T) (X : Over P × Over P) (rT rF : TernaryGraph)

/-- Covering the two leaf families covers every polynomial point. In particular this
quantifies over all model elements, without restricting the parameter or the
represented point to a standard numeral. -/
theorem representation_cover
    (ht : ∀ (p : Obj T M P) (z : Obj T M X.1.left),
      (F T M).map X.1.hom z = p → ∃ u : M, rT.val.Evalb ![p.val, u, z.val])
    (hf : ∀ (p : Obj T M P) (z : Obj T M X.2.left),
      (F T M).map X.2.hom z = p → ∃ u : M, rF.val.Evalb ![p.val, u, z.val])
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P)
    (z : Obj T M ((a.withParameters P).eval.obj X).left)
    (hzp : (F T M).map ((a.withParameters P).eval.obj X).hom z = p) :
    ∃ u : M, (representation T P X rT rF a).val.Evalb ![p.val, u, z.val] := by
  induction a with
  | term => exact ht p z hzp
  | formula => exact hf p z hzp
  | coefficient C =>
      let u := (F T M).map (prod.snd : P ⨯ C ⟶ C) z
      exact ⟨u.val, (representation_coefficient_eval T M P X rT rF C p.val u.val z.val).mpr
        ⟨(chosenGraph_map_iff T M prod.fst z p).mpr hzp,
          (chosenGraph_map_iff T M prod.snd z u).mpr rfl⟩⟩
  | unit =>
      exact ⟨0, (representation_unit_eval T M P X rT rF p.val 0 z.val).mpr
        ⟨(chosenGraph_map_iff T M (⊤_ (Over P)).hom z p).mpr hzp, rfl⟩⟩
  | product a b ia ib =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      let x := (F T M).map (prod.fst : A ⨯ B ⟶ A).left z
      let y := (F T M).map (prod.snd : A ⨯ B ⟶ B).left z
      have hxp : (F T M).map A.hom x = p :=
        (over_value T M (prod.fst : A ⨯ B ⟶ A) z).trans hzp
      have hyp : (F T M).map B.hom y = p :=
        (over_value T M (prod.snd : A ⨯ B ⟶ B) z).trans hzp
      obtain ⟨v, hv⟩ := ia x hxp
      obtain ⟨w, hw⟩ := ib y hyp
      exact ⟨Arithmetic.pair v w,
        (representation_product_eval T M P X rT rF a b p.val _ z.val).mpr
          ⟨v, w, x.val, y.val, rfl, hv, hw,
            (chosenGraph_map_iff T M (prod.fst : A ⨯ B ⟶ A).left z x).mpr rfl,
            (chosenGraph_map_iff T M (prod.snd : A ⨯ B ⟶ B).left z y).mpr rfl⟩⟩
  | sum a b ia ib =>
      let A := (a.withParameters P).eval.obj X
      let B := (b.withParameters P).eval.obj X
      rcases modelOverSum_cases T M A B z with ⟨x, hxz⟩ | ⟨y, hyz⟩
      · have hxp : (F T M).map A.hom x = p := by
          have h := over_value T M (coprod.inl : A ⟶ A ⨿ B) x
          rw [hxz] at h
          exact h.symm.trans hzp
        obtain ⟨v, hv⟩ := ia x hxp
        exact ⟨Arithmetic.pair v 0,
          (representation_sum_eval T M P X rT rF a b p.val _ z.val).mpr
            (Or.inl ⟨v, x.val, rfl, hv,
              (chosenGraph_map_iff T M (coprod.inl : A ⟶ A ⨿ B).left x z).mpr hxz⟩)⟩
      · have hyp : (F T M).map B.hom y = p := by
          have h := over_value T M (coprod.inr : B ⟶ A ⨿ B) y
          rw [hyz] at h
          exact h.symm.trans hzp
        obtain ⟨w, hw⟩ := ib y hyp
        exact ⟨Arithmetic.pair w 1,
          (representation_sum_eval T M P X rT rF a b p.val _ z.val).mpr
            (Or.inr ⟨w, y.val, rfl, hw,
              (chosenGraph_map_iff T M (coprod.inr : B ⟶ A ⨿ B).left y z).mpr hyz⟩)⟩

/-- Covering specializes both to full-value coordinates in arbitrary
families and to child-word coordinates in the constant source families. -/
theorem fiberRepresentation_cover (a : SyntaxPolynomial (PredicateCategory T))
    (p : Obj T M P) (z : Obj T M ((a.withParameters P).eval.obj X).left)
    (hzp : (F T M).map ((a.withParameters P).eval.obj X).hom z = p) :
    ∃ u : M, (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val] := by
  apply representation_cover T M P X (fiberLeaf T P X.1) (fiberLeaf T P X.2)
    (a := a) (p := p) (z := z) _ _ hzp
  · intro p z hp
    exact ⟨z.val, (fiberLeaf_model T M P X.1 p z z).mpr ⟨rfl, hp⟩⟩
  · intro p z hp
    exact ⟨z.val, (fiberLeaf_model T M P X.2 p z z).mpr ⟨rfl, hp⟩⟩

theorem constantRepresentation_cover (C D : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left)
    (hzp : (F T M).map ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).hom z = p) :
    ∃ u : M, (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val] := by
  apply representation_cover T M P (constantFamily P C, constantFamily P D)
    (constantLeaf T P C) (constantLeaf T P D) (a := a) (p := p) (z := z) _ _ hzp
  · intro p z hp
    let c := (F T M).map (prod.snd : P ⨯ C ⟶ C) z
    exact ⟨c.val, (constantLeaf_model T M P C p c z).mpr ⟨hp, rfl⟩⟩
  · intro p z hp
    let d := (F T M).map (prod.snd : P ⨯ D ⟶ D) z
    exact ⟨d.val, (constantLeaf_model T M P D p d z).mpr ⟨hp, rfl⟩⟩

/-- The parameter coordinate is retained while constant-family leaf
coordinates erase only the first product projection. -/
def constantInput (P C D : Carrier) : RawPolynomial → 𝚺₁.Semisentence 2 :=
  fiberInput P (.mkSigma “p u. !P.val p ∧ !C.val u”)
    (.mkSigma “p u. !P.val p ∧ !D.val u”)


omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem constantInput_eval (C D : PredicateCategory T)
    (a : RawPolynomial) (p u : M) :
    (constantInput P C D a).val.Evalb ![p, u] ↔
      P.val.Evalb ![p] ∧ (rawCarrier C D a).val.Evalb ![u] := by
  induction a generalizing u with
  | term => simp [constantInput, fiberInput, rawCarrier]
  | formula => simp [constantInput, fiberInput, rawCarrier]
  | coefficient E => simp [constantInput, fiberInput, rawCarrier]
  | unit => simp [constantInput, fiberInput, rawCarrier]
  | product a b ia ib =>
      change (fiberInput P _ _ (.product a b)).val.Evalb ![p, u] ↔ _
      rw [fiberInput_product_eval, rawCarrier_product_eval]
      constructor
      · rintro ⟨v, w, he, hv, hw⟩
        exact ⟨(ia v).mp hv |>.1,
          v, w, he, (ia v).mp hv |>.2, (ib w).mp hw |>.2⟩
      · rintro ⟨hp, v, w, he, hv, hw⟩
        exact ⟨v, w, he, (ia v).mpr ⟨hp, hv⟩, (ib w).mpr ⟨hp, hw⟩⟩
  | sum a b ia ib =>
      change (fiberInput P _ _ (.sum a b)).val.Evalb ![p, u] ↔ _
      rw [fiberInput_sum_eval, rawCarrier_sum_eval]
      constructor
      · rintro (⟨v, he, hv⟩ | ⟨w, he, hw⟩)
        · exact ⟨(ia v).mp hv |>.1, Or.inl ⟨v, he, (ia v).mp hv |>.2⟩⟩
        · exact ⟨(ib w).mp hw |>.1, Or.inr ⟨w, he, (ib w).mp hw |>.2⟩⟩
      · rintro ⟨hp, (⟨v, he, hv⟩ | ⟨w, he, hw⟩)⟩
        · exact Or.inl ⟨v, he, (ia v).mpr ⟨hp, hv⟩⟩
        · exact Or.inr ⟨w, he, (ib w).mpr ⟨hp, hw⟩⟩

theorem constantRepresentation_support (C D : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (p u z : M)
    (h : (constantRepresentation T P C D a).val.Evalb ![p, u, z]) :
    P.val.Evalb ![p] ∧ (rawCarrier C D a).val.Evalb ![u] ∧
      ((a.withParameters P).eval.obj (constantFamily P C, constantFamily P D)).left.val.Evalb
        ![z] ∧ (chosenGraph T ((a.withParameters P).eval.obj
          (constantFamily P C, constantFamily P D)).hom).graph.val.Evalb ![z, p] := by
  let t : 𝚺₁.Semisentence 2 := .mkSigma “p u. !P.val p ∧ !C.val u”
  let f : 𝚺₁.Semisentence 2 := .mkSigma “p u. !P.val p ∧ !D.val u”
  have ht : ∀ p u z : M, (constantLeaf T P C).val.Evalb ![p, u, z] →
      t.val.Evalb ![p, u] ∧ (P ⨯ C).val.Evalb ![z] ∧
        (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] := by
    intro p u z h
    have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] ∧
        (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z, u] := by
      simpa [constantLeaf] using h
    have hs₁ := (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).support_model M z p hh.1
    have hs₂ := (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).support_model M z u hh.2
    exact ⟨by simpa [t] using And.intro hs₁.2 hs₂.2, hs₁.1, hh.1⟩
  have hf : ∀ p u z : M, (constantLeaf T P D).val.Evalb ![p, u, z] →
      f.val.Evalb ![p, u] ∧ (P ⨯ D).val.Evalb ![z] ∧
        (chosenGraph T (prod.fst : P ⨯ D ⟶ P)).graph.val.Evalb ![z, p] := by
    intro p u z h
    have hh : (chosenGraph T (prod.fst : P ⨯ D ⟶ P)).graph.val.Evalb ![z, p] ∧
        (chosenGraph T (prod.snd : P ⨯ D ⟶ D)).graph.val.Evalb ![z, u] := by
      simpa [constantLeaf] using h
    have hs₁ := (chosenGraph T (prod.fst : P ⨯ D ⟶ P)).support_model M z p hh.1
    have hs₂ := (chosenGraph T (prod.snd : P ⨯ D ⟶ D)).support_model M z u hh.2
    exact ⟨by simpa [f] using And.intro hs₁.2 hs₂.2, hs₁.1, hh.1⟩
  obtain ⟨hi, hz, hp⟩ := representation_support T M P
    (constantFamily P C, constantFamily P D) (constantLeaf T P C) (constantLeaf T P D)
    t f ht hf a p u z h
  obtain ⟨hp', hu⟩ := (constantInput_eval T M P C D a p u).mp hi
  exact ⟨hp', hu, hz, hp⟩

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
