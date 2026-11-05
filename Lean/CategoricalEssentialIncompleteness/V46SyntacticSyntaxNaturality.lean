/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawMap

/-! # Polynomial mapping agrees with the actual slice morphisms -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The preserved coproduct comparison commutes with actual slice maps. -/
theorem modelOverSum_map_inl {P : PredicateCategory T} {A B C D : Over P}
    (f : A ⟶ C) (g : B ⟶ D) (x : Obj T M A.left) :
    (F T M).map (coprod.map f g).left
      ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left x) =
        (F T M).map (coprod.inl : C ⟶ C ⨿ D).left ((F T M).map f.left x) := by
  have h : (coprod.inl : A ⟶ A ⨿ B).left ≫ (coprod.map f g).left =
      f.left ≫ (coprod.inl : C ⟶ C ⨿ D).left :=
    congrArg Over.Hom.left (coprod.inl_map f g)
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm x

theorem modelOverSum_map_inr {P : PredicateCategory T} {A B C D : Over P}
    (f : A ⟶ C) (g : B ⟶ D) (y : Obj T M B.left) :
    (F T M).map (coprod.map f g).left
      ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left y) =
        (F T M).map (coprod.inr : D ⟶ C ⨿ D).left ((F T M).map g.left y) := by
  have h : (coprod.inr : B ⟶ A ⨿ B).left ≫ (coprod.map f g).left =
      g.left ≫ (coprod.inr : D ⟶ C ⨿ D).left :=
    congrArg Over.Hom.left (coprod.inr_map f g)
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm y

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {P C D : PredicateCategory T} {A B : Over P}

/-- Applying the finite raw polynomial to actual candidate arrows gives
coordinates of the actual categorical polynomial map. This forward
comparison requires neither a fold equation nor a comparison inverse. -/
theorem representation_arrow_map (f : constantFamily P C ⟶ A)
    (g : constantFamily P D ⟶ B) (a : SyntaxPolynomial (PredicateCategory T))
    (p : Obj T M P) (u v : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left)
    (h : (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val])
    (hm : (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p.val, u, v]) :
    (fiberRepresentation T P (A, B) a).val.Evalb
      ![p.val, v, ((F T M).map ((a.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))).left z).val] := by
  induction a generalizing u v with
  | term => exact rawArrow_fiberLeaf T M f p u v z h hm
  | formula => exact rawArrow_fiberLeaf T M g p u v z h hm
  | coefficient E =>
      have hh : P.val.Evalb ![p.val] ∧ E.val.Evalb ![u] ∧ v = u := by
        simpa [mapRaw] using hm
      have hv : v = u := hh.2.2
      subst v
      change (fiberRepresentation T P (A, B) (.coefficient E)).val.Evalb
        ![p.val, u, ((F T M).map (𝟙 (P ⨯ E)) z).val]
      rw [(F T M).map_id]
      exact h
  | unit =>
      have hh : P.val.Evalb ![p.val] ∧ u = 0 ∧ v = 0 := by simpa [mapRaw] using hm
      have hv : v = u := hh.2.2.trans hh.2.1.symm
      subst v
      change (fiberRepresentation T P (A, B) .unit).val.Evalb
        ![p.val, u, ((F T M).map (𝟙 (⊤_ (Over P)).left) z).val]
      rw [(F T M).map_id]
      exact h
  | product a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (constantFamily P C, constantFamily P D)
      let S₂ := (b.withParameters P).eval.obj (constantFamily P C, constantFamily P D)
      let T₁ := (a.withParameters P).eval.obj (A, B)
      let T₂ := (b.withParameters P).eval.obj (A, B)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))
      obtain ⟨x, y, r, s, he, hr, hs, hzr, hzs⟩ :=
        (representation_product_eval T M P (constantFamily P C, constantFamily P D)
          (constantLeaf T P C) (constantLeaf T P D) a b p.val u z.val).mp h
      obtain ⟨x₀, y₀, x', y', he₀, hv, hx', hy'⟩ :=
        (mapRaw_product_eval P (rawArrow T f) (rawArrow T g) a b p.val u v).mp hm
      obtain ⟨hx, hy⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he₀)
      subst x₀
      subst y₀
      let rr : Obj T M S₁.left :=
        ⟨r, ((chosenGraph T (prod.fst : S₁ ⨯ S₂ ⟶ S₁).left).support_model
          M z.val r hzr).2⟩
      let ss : Obj T M S₂.left :=
        ⟨s, ((chosenGraph T (prod.snd : S₁ ⨯ S₂ ⟶ S₂).left).support_model
          M z.val s hzs).2⟩
      let out := (F T M).map (prod.map fa fb).left z
      let out₁ := (F T M).map fa.left rr
      let out₂ := (F T M).map fb.left ss
      have hf : (F T M).map (prod.fst : T₁ ⨯ T₂ ⟶ T₁).left out = out₁ :=
        (modelOverProduct_map_fst T M fa fb z).trans
          (congrArg ((F T M).map fa.left)
            ((chosenGraph_map_iff T M (prod.fst : S₁ ⨯ S₂ ⟶ S₁).left z rr).mp hzr))
      have hg : (F T M).map (prod.snd : T₁ ⨯ T₂ ⟶ T₂).left out = out₂ :=
        (modelOverProduct_map_snd T M fa fb z).trans
          (congrArg ((F T M).map fb.left)
            ((chosenGraph_map_iff T M (prod.snd : S₁ ⨯ S₂ ⟶ S₂).left z ss).mp hzs))
      exact (representation_product_eval T M P (A, B) (fiberLeaf T P A)
        (fiberLeaf T P B) a b p.val v out.val).mpr
          ⟨x', y', out₁.val, out₂.val, hv, ia x x' rr hr hx', ib y y' ss hs hy',
            (chosenGraph_map_iff T M (prod.fst : T₁ ⨯ T₂ ⟶ T₁).left out out₁).mpr hf,
            (chosenGraph_map_iff T M (prod.snd : T₁ ⨯ T₂ ⟶ T₂).left out out₂).mpr hg⟩
  | sum a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (constantFamily P C, constantFamily P D)
      let S₂ := (b.withParameters P).eval.obj (constantFamily P C, constantFamily P D)
      let T₁ := (a.withParameters P).eval.obj (A, B)
      let T₂ := (b.withParameters P).eval.obj (A, B)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))
      let out := (F T M).map (coprod.map fa fb).left z
      rcases (representation_sum_eval T M P (constantFamily P C, constantFamily P D)
        (constantLeaf T P C) (constantLeaf T P D) a b p.val u z.val).mp h with
          ⟨x, r, he, hr, hrz⟩ | ⟨y, s, he, hs, hsz⟩
      · rcases (mapRaw_sum_eval P (rawArrow T f) (rawArrow T g) a b p.val u v).mp hm with
          ⟨x₀, x', he₀, hv, hx'⟩ | ⟨y₀, y', he₀, _, _⟩
        · have hx := ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he₀)).1
          subst x₀
          let rr : Obj T M S₁.left :=
            ⟨r, ((chosenGraph T (coprod.inl : S₁ ⟶ S₁ ⨿ S₂).left).support_model
              M r z.val hrz).1⟩
          let out₁ := (F T M).map fa.left rr
          have hf : (F T M).map (coprod.inl : T₁ ⟶ T₁ ⨿ T₂).left out₁ = out :=
            (modelOverSum_map_inl T M fa fb rr).symm.trans
              (congrArg ((F T M).map (coprod.map fa fb).left)
                ((chosenGraph_map_iff T M
                  (coprod.inl : S₁ ⟶ S₁ ⨿ S₂).left rr z).mp hrz))
          exact (representation_sum_eval T M P (A, B) (fiberLeaf T P A)
            (fiberLeaf T P B) a b p.val v out.val).mpr
              (Or.inl ⟨x', out₁.val, hv, ia x x' rr hr hx',
                (chosenGraph_map_iff T M
                  (coprod.inl : T₁ ⟶ T₁ ⨿ T₂).left out₁ out).mpr hf⟩)
        · exact (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he₀)).2).elim
      · rcases (mapRaw_sum_eval P (rawArrow T f) (rawArrow T g) a b p.val u v).mp hm with
          ⟨x₀, x', he₀, _, _⟩ | ⟨y₀, y', he₀, hv, hy'⟩
        · exact (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp (he₀.symm.trans he)).2).elim
        · have hy := ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he₀)).1
          subst y₀
          let ss : Obj T M S₂.left :=
            ⟨s, ((chosenGraph T (coprod.inr : S₂ ⟶ S₁ ⨿ S₂).left).support_model
              M s z.val hsz).1⟩
          let out₂ := (F T M).map fb.left ss
          have hg : (F T M).map (coprod.inr : T₂ ⟶ T₁ ⨿ T₂).left out₂ = out :=
            (modelOverSum_map_inr T M fa fb ss).symm.trans
              (congrArg ((F T M).map (coprod.map fa fb).left)
                ((chosenGraph_map_iff T M
                  (coprod.inr : S₂ ⟶ S₁ ⨿ S₂).left ss z).mp hsz))
          exact (representation_sum_eval T M P (A, B) (fiberLeaf T P A)
            (fiberLeaf T P B) a b p.val v out.val).mpr
              (Or.inr ⟨y', out₂.val, hv, ib y y' ss hs hy',
                (chosenGraph_map_iff T M
                  (coprod.inr : T₂ ⟶ T₁ ⨿ T₂).left out₂ out).mpr hg⟩)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
