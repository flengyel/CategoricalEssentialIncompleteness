/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPolynomial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoordinates
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter

/-! # Forward polynomial charts for maps that depend on a fixed parameter -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem constantLeaf_model (P C : PredicateCategory T) (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ C)) :
    (constantLeaf T P C).val.Evalb ![p.val,u,z.val] ↔
      (F T M).map (prod.fst : P ⨯ C ⟶ P) z = p ∧
        ((F T M).map (prod.snd : P ⨯ C ⟶ C) z).val = u := by
  constructor
  · intro h
    have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z.val,p.val] ∧
        (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z.val,u] := by
      simpa [constantLeaf] using h
    exact ⟨(chosenGraph_map_iff T M prod.fst z p).mp hh.1,
      constantLeaf_value T M P C p.val u z h⟩
  · rintro ⟨hp,hu⟩
    have hs := (chosenGraph_map_iff T M (prod.snd : P ⨯ C ⟶ C) z
      ((F T M).map (prod.snd : P ⨯ C ⟶ C) z)).mpr rfl
    have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z.val,p.val] ∧
        (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z.val,u] :=
      ⟨(chosenGraph_map_iff T M prod.fst z p).mpr hp,by simpa only [hu] using hs⟩
    simpa [constantLeaf] using hh

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {P X Y C D : PredicateCategory T}

/-- The parameter need not be encoded as a numerical pair. The two leaf-value hypotheses
concern the fixed fiber, and the conclusion uses the slice-polynomial map. This finite
AST theorem assumes no fold or initiality equation. -/
theorem constantRepresentation_map (f : constantFamily P X ⟶ constantFamily P C)
    (g : constantFamily P Y ⟶ constantFamily P D) (p : Obj T M P) (φ ψ : M → M)
    (hf : ∀ z : Obj T M (P ⨯ X), (F T M).map (prod.fst : P ⨯ X ⟶ P) z = p →
      ((F T M).map (prod.snd : P ⨯ C ⟶ C) ((F T M).map f.left z)).val =
        φ ((F T M).map (prod.snd : P ⨯ X ⟶ X) z).val)
    (hg : ∀ z : Obj T M (P ⨯ Y), (F T M).map (prod.fst : P ⨯ Y ⟶ P) z = p →
      ((F T M).map (prod.snd : P ⨯ D ⟶ D) ((F T M).map g.left z)).val =
        ψ ((F T M).map (prod.snd : P ⨯ Y ⟶ Y) z).val)
    (q : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((q.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left)
    (hz : (constantRepresentation T P X Y q).val.Evalb ![p.val,u,z.val]) :
    (constantRepresentation T P C D q).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren φ ψ q u,
        ((F T M).map ((q.withParameters P).eval.map ((f,g) :
          (constantFamily P X,constantFamily P Y) ⟶ (constantFamily P C,constantFamily P D))).left z).val] := by
  induction q generalizing u with
  | term =>
      have hs := (constantLeaf_model T M P X p u z).mp hz
      apply (constantLeaf_model T M P C p (φ u) ((F T M).map f.left z)).mpr
      exact ⟨(over_value T M f z).trans hs.1,(hf z hs.1).trans (congrArg φ hs.2)⟩
  | formula =>
      have hs := (constantLeaf_model T M P Y p u z).mp hz
      apply (constantLeaf_model T M P D p (ψ u) ((F T M).map g.left z)).mpr
      exact ⟨(over_value T M g z).trans hs.1,(hg z hs.1).trans (congrArg ψ hs.2)⟩
  | coefficient E =>
      change (constantRepresentation T P C D (.coefficient E)).val.Evalb
        ![p.val,u,((F T M).map (𝟙 (P ⨯ E)) z).val]
      rw [(F T M).map_id]
      exact hz
  | unit =>
      have hs := (representation_unit_eval T M P (constantFamily P X,constantFamily P Y)
        (constantLeaf T P X) (constantLeaf T P Y) p.val u z.val).mp hz
      change (constantRepresentation T P C D .unit).val.Evalb
        ![p.val,0,((F T M).map (𝟙 (⊤_ (Over P)).left) z).val]
      rw [(F T M).map_id]
      exact (representation_unit_eval T M P (constantFamily P C,constantFamily P D)
        (constantLeaf T P C) (constantLeaf T P D) p.val 0 z.val).mpr ⟨hs.1,rfl⟩
  | product a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)
      let S₂ := (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)
      let T₁ := (a.withParameters P).eval.obj (constantFamily P C,constantFamily P D)
      let T₂ := (b.withParameters P).eval.obj (constantFamily P C,constantFamily P D)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f,g) :
        (constantFamily P X,constantFamily P Y) ⟶ (constantFamily P C,constantFamily P D))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f,g) :
        (constantFamily P X,constantFamily P Y) ⟶ (constantFamily P C,constantFamily P D))
      obtain ⟨x,y,r,s,he,hr,hs,hzr,hzs⟩ :=
        (representation_product_eval T M P (constantFamily P X,constantFamily P Y)
          (constantLeaf T P X) (constantLeaf T P Y) a b p.val u z.val).mp hz
      let rr : Obj T M S₁.left := ⟨r,((chosenGraph T (prod.fst : S₁ ⨯ S₂ ⟶ S₁).left).support_model M z.val r hzr).2⟩
      let ss : Obj T M S₂.left := ⟨s,((chosenGraph T (prod.snd : S₁ ⨯ S₂ ⟶ S₂).left).support_model M z.val s hzs).2⟩
      let out := (F T M).map (prod.map fa fb).left z
      let out₁ := (F T M).map fa.left rr
      let out₂ := (F T M).map fb.left ss
      have h₁ : (F T M).map (prod.fst : T₁ ⨯ T₂ ⟶ T₁).left out = out₁ :=
        (modelOverProduct_map_fst T M fa fb z).trans (congrArg ((F T M).map fa.left)
          ((chosenGraph_map_iff T M (prod.fst : S₁ ⨯ S₂ ⟶ S₁).left z rr).mp hzr))
      have h₂ : (F T M).map (prod.snd : T₁ ⨯ T₂ ⟶ T₂).left out = out₂ :=
        (modelOverProduct_map_snd T M fa fb z).trans (congrArg ((F T M).map fb.left)
          ((chosenGraph_map_iff T M (prod.snd : S₁ ⨯ S₂ ⟶ S₂).left z ss).mp hzs))
      have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.product a b) u =
          Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ a x)
            (ConcreteNamedSubstitution.mapChildren φ ψ b y) := by
        simp [he,ConcreteNamedSubstitution.mapChildren]
      rw [hm]
      exact (representation_product_eval T M P (constantFamily P C,constantFamily P D)
        (constantLeaf T P C) (constantLeaf T P D) a b p.val _ out.val).mpr
        ⟨_,_,out₁.val,out₂.val,rfl,ia x rr hr,ib y ss hs,
          (chosenGraph_map_iff T M (prod.fst : T₁ ⨯ T₂ ⟶ T₁).left out out₁).mpr h₁,
          (chosenGraph_map_iff T M (prod.snd : T₁ ⨯ T₂ ⟶ T₂).left out out₂).mpr h₂⟩
  | sum a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)
      let S₂ := (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)
      let T₁ := (a.withParameters P).eval.obj (constantFamily P C,constantFamily P D)
      let T₂ := (b.withParameters P).eval.obj (constantFamily P C,constantFamily P D)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f,g) :
        (constantFamily P X,constantFamily P Y) ⟶ (constantFamily P C,constantFamily P D))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f,g) :
        (constantFamily P X,constantFamily P Y) ⟶ (constantFamily P C,constantFamily P D))
      let out := (F T M).map (coprod.map fa fb).left z
      rcases (representation_sum_eval T M P (constantFamily P X,constantFamily P Y)
        (constantLeaf T P X) (constantLeaf T P Y) a b p.val u z.val).mp hz with
        ⟨x,r,he,hr,hi⟩ | ⟨y,s,he,hs,hi⟩
      · let rr : Obj T M S₁.left := ⟨r,((chosenGraph T
          (coprod.inl : S₁ ⟶ S₁ ⨿ S₂).left).support_model M r z.val hi).1⟩
        let out₁ := (F T M).map fa.left rr
        have h₁ : (F T M).map (coprod.inl : T₁ ⟶ T₁ ⨿ T₂).left out₁ = out :=
          (modelOverSum_map_inl T M fa fb rr).symm.trans
            (congrArg ((F T M).map (coprod.map fa fb).left)
              ((chosenGraph_map_iff T M (coprod.inl : S₁ ⟶ S₁ ⨿ S₂).left rr z).mp hi))
        have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.sum a b) u =
            Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ a x) 0 := by
          simp [he,ConcreteNamedSubstitution.mapChildren]
        rw [hm]
        exact (representation_sum_eval T M P (constantFamily P C,constantFamily P D)
          (constantLeaf T P C) (constantLeaf T P D) a b p.val _ out.val).mpr
          (Or.inl ⟨_,out₁.val,rfl,ia x rr hr,
            (chosenGraph_map_iff T M (coprod.inl : T₁ ⟶ T₁ ⨿ T₂).left out₁ out).mpr h₁⟩)
      · let ss : Obj T M S₂.left := ⟨s,((chosenGraph T
          (coprod.inr : S₂ ⟶ S₁ ⨿ S₂).left).support_model M s z.val hi).1⟩
        let out₂ := (F T M).map fb.left ss
        have h₂ : (F T M).map (coprod.inr : T₂ ⟶ T₁ ⨿ T₂).left out₂ = out :=
          (modelOverSum_map_inr T M fa fb ss).symm.trans
            (congrArg ((F T M).map (coprod.map fa fb).left)
              ((chosenGraph_map_iff T M (coprod.inr : S₂ ⟶ S₁ ⨿ S₂).left ss z).mp hi))
        have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.sum a b) u =
            Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ b y) 1 := by
          simp [he,ConcreteNamedSubstitution.mapChildren]
        rw [hm]
        exact (representation_sum_eval T M P (constantFamily P C,constantFamily P D)
          (constantLeaf T P C) (constantLeaf T P D) a b p.val _ out.val).mpr
          (Or.inr ⟨_,out₂.val,rfl,ib y ss hs,
            (chosenGraph_map_iff T M (coprod.inr : T₂ ⟶ T₁ ⨿ T₂).left out₂ out).mpr h₂⟩)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
