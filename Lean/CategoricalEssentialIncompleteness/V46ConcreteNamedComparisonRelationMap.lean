/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonConstantMap
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoordinates
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter

/-! # Forward polynomial charts with arbitrary target leaf relations -/

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

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
section GeneralRelationMap
variable {P : PredicateCategory T} {A B C D : Over P}

/-- Arbitrary positive source and target leaf coordinates extend through
all actual slice products and sums. Only the indicated forward leaf
relations are used, so neither relation is required to be invertible. -/
theorem representation_relation_map (f : A ⟶ C) (g : B ⟶ D)
    (rT rF sT sF : TernaryGraph) (p : Obj T M P) (φ ψ : M → M)
    (hf : ∀ (u : M) (z : Obj T M A.left), rT.val.Evalb ![p.val,u,z.val] →
      sT.val.Evalb ![p.val,φ u,((F T M).map f.left z).val])
    (hg : ∀ (u : M) (z : Obj T M B.left), rF.val.Evalb ![p.val,u,z.val] →
      sF.val.Evalb ![p.val,ψ u,((F T M).map g.left z).val])
    (q : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((q.withParameters P).eval.obj (A,B)).left)
    (hz : (representation T P (A,B) rT rF q).val.Evalb ![p.val,u,z.val]) :
    (representation T P (C,D) sT sF q).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren φ ψ q u,
        ((F T M).map ((q.withParameters P).eval.map ((f,g) : (A,B) ⟶ (C,D))).left z).val] := by
  induction q generalizing u with
  | term => exact hf u z hz
  | formula => exact hg u z hz
  | coefficient E =>
      change (representation T P (C,D) sT sF (.coefficient E)).val.Evalb
        ![p.val,u,((F T M).map (𝟙 (P ⨯ E)) z).val]
      rw [(F T M).map_id]
      exact hz
  | unit =>
      have hs := (representation_unit_eval T M P (A,B)
        rT rF p.val u z.val).mp hz
      change (representation T P (C,D) sT sF .unit).val.Evalb
        ![p.val,0,((F T M).map (𝟙 (⊤_ (Over P)).left) z).val]
      rw [(F T M).map_id]
      exact (representation_unit_eval T M P (C,D)
        sT sF p.val 0 z.val).mpr ⟨hs.1,rfl⟩
  | product a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (A,B)
      let S₂ := (b.withParameters P).eval.obj (A,B)
      let T₁ := (a.withParameters P).eval.obj (C,D)
      let T₂ := (b.withParameters P).eval.obj (C,D)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f,g) :
        (A,B) ⟶ (C,D))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f,g) :
        (A,B) ⟶ (C,D))
      obtain ⟨x,y,r,s,he,hr,hs,hzr,hzs⟩ :=
        (representation_product_eval T M P (A,B)
          rT rF a b p.val u z.val).mp hz
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
      exact (representation_product_eval T M P (C,D)
        sT sF a b p.val _ out.val).mpr
        ⟨_,_,out₁.val,out₂.val,rfl,ia x rr hr,ib y ss hs,
          (chosenGraph_map_iff T M (prod.fst : T₁ ⨯ T₂ ⟶ T₁).left out out₁).mpr h₁,
          (chosenGraph_map_iff T M (prod.snd : T₁ ⨯ T₂ ⟶ T₂).left out out₂).mpr h₂⟩
  | sum a b ia ib =>
      let S₁ := (a.withParameters P).eval.obj (A,B)
      let S₂ := (b.withParameters P).eval.obj (A,B)
      let T₁ := (a.withParameters P).eval.obj (C,D)
      let T₂ := (b.withParameters P).eval.obj (C,D)
      let fa : S₁ ⟶ T₁ := (a.withParameters P).eval.map ((f,g) :
        (A,B) ⟶ (C,D))
      let fb : S₂ ⟶ T₂ := (b.withParameters P).eval.map ((f,g) :
        (A,B) ⟶ (C,D))
      let out := (F T M).map (coprod.map fa fb).left z
      rcases (representation_sum_eval T M P (A,B)
        rT rF a b p.val u z.val).mp hz with
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
        exact (representation_sum_eval T M P (C,D)
          sT sF a b p.val _ out.val).mpr
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
        exact (representation_sum_eval T M P (C,D)
          sT sF a b p.val _ out.val).mpr
          (Or.inr ⟨_,out₂.val,rfl,ib y ss hs,
            (chosenGraph_map_iff T M (coprod.inr : T₂ ⟶ T₁ ⨿ T₂).left out₂ out).mpr h₂⟩)

end GeneralRelationMap

variable {P X Y : PredicateCategory T} {A B : Over P}

/-- A fixed-fiber specialization with literal source-word coordinates. -/
theorem relationRepresentation_map (f : constantFamily P X ⟶ A)
    (g : constantFamily P Y ⟶ B) (rT rF : TernaryGraph) (p : Obj T M P) (φ ψ : M → M)
    (hf : ∀ z : Obj T M (P ⨯ X), (F T M).map (prod.fst : P ⨯ X ⟶ P) z = p →
      rT.val.Evalb ![p.val,φ ((F T M).map (prod.snd : P ⨯ X ⟶ X) z).val,
        ((F T M).map f.left z).val])
    (hg : ∀ z : Obj T M (P ⨯ Y), (F T M).map (prod.fst : P ⨯ Y ⟶ P) z = p →
      rF.val.Evalb ![p.val,ψ ((F T M).map (prod.snd : P ⨯ Y ⟶ Y) z).val,
        ((F T M).map g.left z).val])
    (q : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((q.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left)
    (hz : (constantRepresentation T P X Y q).val.Evalb ![p.val,u,z.val]) :
    (representation T P (A,B) rT rF q).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren φ ψ q u,
        ((F T M).map ((q.withParameters P).eval.map ((f,g) :
          (constantFamily P X,constantFamily P Y) ⟶ (A,B))).left z).val] := by
  apply representation_relation_map T M f g
    (constantLeaf T P X) (constantLeaf T P Y) rT rF p φ ψ ?_ ?_ q u z hz
  · intro v w hw
    have hs := (constantLeaf_model T M P X p v w).mp hw
    simpa only [hs.2] using hf w hs.1
  · intro v w hw
    have hs := (constantLeaf_model T M P Y p v w).mp hw
    simpa only [hs.2] using hg w hs.1

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
