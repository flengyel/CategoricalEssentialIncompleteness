/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationMap

/-! # Reading actual product and coproduct points from forward leaf relations -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P : PredicateCategory T) (X : Over P × Over P) (rT rF : TernaryGraph)

theorem relation_product_points (a b : SyntaxPolynomial (PredicateCategory T)) (p u : M)
    (z : Obj T M (((a.product b).withParameters P).eval.obj X).left)
    (hz : (representation T P X rT rF (.product a b)).val.Evalb ![p,u,z.val]) :
    ∃ v w : M, u = Arithmetic.pair v w ∧
      (representation T P X rT rF a).val.Evalb
        ![p,v,((F T M).map (prod.fst : (a.withParameters P).eval.obj X ⨯
          (b.withParameters P).eval.obj X ⟶ _).left z).val] ∧
      (representation T P X rT rF b).val.Evalb
        ![p,w,((F T M).map (prod.snd : (a.withParameters P).eval.obj X ⨯
          (b.withParameters P).eval.obj X ⟶ _).left z).val] := by
  obtain ⟨v,w,x,y,he,hx,hy,hf,hg⟩ := (representation_product_eval T M P X rT rF a b p u z.val).mp hz
  let xx : Obj T M ((a.withParameters P).eval.obj X).left :=
    ⟨x,((chosenGraph T (prod.fst : (a.withParameters P).eval.obj X ⨯
      (b.withParameters P).eval.obj X ⟶ _).left).support_model M z.val x hf).2⟩
  let yy : Obj T M ((b.withParameters P).eval.obj X).left :=
    ⟨y,((chosenGraph T (prod.snd : (a.withParameters P).eval.obj X ⨯
      (b.withParameters P).eval.obj X ⟶ _).left).support_model M z.val y hg).2⟩
  have h₁ := (chosenGraph_map_iff T M (prod.fst : (a.withParameters P).eval.obj X ⨯
    (b.withParameters P).eval.obj X ⟶ _).left z xx).mp hf
  have h₂ := (chosenGraph_map_iff T M (prod.snd : (a.withParameters P).eval.obj X ⨯
    (b.withParameters P).eval.obj X ⟶ _).left z yy).mp hg
  exact ⟨v,w,he,by simpa only [h₁] using hx,by simpa only [h₂] using hy⟩

theorem relation_sum_points (a b : SyntaxPolynomial (PredicateCategory T)) (p u : M)
    (z : Obj T M (((a.sum b).withParameters P).eval.obj X).left)
    (hz : (representation T P X rT rF (.sum a b)).val.Evalb ![p,u,z.val]) :
    (∃ v : M, ∃ x : Obj T M ((a.withParameters P).eval.obj X).left,
      u = Arithmetic.pair v 0 ∧ (representation T P X rT rF a).val.Evalb ![p,v,x.val] ∧
      (F T M).map (coprod.inl : (a.withParameters P).eval.obj X ⟶
        (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left x = z) ∨
    (∃ w : M, ∃ y : Obj T M ((b.withParameters P).eval.obj X).left,
      u = Arithmetic.pair w 1 ∧ (representation T P X rT rF b).val.Evalb ![p,w,y.val] ∧
      (F T M).map (coprod.inr : (b.withParameters P).eval.obj X ⟶
        (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left y = z) := by
  rcases (representation_sum_eval T M P X rT rF a b p u z.val).mp hz with
    ⟨v,x,he,hx,hf⟩ | ⟨w,y,he,hy,hg⟩
  · let xx : Obj T M ((a.withParameters P).eval.obj X).left :=
      ⟨x,((chosenGraph T (coprod.inl : (a.withParameters P).eval.obj X ⟶
        (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).support_model M x z.val hf).1⟩
    exact Or.inl ⟨v,xx,he,hx,(chosenGraph_map_iff T M _ xx z).mp hf⟩
  · let yy : Obj T M ((b.withParameters P).eval.obj X).left :=
      ⟨y,((chosenGraph T (coprod.inr : (b.withParameters P).eval.obj X ⟶
        (a.withParameters P).eval.obj X ⨿ (b.withParameters P).eval.obj X).left).support_model M y z.val hg).1⟩
    exact Or.inr ⟨w,yy,he,hy,(chosenGraph_map_iff T M _ yy z).mp hg⟩

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
