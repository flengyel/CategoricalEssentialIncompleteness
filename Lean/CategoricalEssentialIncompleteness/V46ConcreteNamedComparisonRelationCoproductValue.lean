/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationPoints

/-! # Finite constructor dispatch through actual slice coproducts -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P : PredicateCategory T) (X : Over P × Over P) (rT rF : TernaryGraph)

theorem relation_coprod_value (a b : SyntaxPolynomial (PredicateCategory T)) {Z : Over P}
    (f : (a.withParameters P).eval.obj X ⟶ Z) (g : (b.withParameters P).eval.obj X ⟶ Z)
    (value : Obj T M Z.left → M) (φ : M → M) (p : M)
    (hf : ∀ (u : M) (x : Obj T M ((a.withParameters P).eval.obj X).left),
      (representation T P X rT rF a).val.Evalb ![p,u,x.val] →
        value ((F T M).map f.left x) = φ (Arithmetic.pair u 0))
    (hg : ∀ (u : M) (y : Obj T M ((b.withParameters P).eval.obj X).left),
      (representation T P X rT rF b).val.Evalb ![p,u,y.val] →
        value ((F T M).map g.left y) = φ (Arithmetic.pair u 1))
    (u : M) (z : Obj T M (((a.sum b).withParameters P).eval.obj X).left)
    (hz : (representation T P X rT rF (.sum a b)).val.Evalb ![p,u,z.val]) :
    value ((F T M).map (coprod.desc f g).left z) = φ u := by
  rcases relation_sum_points T M P X rT rF a b p u z hz with
    ⟨v,x,hu,hx,hi⟩ | ⟨w,y,hu,hy,hi⟩
  · have he : (F T M).map (coprod.desc f g).left z = (F T M).map f.left x := by
      erw [← hi,← Functor.map_comp_apply,← Over.comp_left,coprod.inl_desc]
    rw [he,hu]
    exact hf v x hx
  · have he : (F T M).map (coprod.desc f g).left z = (F T M).map g.left y := by
      erw [← hi,← Functor.map_comp_apply,← Over.comp_left,coprod.inr_desc]
    rw [he,hu]
    exact hg w y hy

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
