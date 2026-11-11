/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPolynomial

/-! # Product and sum eliminators for the forward numerical chart -/

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
variable (X Y : PredicateCategory T)
local instance namedRepresentationModelDecidableEq : DecidableEq M := Classical.decEq M

/-- A chart for a chosen product point restricts to charts for its actual
categorical projections. This only eliminates a representation; no
inverse for the general polynomial encoder is used. -/
theorem representation_product_points (a b : SyntaxPolynomial (PredicateCategory T))
    (u : M) (z : Obj T M ((a.product b).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (.product a b)).val.Evalb ![u,z.val]) :
    ∃ v w : M, u = Arithmetic.pair v w ∧
      (baseRepresentation T X Y a).val.Evalb
        ![v,((F T M).map (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z).val] ∧
      (baseRepresentation T X Y b).val.Evalb
        ![w,((F T M).map (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z).val] := by
  obtain ⟨v,w,x,y,hu,hx,hy,hf,hg⟩ :=
    (baseRepresentation_product_eval T M X Y a b u z.val).mp hz
  let xx : Obj T M (a.eval.obj (X,Y)) := ⟨x,(baseRepresentation_support T M X Y a v x hx).2⟩
  let yy : Obj T M (b.eval.obj (X,Y)) := ⟨y,(baseRepresentation_support T M X Y b w y hy).2⟩
  have he := (chosenGraph_map_iff T M
    (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z xx).mp hf
  have he' := (chosenGraph_map_iff T M
    (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z yy).mp hg
  exact ⟨v,w,hu,by simpa only [he] using hx,by simpa only [he'] using hy⟩

/-- A represented chosen coproduct point comes from the indicated actual
injection and the same numerical payload. -/
theorem representation_sum_points (a b : SyntaxPolynomial (PredicateCategory T))
    (u : M) (z : Obj T M ((a.sum b).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (.sum a b)).val.Evalb ![u,z.val]) :
    (∃ v : M, ∃ x : Obj T M (a.eval.obj (X,Y)), u = Arithmetic.pair v 0 ∧
      (baseRepresentation T X Y a).val.Evalb ![v,x.val] ∧
      (F T M).map (coprod.inl : a.eval.obj (X,Y) ⟶ a.eval.obj (X,Y) ⨿ b.eval.obj (X,Y)) x = z) ∨
    (∃ w : M, ∃ y : Obj T M (b.eval.obj (X,Y)), u = Arithmetic.pair w 1 ∧
      (baseRepresentation T X Y b).val.Evalb ![w,y.val] ∧
      (F T M).map (coprod.inr : b.eval.obj (X,Y) ⟶ a.eval.obj (X,Y) ⨿ b.eval.obj (X,Y)) y = z) := by
  rcases (baseRepresentation_sum_eval T M X Y a b u z.val).mp hz with
    ⟨v,x,hu,hx,hf⟩ | ⟨w,y,hu,hy,hg⟩
  · let xx : Obj T M (a.eval.obj (X,Y)) := ⟨x,(baseRepresentation_support T M X Y a v x hx).2⟩
    exact Or.inl ⟨v,xx,hu,hx,(chosenGraph_map_iff T M coprod.inl xx z).mp hf⟩
  · let yy : Obj T M (b.eval.obj (X,Y)) := ⟨y,(baseRepresentation_support T M X Y b w y hy).2⟩
    exact Or.inr ⟨w,yy,hu,hy,(chosenGraph_map_iff T M coprod.inr yy z).mp hg⟩

/-- Numerical values on the summands give the value of the genuine
categorical coproduct eliminator. -/
theorem representation_coprod_desc {a b : SyntaxPolynomial (PredicateCategory T)}
    {C : PredicateCategory T} (f : a.eval.obj (X,Y) ⟶ C) (g : b.eval.obj (X,Y) ⟶ C)
    (φ ψ : M → M)
    (hf : ∀ u (x : Obj T M (a.eval.obj (X,Y))),
      (baseRepresentation T X Y a).val.Evalb ![u,x.val] → ((F T M).map f x).val = φ u)
    (hg : ∀ u (y : Obj T M (b.eval.obj (X,Y))),
      (baseRepresentation T X Y b).val.Evalb ![u,y.val] → ((F T M).map g y).val = ψ u)
    (u : M) (z : Obj T M ((a.sum b).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (.sum a b)).val.Evalb ![u,z.val]) :
    ((F T M).map (coprod.desc f g) z).val =
      if π₂ u = 0 then φ (π₁ u) else ψ (π₁ u) := by
  classical
  rcases representation_sum_points T M X Y a b u z hz with
    ⟨v,x,rfl,hx,he⟩ | ⟨w,y,rfl,hy,he⟩
  · rw [← he,← Functor.map_comp_apply,coprod.inl_desc]
    simpa using hf v x hx
  · rw [← he,← Functor.map_comp_apply,coprod.inr_desc]
    simpa using hg w y hy

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
