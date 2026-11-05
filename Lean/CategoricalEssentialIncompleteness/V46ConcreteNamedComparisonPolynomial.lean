/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionMap
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation

/-! # Forward polynomial charts for actual morphisms with numerical values -/

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
variable {X Y C D : PredicateCategory T}

/-- Known scalar values of the two actual recursive-position morphisms
give a chart for the actual categorical polynomial map. This forward
statement uses only the representation and the finite AST. -/
theorem representation_map (f : X ⟶ C) (g : Y ⟶ D) (φ ψ : M → M)
    (hf : ∀ x : Obj T M X, ((F T M).map f x).val = φ x.val)
    (hg : ∀ y : Obj T M Y, ((F T M).map g y).val = ψ y.val)
    (q : SyntaxPolynomial (PredicateCategory T)) (u : M) (z : Obj T M (q.eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y q).val.Evalb ![u,z.val]) :
    (baseRepresentation T C D q).val.Evalb
      ![ConcreteNamedSubstitution.mapChildren φ ψ q u,
        ((F T M).map (q.eval.map ((f,g) : (X,Y) ⟶ (C,D))) z).val] := by
  induction q generalizing u with
  | term =>
      have he := (baseRepresentation_term_eval T M X Y u z.val).mp hz
      rw [baseRepresentation_term_eval]
      change C.val.Evalb ![((F T M).map f z).val] ∧ ((F T M).map f z).val = φ u
      exact ⟨((F T M).map f z).property, (hf z).trans (congrArg φ he.2)⟩
  | formula =>
      have he := (baseRepresentation_formula_eval T M X Y u z.val).mp hz
      rw [baseRepresentation_formula_eval]
      change D.val.Evalb ![((F T M).map g z).val] ∧ ((F T M).map g z).val = ψ u
      exact ⟨((F T M).map g z).property, (hg z).trans (congrArg ψ he.2)⟩
  | coefficient E =>
      change (baseRepresentation T C D (.coefficient E)).val.Evalb
        ![u, ((F T M).map (𝟙 E) z).val]
      rw [(F T M).map_id]
      exact (baseRepresentation_coefficient_eval T M C D E u z.val).mpr
        ((baseRepresentation_coefficient_eval T M X Y E u z.val).mp hz)
  | unit =>
      change (baseRepresentation T C D .unit).val.Evalb
        ![0, ((F T M).map (𝟙 (⊤_ (PredicateCategory T))) z).val]
      rw [(F T M).map_id]
      exact (baseRepresentation_unit_eval T M C D 0 z.val).mpr ⟨z.property,rfl⟩
  | product a b ia ib =>
      obtain ⟨x,y,r,s,he,hr,hs,hzr,hzs⟩ :=
        (baseRepresentation_product_eval T M X Y a b u z.val).mp hz
      let rr : Obj T M (a.eval.obj (X,Y)) :=
        ⟨r,(baseRepresentation_support T M X Y a x r hr).2⟩
      let ss : Obj T M (b.eval.obj (X,Y)) :=
        ⟨s,(baseRepresentation_support T M X Y b y s hs).2⟩
      let fa := a.eval.map ((f,g) : (X,Y) ⟶ (C,D))
      let fb := b.eval.map ((f,g) : (X,Y) ⟶ (C,D))
      let out := (F T M).map (prod.map fa fb) z
      let out₁ := (F T M).map fa rr
      let out₂ := (F T M).map fb ss
      have h₁ : (F T M).map (prod.fst : a.eval.obj (C,D) ⨯ b.eval.obj (C,D) ⟶ _) out = out₁ :=
        (model_map_fst T M fa fb z).trans
          (congrArg ((F T M).map fa) ((chosenGraph_map_iff T M
            (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z rr).mp hzr))
      have h₂ : (F T M).map (prod.snd : a.eval.obj (C,D) ⨯ b.eval.obj (C,D) ⟶ _) out = out₂ :=
        (model_map_snd T M fa fb z).trans
          (congrArg ((F T M).map fb) ((chosenGraph_map_iff T M
            (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z ss).mp hzs))
      have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.product a b) u =
          Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ a x)
            (ConcreteNamedSubstitution.mapChildren φ ψ b y) := by
        simp [he,ConcreteNamedSubstitution.mapChildren]
      rw [hm]
      exact (baseRepresentation_product_eval T M C D a b _ out.val).mpr
        ⟨_,_,out₁.val,out₂.val,rfl,ia x rr hr,ib y ss hs,
          (chosenGraph_map_iff T M (prod.fst : a.eval.obj (C,D) ⨯ b.eval.obj (C,D) ⟶ _)
            out out₁).mpr h₁,
          (chosenGraph_map_iff T M (prod.snd : a.eval.obj (C,D) ⨯ b.eval.obj (C,D) ⟶ _)
            out out₂).mpr h₂⟩
  | sum a b ia ib =>
      let fa := a.eval.map ((f,g) : (X,Y) ⟶ (C,D))
      let fb := b.eval.map ((f,g) : (X,Y) ⟶ (C,D))
      let out := (F T M).map (coprod.map fa fb) z
      rcases (baseRepresentation_sum_eval T M X Y a b u z.val).mp hz with
          ⟨x,r,he,hr,hi⟩ | ⟨y,s,he,hs,hi⟩
      · let rr : Obj T M (a.eval.obj (X,Y)) :=
          ⟨r,(baseRepresentation_support T M X Y a x r hr).2⟩
        let out₁ := (F T M).map fa rr
        have h₁ : (F T M).map (coprod.inl : a.eval.obj (C,D) ⟶
            a.eval.obj (C,D) ⨿ b.eval.obj (C,D)) out₁ = out :=
          (model_sum_map_inl T M fa fb rr).symm.trans
            (congrArg ((F T M).map (coprod.map fa fb))
              ((chosenGraph_map_iff T M (coprod.inl : a.eval.obj (X,Y) ⟶
                a.eval.obj (X,Y) ⨿ b.eval.obj (X,Y)) rr z).mp hi))
        have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.sum a b) u =
            Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ a x) 0 := by
          simp [he,ConcreteNamedSubstitution.mapChildren]
        rw [hm]
        exact (baseRepresentation_sum_eval T M C D a b _ out.val).mpr
          (Or.inl ⟨_,out₁.val,rfl,ia x rr hr,
            (chosenGraph_map_iff T M (coprod.inl : a.eval.obj (C,D) ⟶
              a.eval.obj (C,D) ⨿ b.eval.obj (C,D)) out₁ out).mpr h₁⟩)
      · let ss : Obj T M (b.eval.obj (X,Y)) :=
          ⟨s,(baseRepresentation_support T M X Y b y s hs).2⟩
        let out₂ := (F T M).map fb ss
        have h₂ : (F T M).map (coprod.inr : b.eval.obj (C,D) ⟶
            a.eval.obj (C,D) ⨿ b.eval.obj (C,D)) out₂ = out :=
          (model_sum_map_inr T M fa fb ss).symm.trans
            (congrArg ((F T M).map (coprod.map fa fb))
              ((chosenGraph_map_iff T M (coprod.inr : b.eval.obj (X,Y) ⟶
                a.eval.obj (X,Y) ⨿ b.eval.obj (X,Y)) ss z).mp hi))
        have hm : ConcreteNamedSubstitution.mapChildren φ ψ (.sum a b) u =
            Arithmetic.pair (ConcreteNamedSubstitution.mapChildren φ ψ b y) 1 := by
          simp [he,ConcreteNamedSubstitution.mapChildren]
        rw [hm]
        exact (baseRepresentation_sum_eval T M C D a b _ out.val).mpr
          (Or.inr ⟨_,out₂.val,rfl,ib y ss hs,
            (chosenGraph_map_iff T M (coprod.inr : b.eval.obj (C,D) ⟶
              a.eval.obj (C,D) ⨿ b.eval.obj (C,D)) out₂ out).mpr h₂⟩)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
