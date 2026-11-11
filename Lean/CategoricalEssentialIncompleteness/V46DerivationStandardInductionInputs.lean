/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionPowers

/-! # Numerical charts for the actual ordered rule summands -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
open SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The actual summand comparison preserves the rule label and reads its
children by the proved finite-power isomorphism. -/
theorem summand_representation (labels : ℕ → PredicateCategory T) (X : PredicateCategory T)
    (n : ℕ) (p : Obj T M (labels n ⨯ finitePower X n)) (tuple : M)
    (ht : (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.power .term n)).val.Evalb
      ![tuple,((F T M).map (PolynomialComparison.powerIso X n).hom
        ((F T M).map (prod.snd : labels n ⨯ finitePower X n ⟶ _) p)).val]) :
    (baseRepresentation T X (⊤_ (PredicateCategory T))
      (.product (.coefficient (labels n)) (SyntaxPolynomial.power .term n))).val.Evalb
      ![Arithmetic.pair ((F T M).map (prod.fst : labels n ⨯ finitePower X n ⟶ _) p).val tuple,
        ((F T M).map (PolynomialComparison.summandIso labels X n).hom p).val] := by
  let label := (F T M).map (prod.fst : labels n ⨯ finitePower X n ⟶ _) p
  let children := (F T M).map (PolynomialComparison.powerIso X n).hom
    ((F T M).map (prod.snd : labels n ⨯ finitePower X n ⟶ _) p)
  let out := (F T M).map (PolynomialComparison.summandIso labels X n).hom p
  have hf : (F T M).map prod.fst out = label := by
    change (F T M).map prod.fst
      ((F T M).map (prod.map (𝟙 (labels n)) (PolynomialComparison.powerIso X n).hom) p) = label
    rw [ConcreteNamedComparison.model_map_fst, (F T M).map_id]
    rfl
  have hs : (F T M).map prod.snd out = children := by
    exact ConcreteNamedComparison.model_map_snd T M
      (𝟙 (labels n)) (PolynomialComparison.powerIso X n).hom p
  exact (baseRepresentation_product_eval T M X (⊤_ (PredicateCategory T))
    (.coefficient (labels n)) (SyntaxPolynomial.power .term n) _ out.val).mpr
      ⟨label.val,tuple,label.val,children.val,rfl,
        (baseRepresentation_coefficient_eval T M X (⊤_ (PredicateCategory T))
          (labels n) _ _).mpr ⟨label.property,rfl⟩,ht,
        (chosenGraph_map_iff T M prod.fst out label).mpr hf,
        (chosenGraph_map_iff T M prod.snd out children).mpr hs⟩

/-- The chosen finite coproduct injection has the same nested arity tags
as the manuscript's ordered rule polynomial. -/
theorem injection_representation (labels : ℕ → PredicateCategory T) (X : PredicateCategory T)
    (n : ℕ) (i : Fin (n + 1)) (p : Obj T M (labels i.val ⨯ finitePower X i.val))
    (tuple : M)
    (ht : (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.power .term i.val)).val.Evalb
      ![tuple,((F T M).map (PolynomialComparison.powerIso X i.val).hom
        ((F T M).map (prod.snd : labels i.val ⨯ finitePower X i.val ⟶ _) p)).val]) :
    (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.constructors labels n)).val.Evalb
      ![ruleTag M n i
          (Arithmetic.pair ((F T M).map (prod.fst : labels i.val ⨯ finitePower X i.val ⟶ _) p).val tuple),
        ((F T M).map (PolynomialComparison.injection labels X n i) p).val] := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hb := summand_representation T M labels X 0 p tuple ht
      have he : (PolynomialComparison.summandIso labels X 0).hom = 𝟙 (labels 0 ⨯ finitePower X 0) := by
        apply prod.hom_ext <;> simp [PolynomialComparison.summandIso, PolynomialComparison.powerIso]
      rw [he, (F T M).map_id] at hb
      change (baseRepresentation T X (⊤_ (PredicateCategory T))
        (.product (.coefficient (labels 0)) (SyntaxPolynomial.power .term 0))).val.Evalb
        ![Arithmetic.pair ((F T M).map prod.fst p).val tuple,
          ((F T M).map (𝟙 (labels 0 ⨯ finitePower X 0)) p).val]
      rw [(F T M).map_id]
      exact hb
  | succ n ih =>
      revert p
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro p ht
        let a := SyntaxPolynomial.constructors labels n
        let b : SyntaxPolynomial (PredicateCategory T) :=
          .product (.coefficient (labels (n + 1))) (SyntaxPolynomial.power .term (n + 1))
        let out := (F T M).map (PolynomialComparison.summandIso labels X (n + 1)).hom p
        let target := (F T M).map (coprod.inr : b.eval.obj (X,⊤_ (PredicateCategory T)) ⟶
          a.eval.obj (X,⊤_ (PredicateCategory T)) ⨿ b.eval.obj (X,⊤_ (PredicateCategory T))) out
        have hb := summand_representation T M labels X (n + 1) p tuple ht
        have hι := (chosenGraph_map_iff T M
          (coprod.inr : b.eval.obj (X,⊤_ (PredicateCategory T)) ⟶
            a.eval.obj (X,⊤_ (PredicateCategory T)) ⨿ b.eval.obj (X,⊤_ (PredicateCategory T))) out target).mpr rfl
        have hs := (baseRepresentation_sum_eval T M X (⊤_ (PredicateCategory T)) a b
          (Arithmetic.pair (Arithmetic.pair ((F T M).map prod.fst p).val tuple) 1) target.val).mpr
            (Or.inr ⟨_,out.val,rfl,hb,hι⟩)
        simp only [PolynomialComparison.injection, ruleTag, Fin.lastCases_last, Fin.val_last,
          Functor.map_comp_apply]
        change (baseRepresentation T X (⊤_ (PredicateCategory T)) (.sum a b)).val.Evalb
          ![Arithmetic.pair (Arithmetic.pair ((F T M).map prod.fst p).val tuple) 1,target.val]
        exact hs
      · intro p ht
        let a := SyntaxPolynomial.constructors labels n
        let b : SyntaxPolynomial (PredicateCategory T) :=
          .product (.coefficient (labels (n + 1))) (SyntaxPolynomial.power .term (n + 1))
        let out := (F T M).map (PolynomialComparison.injection labels X n j) p
        let target := (F T M).map (coprod.inl : a.eval.obj (X,⊤_ (PredicateCategory T)) ⟶
          a.eval.obj (X,⊤_ (PredicateCategory T)) ⨿ b.eval.obj (X,⊤_ (PredicateCategory T))) out
        have hb := ih j p ht
        have hι := (chosenGraph_map_iff T M
          (coprod.inl : a.eval.obj (X,⊤_ (PredicateCategory T)) ⟶
            a.eval.obj (X,⊤_ (PredicateCategory T)) ⨿ b.eval.obj (X,⊤_ (PredicateCategory T))) out target).mpr rfl
        have hs := (baseRepresentation_sum_eval T M X (⊤_ (PredicateCategory T)) a b
          (Arithmetic.pair (ruleTag M n j
            (Arithmetic.pair ((F T M).map prod.fst p).val tuple)) 0) target.val).mpr
            (Or.inl ⟨_,out.val,rfl,hb,hι⟩)
        simp only [PolynomialComparison.injection, ruleTag, Fin.lastCases_castSucc, Fin.val_castSucc,
          Functor.map_comp_apply]
        change (baseRepresentation T X (⊤_ (PredicateCategory T)) (.sum a b)).val.Evalb
          ![Arithmetic.pair (ruleTag M n j
            (Arithmetic.pair ((F T M).map prod.fst p).val tuple)) 0,target.val]
        exact hs

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
