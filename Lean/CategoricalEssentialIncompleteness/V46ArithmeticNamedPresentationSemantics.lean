/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationRoundtrip

/-! # Semantic roundtrip for each named arithmetic sentence

The semantic structure K is independent of the standard or nonstandard
arithmetic structure carrying the word codes.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
universe w
variable {K : Type w} [ORingStructure K]

/-- The closing rewrite changes precisely the original variable's
valuation, including beneath repeated binders. -/
theorem eval_bindName {n : ℕ} (x : Fin n) (φ : Semiformula ℒₒᵣ (Fin n) 0)
    (ρ : ℕ → K) (a : K) :
    (bindName x ▹ φ).Eval (s := Arithmetic.standardModel K) ![a] (fun i => ρ i.val) ↔
      φ.Eval (s := Arithmetic.standardModel K) ![] (fun i => Function.update ρ x.val a i.val) := by
  classical
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (s := Arithmetic.standardModel K) ![a] (fun i : Fin n => ρ i.val) ∘
      bindName x ∘ Semiterm.bvar) = (![] : Fin 0 → K) := by
    funext i; exact i.elim0
  have hf : (Semiterm.val (s := Arithmetic.standardModel K) ![a] (fun i : Fin n => ρ i.val) ∘
      bindName x ∘ Semiterm.fvar) = (fun i : Fin n => Function.update ρ x.val a i.val) := by
    funext i
    by_cases he : i = x
    · subst i; simp [bindName,Function.comp_def]
    · have hne : i.val ≠ x.val := fun h => he (Fin.ext h)
      simp [bindName,he,Function.comp_def,Function.update_of_ne hne]
  rw [hb,hf]

/-- Every arbitrary original named formula has the semantics of its
source presentation, with the exact original assignment of free names. -/
theorem formula_semantics (n : ℕ) (φ : Formula) (hφ : Bound n φ) :
    ∀ ρ : ℕ → K,
      (formula n φ).Eval (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) ↔
        φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ := by
  induction φ with
  | equal r t =>
      intro ρ
      have hb := bound_equal.mp hφ
      change (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) =
        (term n t).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) ↔ _
      rw [term_value n r hb.1 ρ,term_value n t hb.2 ρ]
      rfl
  | relation k s children =>
      intro ρ
      rcases relation_presentation k s children with ⟨r,t,he⟩
      rw [he] at hφ ⊢
      have hb : TermBound n r ∧ TermBound n t := by
        simpa [Bound,names,less,List.ofFn_succ,TermBound,or_imp,forall_and] using hφ
      change (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) <
        (term n t).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) ↔ _
      rw [term_value n r hb.1 ρ,term_value n t hb.2 ρ]
      exact (ArithmeticNamedTranslation.holds_less r t ρ).symm
  | neg φ ih =>
      intro ρ
      simpa only [formula,LogicalConnective.HomClass.map_neg,LogicalConnective.Prop.neg_eq,
        NamedFiniteSyntax.Formula.Holds] using not_congr (ih hφ ρ)
  | imp φ ψ il ir =>
      intro ρ
      have hb := bound_imp.mp hφ
      simpa only [formula,LogicalConnective.HomClass.map_imply,LogicalConnective.Prop.arrow_eq,
        NamedFiniteSyntax.Formula.Holds] using imp_congr (il hb.1 ρ) (ir hb.2 ρ)
  | all x φ ih =>
      intro ρ
      have hb := bound_all.mp hφ
      change (if hx : x < n then ∀¹ (bindName ⟨x,hx⟩ ▹ formula n φ) else formula n φ).Eval
        (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) ↔ _
      rw [dite_eq_left hb.1]
      change (∀ a : K, (bindName (⟨x,hb.1⟩ : Fin n) ▹ formula n φ).Eval
        (s := Arithmetic.standardModel K) ![a] (fun i => ρ i.val)) ↔
        ∀ a : K, φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations
          (Function.update ρ x a)
      exact forall_congr' (fun a => (eval_bindName ⟨x,hb.1⟩ (formula n φ) ρ a).trans
        (ih hb.2 (Function.update ρ x a)))

/-- Sentence closure preserves the original named sentence's semantics in every arithmetic
structure K, for every named variable assignment. -/
theorem sentence_semantics (φ : Formula) (hφ : φ.freeVariables = []) (ρ : ℕ → K) :
    (sentence φ hφ).Evalb (s := Arithmetic.standardModel K) ![] ↔
      φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ := by
  have h := formula_semantics (nameBound φ) φ (bound_nameBound φ) ρ
  have he : (formula (nameBound φ) φ).Eval (s := Arithmetic.standardModel K) ![]
      (fun i => ρ i.val) ↔ (sentence φ hφ).Evalb (s := Arithmetic.standardModel K) ![] := by
    rw [← Semiformula.emb_toEmpty (formula (nameBound φ) φ)
      (formula_closed (nameBound φ) φ (bound_nameBound φ) hφ)]
    exact Semiformula.eval_emb _
  exact he.symm.trans h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
