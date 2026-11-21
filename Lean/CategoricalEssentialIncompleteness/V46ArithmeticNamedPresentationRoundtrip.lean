/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationAlpha

/-! # Hilbert proof-equivalence for the given named presentation

The statement ranges over every original named formula, including arbitrary repeated
binders and implication/negation words. Its conclusion is a proof of equivalence in
the seven-scheme Hilbert calculus.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
local instance presentationNamedDecidableEq : DecidableEq NamedArithmeticSignature.Formula := Classical.decEq _

variable (Γ : SyntacticPredicates.Carrier)
local notation "S" => ArithmeticNamedProofConnectives.system Γ

/-- The source NNF back presentation elaborates to a formula provably
equivalent to the original named formula, rather than just erasing names. -/
theorem formula_roundtrip (n : ℕ) (φ : Formula) (hφ : Bound n φ) :
    ∀ seed, n ≤ seed →
    S ⊢ ArithmeticNamedOpenTranslation.formula seed ![] Fin.val (formula n φ) 🡘 φ := by
  induction φ with
  | equal r t =>
      intro seed _
      have hb := bound_equal.mp hφ
      change S ⊢ (NamedFiniteSyntax.Formula.equal
        (ArithmeticNamedOpenTranslation.term ![] Fin.val (term n r))
        (ArithmeticNamedOpenTranslation.term ![] Fin.val (term n t))) 🡘 (.equal r t)
      rw [term_roundtrip n r hb.1,term_roundtrip n t hb.2]
      exact E_id
  | relation k s children =>
      intro seed _
      rcases relation_presentation k s children with ⟨r,t,he⟩
      have hb : TermBound n r ∧ TermBound n t := by
        rw [he] at hφ
        simpa [Bound,names,less,NamedFiniteSyntax.Formula.freeVariables,
          List.ofFn_succ,TermBound,or_imp,forall_and] using hφ
      rw [he]
      change S ⊢ (NamedArithmeticSignature.less
        (ArithmeticNamedOpenTranslation.term ![] Fin.val (term n r))
        (ArithmeticNamedOpenTranslation.term ![] Fin.val (term n t))) 🡘 less r t
      rw [term_roundtrip n r hb.1,term_roundtrip n t hb.2]
      exact E_id
  | neg φ ih =>
      intro seed hn
      exact E_trans (ArithmeticNamedProofConnectives.nnf_neg Γ (formula n φ) seed ![] Fin.val)
        (ENN_of_E (ih hφ seed hn))
  | imp φ ψ il ir =>
      intro seed hn
      have hb := bound_imp.mp hφ
      exact E_trans (ArithmeticNamedProofConnectives.implication Γ
        (formula n φ) (formula n ψ) seed ![] Fin.val)
        (ECC_of_E_of_E (il hb.1 seed hn) (ir hb.2 seed hn))
  | all x φ ih =>
      intro seed hn
      have hb := bound_all.mp hφ
      have he := closed_name_alpha Γ (⟨x,hb.1⟩ : Fin n) (formula n φ) seed hn
      have hi := ArithmeticNamedProofConnectives.all_equivalence Γ x
        (ih hb.2 (seed+1) (hn.trans (Nat.le_succ seed)))
      simpa only [formula,dite_eq_left hb.1,ArithmeticNamedOpenTranslation.formula]
        using E_trans (E_symm he) hi

/-- Free source variables retain their literal names, including the
proper removal of precisely the name bound by each quantifier. -/
theorem formula_fvar (n : ℕ) (φ : Formula) (hφ : Bound n φ) (y : Fin n)
    (hy : (formula n φ).FVar? y) : y.val ∈ φ.freeVariables := by
  induction φ with
  | equal r t =>
      have h : (term n r).FVar? y ∨ (term n t).FVar? y := by
        simpa [formula,Fin.exists_fin_two] using hy
      exact List.mem_append.mpr (h.imp (term_fvar n r y) (term_fvar n t y))
  | relation k s children =>
      rcases relation_presentation k s children with ⟨r,t,he⟩
      rw [he] at hy ⊢
      have h : (term n r).FVar? y ∨ (term n t).FVar? y := by
        simpa [formula,less,Fin.exists_fin_two] using hy
      simpa [less,NamedFiniteSyntax.Formula.freeVariables,List.ofFn_succ] using
        List.mem_append.mpr (h.imp (term_fvar n r y) (term_fvar n t y))
  | neg φ ih =>
      exact ih hφ (by simpa [formula,Semiformula.FVar?] using hy)
  | imp φ ψ il ir =>
      have hb := bound_imp.mp hφ
      have h : (formula n φ).FVar? y ∨ (formula n ψ).FVar? y := by
        simpa [formula,Semiformula.FVar?] using hy
      exact List.mem_append.mpr (h.imp (il hb.1) (ir hb.2))
  | all x φ ih =>
      have hb := bound_all.mp hφ
      have hy' : (bindName (⟨x,hb.1⟩ : Fin n) ▹ formula n φ).FVar? y := by
        simpa only [formula,dite_eq_left hb.1,Semiformula.FVar?,Semiformula.freeVariables_all] using hy
      rcases Semiformula.fvar?_rew hy' with ⟨i,hi⟩ | ⟨z,hz,hzy⟩
      · exact i.elim0
      · by_cases he : z = (⟨x,hb.1⟩ : Fin n)
        · simp [bindName,he] at hzy
        · have hzy' : z = y := by simpa [bindName,he] using hzy
          subst z
          have hyne : y.val ≠ x := fun h => he (Fin.ext h)
          have hm := ih hb.2 hz
          simpa [NamedFiniteSyntax.Formula.freeVariables,hyne] using hm

theorem formula_closed (n : ℕ) (φ : Formula) (hφ : Bound n φ)
    (hclosed : φ.freeVariables = []) : (formula n φ).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have h := formula_fvar n φ hφ y hy
  simp [hclosed] at h

/-- A source sentence attached to the literal given named sentence. -/
def sentence (φ : Formula) (hφ : φ.freeVariables = []) : ArithmeticSentence :=
  (formula (nameBound φ) φ).toEmpty (formula_closed (nameBound φ) φ (bound_nameBound φ) hφ)

/-- Closing the free-name type preserves the Hilbert proof comparison to each original
named sentence. -/
theorem sentence_roundtrip (φ : Formula) (hφ : φ.freeVariables = []) :
    S ⊢ ArithmeticNamedTranslation.translateFormula (nameBound φ) ![] (sentence φ hφ) 🡘 φ := by
  have hr := formula_roundtrip Γ (nameBound φ) φ (bound_nameBound φ) (nameBound φ) le_rfl
  have he := ArithmeticNamedOpenTranslation.formula_rew (sentence φ hφ)
    (Rew.emb (L := ℒₒᵣ)) (nameBound φ) ![] (Fin.val : Fin (nameBound φ) → ℕ) ![] Empty.elim
    (by intro i; exact i.elim0) (by intro e; exact e.elim)
  have he' : ArithmeticNamedOpenTranslation.formula (nameBound φ) ![] Fin.val
      (formula (nameBound φ) φ) =
      ArithmeticNamedTranslation.translateFormula (nameBound φ) ![] (sentence φ hφ) := by
    simpa only [sentence,Semiformula.emb_toEmpty,
      ArithmeticNamedOpenTranslation.formula_empty] using he
  exact he' ▸ hr

/-- The fixed source-to-Hilbert proof translation starts with seed zero. Changing its
fresh binders uses the already proved alpha steps. -/
theorem sentence_zero_roundtrip (φ : Formula) (hφ : φ.freeVariables = []) :
    S ⊢ ArithmeticNamedTranslation.translateFormula 0 ![] (sentence φ hφ) 🡘 φ := by
  have hs := ArithmeticNamedProofConnectives.seed_mono Γ (sentence φ hφ)
    0 (nameBound φ) ![] Empty.elim
    (by intro i; exact i.elim0) (by intro e; exact e.elim) (Nat.zero_le _)
  have hs' : S ⊢ ArithmeticNamedTranslation.translateFormula 0 ![] (sentence φ hφ) 🡘
      ArithmeticNamedTranslation.translateFormula (nameBound φ) ![] (sentence φ hφ) := by
    simpa only [ArithmeticNamedOpenTranslation.formula_empty] using hs
  exact E_trans hs' (sentence_roundtrip Γ φ hφ)

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
