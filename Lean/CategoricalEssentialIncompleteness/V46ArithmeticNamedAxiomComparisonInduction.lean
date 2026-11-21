/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonBasic

/-! # Named induction and the source PA universal closure -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
open NamedArithmeticSignature ArithmeticNamedOpenTranslation ArithmeticNamedProofConnectives
local instance inductionComparisonDecidableEq : DecidableEq Fm := Classical.decEq _
variable (A : SyntacticPredicates.Carrier)
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
local notation "S" => ArithmeticNamedProofConnectives.system A

private theorem nativeInduction (φ : Fm) (h : S ⊢ φ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mp h
private theorem propositionalInduction (φ : Fm) (h : D φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mpr h

/-- Fresh names in the precise order introduced by source allClosure. -/
def closureContext (start : ℕ) : (n : ℕ) → Fin n → ℕ
  | 0 => Fin.elim0
  | n+1 => Matrix.vecCons (start+n) (closureContext start n)

theorem closureContext_bound (start n : ℕ) : ∀ i, closureContext start n i < start+n := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (ih j)

/-- Source universal closure is realized by the Hilbert Gen rule, with its source binder
order and every fresh name retained. -/
theorem derives_allClosure {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (start : ℕ) (fn : ξ → ℕ)
    (h : D (formula (start+n) (closureContext start n) fn φ)) :
    D (formula start ![] fn (∀¹* φ)) := by
  revert φ
  induction n with
  | zero => intro φ h; exact h
  | succ n ih =>
      intro φ h
      exact ih (∀¹ φ) (.generalization (start+n) h)

private def zeroSource : ArithmeticTerm ℕ := .func .zero Fin.elim0

private def successorTerm : ArithmeticSemiterm ℕ 1 :=
  .func .add ![.bvar 0,.func .one Fin.elim0]

private def inductionSuccessor : ArithmeticSemiformula ℕ 1 → ArithmeticSemiformula ℕ 1 :=
  fun φ => φ/[successorTerm]

private theorem successor_substitution (φ : ArithmeticSemiformula ℕ 1)
    (x : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < x) :
    (formula (x+1) ![x] fn φ).substitute x (add (.var x) one) =
      some (formula (x+1) ![x] fn (inductionSuccessor φ)) := by
  apply formula_substitution_rew φ
    (Rew.subst ![successorTerm])
    (x+1) ![x] fn ![x] fn x (add (.var x) one)
  · exact Nat.lt_succ_self x
  · intro z hz
    have he : z = x := by
      simpa [NamedFiniteSyntax.Term.freeVariables] using hz
    subst z
    exact Nat.lt_succ_self x
  · intro i
    fin_cases i
    change (if x = x then add (.var x) one else NamedFiniteSyntax.Term.var x) = add (.var x) one
    exact ite_eq_left rfl
  · intro i
    change (if fn i = x then add (.var x) one else NamedFiniteSyntax.Term.var (fn i)) =
      NamedFiniteSyntax.Term.var (fn i)
    exact ite_eq_right (Nat.ne_of_lt (hf i))

/-- The induction scheme for the translated formula uses substitution of zero and
successor. Both terms are free for the induction variable. -/
theorem succInd_admissible (hΓ : ExtendsPA A) (φ : ArithmeticSemiformula ℕ 1)
    (x : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < x) :
    D (formula x ![] fn (succInd φ)) := by
  let body := formula (x+1) ![x] fn φ
  let base := formula (x+1) ![] fn (φ/[zeroSource])
  let step := formula (x+1) ![x] fn (inductionSuccessor φ)
  have h0 : body.FreeFor x zero :=
    formula_freeFor_bounded φ (x+1) ![x] fn x zero (by simp)
  have hs : body.FreeFor x (add (.var x) one) := by
    apply formula_freeFor_bounded φ (x+1) ![x] fn x (add (.var x) one)
    intro z hz
    have he : z = x := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
    subst z
    exact Nat.lt_succ_self x
  have s0 : body.substitute x zero = some base :=
    instance_substitution φ zeroSource x fn hf
  have ss : body.substitute x (add (.var x) one) = some step :=
    successor_substitution φ x fn hf
  have hp : D (inductionMatrix x body base step) :=
    derives_of_closure A _ _ ((extendsPA_iff_canonical A).mp hΓ _
      (PASeed.induction x body base step h0 hs s0 ss))
  have heBase := seed_mono A (φ/[zeroSource]) x (x+1) ![] fn
    (fun i => i.elim0) hf (Nat.le_succ x)
  have heStep := all_equivalence A x
    (implication A φ (inductionSuccessor φ) (x+1) ![x] fn)
  have heInner := implication A (∀¹ (φ 🡒 inductionSuccessor φ)) (∀¹ φ) x ![] fn
  have heOuter := implication A (φ/[zeroSource])
    ((∀¹ (φ 🡒 inductionSuccessor φ)) 🡒 (∀¹ φ)) x ![] fn
  have hShape : succInd φ =
      ((φ/[zeroSource]) 🡒 ((∀¹ (φ 🡒 inductionSuccessor φ)) 🡒 (∀¹ φ))) := by
    simp [succInd,inductionSuccessor,zeroSource,successorTerm]
    constructor
    · apply congrArg (fun t : ArithmeticTerm ℕ => φ/[t])
      change Semiterm.func _ _ = Semiterm.func _ _
      congr 1
      funext i
      exact i.elim0
    · apply congrArg (fun t : ArithmeticSemiterm ℕ 1 => φ/[t])
      change Semiterm.func _ _ = Semiterm.func _ _
      congr 1
      funext i
      fin_cases i
      · rfl
      · change Semiterm.func _ _ = Semiterm.func _ _
        congr 1
        funext j
        exact j.elim0
  have he : S ⊢ formula x ![] fn (succInd φ) 🡘 inductionMatrix x body base step := by
    rw [hShape]
    exact E_trans heOuter (ECC_of_E_of_E heBase
      (E_trans heInner (ECC_of_E_of_E heStep E_id)))
  exact nativeInduction A _ ((K_right he) ⨀ propositionalInduction A _ hp)

/-- Every source PA induction axiom has a proof over the given named enumeration. No
source-axiom admissibility is assumed. -/
theorem induction_admissible (hΓ : ExtendsPA A) (φ : ArithmeticSemiformula ℕ 1) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (.univCl (succInd φ))) := by
  let k := (succInd φ).fvSup
  let n := 0+k
  let fn : ℕ → ℕ := fun i => if h : i < n then closureContext 1 n ⟨i,h⟩ else 0
  have hf : ∀ i, fn i < 1+n := by
    intro i
    dsimp [fn]
    split
    · exact closureContext_bound 1 n _
    · omega
  have hp := succInd_admissible A hΓ φ (1+n) fn hf
  have hr : formula (1+n) (closureContext 1 n) (fun _ : ℕ => 0)
      (Rew.fixitr 0 k ▹ succInd φ) = formula (1+n) ![] fn (succInd φ) := by
    apply formula_rew (succInd φ) (Rew.fixitr 0 k) (1+n)
      (closureContext 1 n) (fun _ : ℕ => 0) ![] fn
    · intro i; exact i.elim0
    · intro i
      simp only [Rew.fixitr_fvar]
      split_ifs with hi
      · simp [fn,n,hi,term]
      · simp [fn,n,hi,term]
  have hq : D (formula 1 ![] (fun _ : ℕ => 0)
      ((succInd φ).univCl')) :=
    derives_allClosure A (Rew.fixitr 0 k ▹ succInd φ) 1 (fun _ : ℕ => 0) (by rw [hr]; exact hp)
  have hEmb := formula_emb (.univCl (succInd φ)) 1 ![] (fun _ : ℕ => 0)
  rw [Semiformula.coe_univCl_eq_univCl'] at hEmb
  have hc : D (ArithmeticNamedTranslation.translateFormula 1 ![] (.univCl (succInd φ))) := hEmb ▸ hq
  have he := seed_mono A (.univCl (succInd φ)) 0 1 ![] Empty.elim
    (fun i => i.elim0) (fun i => i.elim) (by decide)
  rw [formula_empty,formula_empty] at he
  exact nativeInduction A _ ((K_right he) ⨀ propositionalInduction A _ hc)

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
