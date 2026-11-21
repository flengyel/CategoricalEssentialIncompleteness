/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteSigmaOne
public import Mathlib.Tactic.FinCases

/-! # Vector append for postfix syntax words -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Words

/-- Foundation's `concat` adjoins one final entry. This blueprint instead
appends an entire second vector, retaining the canonical zero/cons code. -/
def appendBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “o b. o = b”
  adjoin := .mkSigma “o x xs ih b. !adjoinDef.val o x ih”

section Models
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def appendConstruction : VecRec.Construction M appendBlueprint where
  nil p := p 0
  adjoin _ x _ ih := adjoin x ih
  nil_defined := .mk fun v => by simp [appendBlueprint]
  adjoin_defined := .mk fun v => by simp [appendBlueprint]

noncomputable def append (a b : M) : M := appendConstruction.result ![b] a

@[simp] theorem append_nil (b : M) : append 0 b = b := by
  simp [append, appendConstruction]

@[simp] theorem append_adjoin (x a b : M) :
    append (adjoin x a) b = adjoin x (append a b) := by
  simp [append, appendConstruction]

end Models

/-- Variables are output, first word, second word. -/
def appendDef : 𝚺₁.Semisentence 3 := appendBlueprint.resultDef

section Models
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem appendDef_eval (o a b : M) :
    appendDef.val.Evalb ![o, a, b] ↔ o = append a b := by
  simpa [appendDef, append, Matrix.constant_eq_singleton] using
    (appendConstruction (M := M)).eval_resultDef ![o, a, b]

instance append_defined : 𝚺₁-Function₂ (append : M → M → M) via appendDef := .mk fun v => by
  simpa [appendDef, append, Matrix.constant_eq_singleton] using
    (appendConstruction (M := M)).eval_resultDef v

instance append_definable : 𝚺₁-Function₂ (append : M → M → M) :=
  append_defined.to_definable

instance append_definable' (Γ m) : Γ-[m + 1]-Function₂ (append : M → M → M) :=
  append_definable.of_sigmaOne

@[simp] theorem append_nil_right (a : M) : append a 0 = a := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x a ih => simp [ih]

@[simp] theorem append_assoc (a b c : M) : append (append a b) c = append a (append b c) := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x a ih => simp [ih]

@[simp] theorem len_append (a b : M) : len (append a b) = len a + len b := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x a ih => simp [ih, add_assoc, add_comm 1 (len b)]

@[simp] theorem append_singleton (a x : M) : append a (adjoin x 0) = concat a x := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin z a ih => simp [ih]

theorem nth_append_left (a b i : M) (hi : i < len a) : nth (append a b) i = nth a i := by
  induction a using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x a ih =>
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp
    · simpa using ih i (by simpa using hi)

@[simp] theorem nth_append_right (a b i : M) : nth (append a b) (len a + i) = nth b i := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x a ih =>
    simp only [append_adjoin, len_adjoin]
    have he : len a + 1 + i = (len a + i) + 1 := by
      simp [add_assoc, add_comm 1 i]
    rw [he, nth_adjoin_succ]
    exact ih

/-- Every nonempty word has a final record and preceding prefix, including words of
nonstandard model length. -/
theorem nil_or_snoc (a : M) : a = 0 ∨ ∃ b x : M, a = concat b x := by
  induction a using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => exact Or.inl rfl
  case adjoin x a ih =>
    right
    rcases ih with rfl | ⟨b, y, rfl⟩
    · exact ⟨0, x, by simp⟩
    · exact ⟨adjoin x b, y, by simp⟩

theorem snoc_injective (a b x y : M) (h : concat a x = concat b y) : a = b ∧ x = y := by
  have hl : len a = len b := by
    have hn := congrArg len h
    simpa using hn
  have hxy : x = y := by
    have hn := congrArg (fun w => nth w (len a)) h
    rw [concat_nth_len] at hn
    rw [hl, concat_nth_len] at hn
    exact hn
  refine ⟨nth_ext hl (fun i hi => ?_), hxy⟩
  have hn := congrArg (fun w => nth w i) h
  simpa only [concat_nth_lt a x hi, concat_nth_lt b y (by simpa only [hl] using hi)] using hn

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Words
