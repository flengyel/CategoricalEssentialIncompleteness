/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws

/-! # The singleton tree accepted by the parser is the input word -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open Coding

def stackWordBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “o. o = 0”
  adjoin := .mkSigma “o block tail ih. ∃ word, !pi₁Def.val word block ∧ !Words.appendDef.val o ih word”

def copyPrefixBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “o word. o = 0”
  succ := .mkSigma “o prev i word. ∃ record, !nthDef.val record word i ∧ !concatDef.val o prev record”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance conservationDecidableEq1 : DecidableEq M := Classical.decEq M

def stackWordConstruction : VecRec.Construction M stackWordBlueprint where
  nil _ := 0
  adjoin _ block _ ih := Words.append ih (π₁ block)
  nil_defined := .mk fun v => by simp [stackWordBlueprint]
  adjoin_defined := .mk fun v => by simp [stackWordBlueprint]

noncomputable def stackWord (stack : M) : M := stackWordConstruction.result ![] stack

@[simp] theorem stackWord_nil : stackWord (0 : M) = 0 := by simp [stackWord, stackWordConstruction]
@[simp] theorem stackWord_adjoin (block stack : M) :
    stackWord (adjoin block stack) = Words.append (stackWord stack) (π₁ block) := by
  simp [stackWord, stackWordConstruction]

def copyPrefixConstruction : PR.Construction M copyPrefixBlueprint where
  zero _ := 0
  succ v i prev := concat prev (nth (v 0) i)
  zero_defined := .mk fun v => by simp [copyPrefixBlueprint]
  succ_defined := .mk fun v => by simp [copyPrefixBlueprint]

noncomputable def copyPrefix (word n : M) : M := copyPrefixConstruction.result ![word] n

@[simp] theorem copyPrefix_zero (word : M) : copyPrefix word 0 = 0 := by
  simp [copyPrefix, copyPrefixConstruction]
@[simp] theorem copyPrefix_succ (word n : M) :
    copyPrefix word (n + 1) = concat (copyPrefix word n) (nth word n) := by
  simp [copyPrefix, copyPrefixConstruction]
end Models

def stackWordGraph : 𝚺₁.Semisentence 2 := stackWordBlueprint.resultDef

def reorderPrefixGraph (R : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 :=
  .mkSigma “o word n. !R.val o n word”

def copyPrefixGraph : 𝚺₁.Semisentence 3 := reorderPrefixGraph copyPrefixBlueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance conservationDecidableEq2 : DecidableEq M := Classical.decEq M

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem reorderPrefixGraph_eval (R : 𝚺₁.Semisentence 3) (o word n : M) :
    (reorderPrefixGraph R).val.Evalb ![o, word, n] ↔ R.val.Evalb ![o, n, word] := by
  simp [reorderPrefixGraph]

@[simp] theorem stackWordGraph_eval (o stack : M) :
    stackWordGraph.val.Evalb ![o, stack] ↔ o = stackWord stack := by
  have hp : (fun i : Fin 0 => (![o, stack] : Fin 2 → M) i.succ.succ) = ![] := by
    funext i
    exact i.elim0
  have he := (stackWordConstruction (M := M)).eval_resultDef ![o, stack]
  rw [hp] at he
  change stackWordBlueprint.resultDef.val.Evalb ![o, stack] ↔
    o = stackWordConstruction.result ![] stack
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance stackWord_defined : 𝚺₁-Function₁ (stackWord : M → M) via stackWordGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using stackWordGraph_eval (v 0) (v 1)
instance stackWord_definable : 𝚺₁-Function₁ (stackWord : M → M) := stackWord_defined.to_definable
instance stackWord_definable' (Γ m) : Γ-[m + 1]-Function₁ (stackWord : M → M) :=
  stackWord_definable.of_sigmaOne

@[simp] theorem copyPrefixGraph_eval (o word n : M) :
    copyPrefixGraph.val.Evalb ![o, word, n] ↔ o = copyPrefix word n := by
  have hp : (fun i : Fin 1 => (![o, n, word] : Fin 3 → M) i.succ.succ) = ![word] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have he := (copyPrefixConstruction (M := M)).result_defined_iff ![o, n, word]
  rw [hp] at he
  apply (reorderPrefixGraph_eval copyPrefixBlueprint.resultDef o word n).trans
  change copyPrefixBlueprint.resultDef.val.Evalb ![o, n, word] ↔
    o = copyPrefixConstruction.result ![word] n
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance copyPrefix_defined : 𝚺₁-Function₂ (copyPrefix : M → M → M) via copyPrefixGraph := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using copyPrefixGraph_eval (v 0) (v 1) (v 2)
instance copyPrefix_definable : 𝚺₁-Function₂ (copyPrefix : M → M → M) := copyPrefix_defined.to_definable
instance copyPrefix_definable' (Γ m) : Γ-[m + 1]-Function₂ (copyPrefix : M → M → M) :=
  copyPrefix_definable.of_sigmaOne

@[simp] theorem len_copyPrefix (word n : M) : len (copyPrefix word n) = n := by
  induction n using ISigma1.pi1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [ih]

theorem nth_copyPrefix (word n i : M) (hi : i < n) :
    nth (copyPrefix word n) i = nth word i := by
  induction n using ISigma1.pi1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ n ih =>
    have hile : i ≤ n := Arithmetic.lt_succ_iff_le.mp hi
    rcases lt_or_eq_of_le hile with hil | hieq
    · rw [copyPrefix_succ, concat_nth_lt _ _ (by simpa using hil)]
      exact ih i hil
    · subst i
      rw [copyPrefix_succ]
      exact concat_nth_len' (copyPrefix word n) (nth word n) (len_copyPrefix word n)

@[simp] theorem copyPrefix_len (word : M) : copyPrefix word (len word) = word :=
  nth_ext (by simp) (fun i hi => nth_copyPrefix word (len word) i (by simpa using hi))

theorem append_snoc (a b record : M) : Words.append a (concat b record) = concat (Words.append a b) record := by
  rw [← Words.append_singleton, ← Words.append_assoc, Words.append_singleton]

/-- A stack's words are concatenated in their original input order:
its latest top block follows the remaining tail's earlier blocks. -/
theorem childStack_word (q : RawPolynomial) (u rest : M) :
    stackWord (childStack q u rest) = Words.append (stackWord rest) (childrenWord q u) := by
  induction q generalizing u rest with
  | term => simp [childStack, childrenWord]
  | formula => simp [childStack, childrenWord]
  | coefficient C => simp [childStack, childrenWord]
  | unit => simp [childStack, childrenWord]
  | product a b ia ib =>
      simp [childStack, childrenWord, ib, ia]
  | sum a b ia ib =>
      by_cases hk : π₂ u = 0 <;> simp [childStack, childrenWord, hk, ia, ib]

/-- Every successful step consumes child blocks without losing or inventing a single node
record. -/
theorem step_word (a b : RawPolynomial) (record stack out : M)
    (h : step a b record (stack + 1) = out + 1) :
    stackWord out = concat (stackWord stack) record := by
  by_cases hk₀ : π₂ record = 0
  · rcases nil_or_adjoin (refill a (π₁ record) stack) with hz | ⟨u, rest, hu⟩
    · simp [step, hk₀, hz] at h
    · have hout : adjoin ⟪concat (childrenWord a u) record, 0⟫ rest = out :=
        by simpa [step, hk₀, hu] using h
      have hstack := (refill_sound a (π₁ record) stack u rest hu).2
      rw [← hout, ← hstack, childStack_word]
      simp [append_snoc]
  · by_cases hk₁ : π₂ record = 1
    · rcases nil_or_adjoin (refill b (π₁ record) stack) with hz | ⟨u, rest, hu⟩
      · simp [step, hk₁, hz] at h
      · have hout : adjoin ⟪concat (childrenWord b u) record, 1⟫ rest = out :=
          by simpa [step, hk₁, hu] using h
        have hstack := (refill_sound b (π₁ record) stack u rest hu).2
        rw [← hout, ← hstack, childStack_word]
        simp [append_snoc]
    · simp [step, hk₀, hk₁] at h

/-- Pi-one induction on the literal prefix length proves exact word
conservation throughout every successful parser computation. -/
theorem prefix_word (a b : RawPolynomial) (word n out : M)
    (h : runPrefix a b word n 1 = out + 1) : stackWord out = copyPrefix word n := by
  induction n using ISigma1.pi1_succ_induction generalizing out
  · definability
  case zero =>
    have ho : out = 0 := by
      have he : (0 : M) + 1 = out + 1 := by simpa using h
      exact (add_right_cancel he).symm
    simp [ho]
  case succ n ih =>
    rcases zero_or_succ (runPrefix a b word n 1) with hz | ⟨stack, hs⟩
    · simp [prefix_succ, hz] at h
    · rw [prefix_succ, hs] at h
      rw [step_word a b (nth word n) stack out h, ih stack hs, copyPrefix_succ]

theorem run_word (a b : RawPolynomial) (word out : M)
    (h : run a b word 1 = out + 1) : stackWord out = word := by
  simpa using prefix_word a b word (len word) out h

/-- The self-word equation in the carrier definition is a proved redundancy: acceptance
means precisely coefficient validity and one final tree of the requested sort, as in
the postfix parser. -/
theorem carrier_iff_singleton (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] ∧ ∃ stored : M,
        run a b word 1 = adjoin ⟪stored, if formula then 1 else 0⟫ 0 + 1 := by
  rw [carrier_eval]
  constructor
  · rintro ⟨hc, hr⟩
    exact ⟨hc, word, hr⟩
  · rintro ⟨hc, stored, hr⟩
    have hs : stored = word := by simpa using run_word a b word (adjoin ⟪stored, if formula then 1 else 0⟫ 0) hr
    subst stored
    exact ⟨hc, hr⟩

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
