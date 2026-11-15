/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveVectors

/-! # Finite-support Boolean lookup in arithmetic models -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ArithmeticFiniteLookup

/-- Output one for membership in the canonical vector and zero otherwise. -/
def graph : 𝚺₁.Semisentence 3 :=
  .mkSigma “y x l. (y = 1 ∧ !memVecDef.sigma x l) ∨
    (y = 0 ∧ ¬!memVecDef.pi x l)”

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “o x. o = 0”
  adjoin := .mkSigma “o a as ih x. (x = a ∧ o = 1) ∨ (x ≠ a ∧ o = ih)”

/-- Output, searched label, and vector, in that order. -/
def recursiveGraph : 𝚺₁.Semisentence 3 :=
  blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

section Models

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def construction : VecRec.Construction M blueprint where
  nil _ := 0
  adjoin p a _ ih := if p 0 = a then 1 else ih
  nil_defined := .mk fun v => by simp [blueprint]
  adjoin_defined := .mk fun v => by
    by_cases h : v 4 = v 1 <;> simp [blueprint, h]

def lookup (x l : M) : M := construction.result ![x] l

@[simp] theorem recursiveGraph_eval (o x l : M) :
    recursiveGraph.val.Evalb ![o, x, l] ↔ o = lookup x l := by
  simpa [recursiveGraph, lookup, Matrix.constant_eq_singleton] using
    (construction (M := M)).eval_resultDef ![o, l, x]

instance lookup_defined : 𝚺₁-Function₂ (lookup : M → M → M) via recursiveGraph :=
  .mk fun v => by
    simpa [recursiveGraph, lookup, Matrix.constant_eq_singleton] using
      (construction (M := M)).eval_resultDef ![v 0, v 2, v 1]

instance lookup_definable : 𝚺₁-Function₂ (lookup : M → M → M) :=
  lookup_defined.to_definable

instance lookup_definable' (Γ m) : Γ-[m + 1]-Function₂ (lookup : M → M → M) :=
  lookup_definable.of_sigmaOne

@[simp] theorem lookup_nil (x : M) : lookup x 0 = 0 := by
  simp [lookup, construction]

@[simp] theorem lookup_adjoin (x a l : M) :
    lookup x (adjoin a l) = if x = a then 1 else lookup x l := by
  simp [lookup, construction]

theorem lookup_one_iff (x l : M) : lookup x l = 1 ↔ MemVec x l := by
  induction l using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin a l ih =>
    by_cases h : x = a <;> simp [lookup_adjoin, memVec_adjoin_iff, h, ih]

theorem lookup_range (x l : M) : lookup x l = 0 ∨ lookup x l = 1 := by
  induction l using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin a l ih =>
    by_cases h : x = a <;> simp [lookup_adjoin, h, ih]

theorem lookup_zero_iff (x l : M) : lookup x l = 0 ↔ ¬MemVec x l := by
  constructor
  · intro h hm
    have he := h.symm.trans ((lookup_one_iff x l).mpr hm)
    exact zero_ne_one he
  · intro h
    rcases lookup_range x l with hz | ho
    · exact hz
    · exact False.elim (h ((lookup_one_iff x l).mp ho))

@[simp] theorem graph_eval (y x l : M) :
    graph.val.Evalb ![y, x, l] ↔
      (y = 1 ∧ MemVec x l) ∨ (y = 0 ∧ ¬MemVec x l) := by
  simp [graph, HierarchySymbol.Semiformula.val_sigma, memVec_defined.proper.iff']

@[simp] theorem one_iff (x l : M) :
    graph.val.Evalb ![1, x, l] ↔ MemVec x l := by
  simp [graph_eval]

@[simp] theorem zero_iff (x l : M) :
    graph.val.Evalb ![0, x, l] ↔ ¬MemVec x l := by
  simp [graph_eval]

theorem total_model (x l : M) : ∃! y : M, graph.val.Evalb ![y, x, l] := by
  by_cases h : MemVec x l
  · exact ⟨1, (one_iff x l).mpr h, by intro y hy; simpa [h] using hy⟩
  · exact ⟨0, (zero_iff x l).mpr h, by intro y hy; simpa [h] using hy⟩

theorem functional_model (x l y z : M)
    (hy : graph.val.Evalb ![y, x, l])
    (hz : graph.val.Evalb ![z, x, l]) : y = z :=
  (total_model x l).unique hy hz

theorem graph_iff_recursiveGraph (y x l : M) :
    graph.val.Evalb ![y, x, l] ↔ recursiveGraph.val.Evalb ![y, x, l] := by
  rw [graph_eval, recursiveGraph_eval]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ((lookup_one_iff x l).mpr h).symm
    · exact ((lookup_zero_iff x l).mpr h).symm
  · rintro rfl
    rcases lookup_range x l with hz | ho
    · exact Or.inr ⟨hz, (lookup_zero_iff x l).mp hz⟩
    · exact Or.inl ⟨ho, (lookup_one_iff x l).mp ho⟩

theorem negative_label_value (A B : FiniteSigmaOne.Carrier)
    (disjoint : ∀ x : M, A.val.Evalb ![x] → ¬B.val.Evalb ![x])
    (l : M) (support : (FiniteSigmaOne.allEntriesCondition A).Evalb ![l])
    (x : M) (negative : B.val.Evalb ![x]) :
    graph.val.Evalb ![0, x, l] := by
  apply (zero_iff x l).mpr
  rintro ⟨i, hi, hx⟩
  have ha := (FiniteSigmaOne.allEntriesCondition_eval A l).mp support i hi
  exact disjoint x (hx ▸ ha) negative

end Models

def totalSentence : ArithmeticSentence := “∀ x l, ∃! y, !graph.val y x l”

theorem total_PA : 𝗣𝗔 ⊢ totalSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [totalSentence] using (total_model (M := M))

def recursiveComparisonSentence : ArithmeticSentence :=
  “∀ y x l, !graph.val y x l ↔ !recursiveGraph.val y x l”

theorem recursive_comparison_PA : 𝗣𝗔 ⊢ recursiveComparisonSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [recursiveComparisonSentence] using (graph_iff_recursiveGraph (M := M))

def negativeLabelSentence (A B : FiniteSigmaOne.Carrier) : ArithmeticSentence :=
  “(∀ x, !A.val x → ¬!B.val x) →
    ∀ l, !(FiniteSigmaOne.allEntriesCondition A) l →
      ∀ x, !B.val x → !graph.val 0 x l”

theorem negative_label_PA (A B : FiniteSigmaOne.Carrier) :
    𝗣𝗔 ⊢ negativeLabelSentence A B := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [negativeLabelSentence] using (negative_label_value (M := M) A B)

theorem memVec_nat_decode (x l : ℕ) : MemVec x l ↔ x ∈ Nat.natToList l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      cases l with
      | zero => simp [Nat.natToList, MemVec]
      | succ n =>
          have hc : n + 1 = adjoin n.unpair.1 n.unpair.2 := by
            rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]
            simp
          rw [hc, memVec_adjoin_iff, SyntacticSyntax.NatVectors.natToList_adjoin]
          simp only [List.mem_cons, ih n.unpair.2
            (Nat.lt_succ_of_le (Nat.unpair_right_le n))]

theorem lookup_primrec : Primrec₂ (lookup : ℕ → ℕ → ℕ) := by
  have hn : Primrec (fun x : ℕ => (construction (M := ℕ)).nil ![x]) := Primrec.const 0
  have hs : Primrec₂ (fun (x : ℕ) (t : ℕ × List ℕ × ℕ) =>
      (construction (M := ℕ)).adjoin ![x] t.1
        (SyntacticSyntax.NatVectors.pack t.2.1) t.2.2) := by
    have h : Primrec (fun p : ℕ × (ℕ × List ℕ × ℕ) =>
        if p.1 = p.2.1 then 1 else p.2.2.2) :=
      Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.const 1) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec₂.of_eq h.to₂ fun x t => by
      by_cases hx : x = t.1 <;> simp [construction, hx]
  exact SyntacticSyntax.NatVectors.vecRec_primrec
    (construction (M := ℕ)) (fun x : ℕ => ![x]) hn hs

end CategoricalEssentialIncompleteness.V46.ArithmeticFiniteLookup
