/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialPairingPrimrec
public import Mathlib.Data.Nat.Find

/-! # Bounded primitive-recursive projections for exponential pairing -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ExponentialPairing

theorem code_bounds {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a b : M) :
    a ≤ code a b ∧ b ≤ code a b := by
  have ha : a < code a b + 1 := by
    rw [code_add_one]
    exact lt_of_lt_of_le (Arithmetic.lt_exp a) (Arithmetic.le_mul_of_pos_right (by simp))
  have hb : b < code a b + 1 := by
    rw [code_add_one]
    exact lt_of_lt_of_le (lt_of_le_of_lt Arithmetic.le_two_mul_left (lt_add_one _))
      (Arithmetic.le_mul_of_pos_left (Arithmetic.exp_pos a))
  exact ⟨Arithmetic.le_iff_lt_succ.mpr ha, Arithmetic.le_iff_lt_succ.mpr hb⟩

def inverseBound (n : ℕ) : ℕ := (n + 1) * (n + 1)

def inverseIndex (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => code (Nat.unpair m).1 (Nat.unpair m).2 = n) (inverseBound n)

def first (n : ℕ) : ℕ := (Nat.unpair (inverseIndex n)).1
def second (n : ℕ) : ℕ := (Nat.unpair (inverseIndex n)).2

theorem inverseIndex_spec (n : ℕ) :
    code (Nat.unpair (inverseIndex n)).1 (Nat.unpair (inverseIndex n)).2 = n := by
  obtain ⟨a, b, hn⟩ := code_surjective n
  obtain ⟨ha, hb⟩ := code_bounds a b
  rw [← hn] at ha hb
  have ha' : Nat.le a n := by
    rcases Arithmetic.le_def.mp ha with he | ht
    · exact Nat.le_of_eq he
    · exact Nat.le_of_lt ht
  have hb' : Nat.le b n := by
    rcases Arithmetic.le_def.mp hb with he | ht
    · exact Nat.le_of_eq he
    · exact Nat.le_of_lt ht
  have hm : Nat.le (Nat.pair a b) (inverseBound n) := by
    apply Nat.le_of_lt
    have hh := Nat.pair_lt_max_add_one_sq a b
    have hmax : Nat.le (max a b) n := Nat.max_le.mpr ⟨ha', hb'⟩
    have hs : Nat.le ((max a b + 1) ^ 2) ((n + 1) ^ 2) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hmax 1) 2
    simpa only [inverseBound, pow_two] using Nat.lt_of_lt_of_le hh hs
  have hp : code (Nat.unpair (Nat.pair a b)).1 (Nat.unpair (Nat.pair a b)).2 = n := by
    simpa using hn.symm
  exact Nat.findGreatest_spec
    (P := fun m => code (Nat.unpair m).1 (Nat.unpair m).2 = n) hm hp

@[simp] theorem code_first_second (n : ℕ) : code (first n) (second n) = n := inverseIndex_spec n

theorem projections_code (a b : ℕ) : first (code a b) = a ∧ second (code a b) = b :=
  code_injective (code_first_second (code a b))

@[simp] theorem first_code (a b : ℕ) : first (code a b) = a := (projections_code a b).1
@[simp] theorem second_code (a b : ℕ) : second (code a b) = b := (projections_code a b).2

theorem inverseIndex_primrec : Primrec inverseIndex := by
  have hb : Primrec inverseBound := Primrec.nat_mul.comp Primrec.succ Primrec.succ
  have hu : Primrec (fun p : ℕ × ℕ => Nat.unpair p.2) := Primrec.unpair.comp Primrec.snd
  have hp : PrimrecRel (fun n m : ℕ => code (Nat.unpair m).1 (Nat.unpair m).2 = n) :=
    Primrec.eq.comp (code_primrec.comp (Primrec.fst.comp hu) (Primrec.snd.comp hu)) Primrec.fst
  exact Primrec.nat_findGreatest hb hp

theorem first_primrec : Primrec first :=
  Primrec.fst.comp (Primrec.unpair.comp inverseIndex_primrec)

theorem second_primrec : Primrec second :=
  Primrec.snd.comp (Primrec.unpair.comp inverseIndex_primrec)


def firstGraph : 𝚺₁.Semisentence 2 :=
  let G := graph
  .mkSigma “n a. ∃ b, !G.val n a b”

def secondGraph : 𝚺₁.Semisentence 2 :=
  let G := graph
  .mkSigma “n b. ∃ a, !G.val n a b”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem firstGraph_eval (n a : M) :
    firstGraph.val.Evalb ![n, a] ↔ ∃ b : M, n = code a b := by
  simp [firstGraph]

@[simp] theorem secondGraph_eval (n b : M) :
    secondGraph.val.Evalb ![n, b] ↔ ∃ a : M, n = code a b := by
  simp [secondGraph]

theorem firstGraph_existsUnique (n : M) : ∃! a : M, firstGraph.val.Evalb ![n, a] := by
  obtain ⟨a, b, hn⟩ := code_surjective n
  refine ⟨a, (firstGraph_eval n a).mpr ⟨b, hn⟩, ?_⟩
  intro c hc
  obtain ⟨d, hd⟩ := (firstGraph_eval n c).mp hc
  exact (code_injective (hd.symm.trans hn)).1

theorem secondGraph_existsUnique (n : M) : ∃! b : M, secondGraph.val.Evalb ![n, b] := by
  obtain ⟨a, b, hn⟩ := code_surjective n
  refine ⟨b, (secondGraph_eval n b).mpr ⟨a, hn⟩, ?_⟩
  intro d hd
  obtain ⟨c, hc⟩ := (secondGraph_eval n d).mp hd
  exact (code_injective (hc.symm.trans hn)).2

theorem graph_iff_projections (n a b : M) :
    graph.val.Evalb ![n, a, b] ↔
      firstGraph.val.Evalb ![n, a] ∧ secondGraph.val.Evalb ![n, b] := by
  rw [graph_eval, firstGraph_eval, secondGraph_eval]
  constructor
  · intro hn
    exact ⟨⟨b, hn⟩, ⟨a, hn⟩⟩
  · rintro ⟨⟨d, hd⟩, ⟨c, hc⟩⟩
    have hb : d = b := (code_injective (hd.symm.trans hc)).2
    simpa only [hb] using hd

end Models

@[simp] theorem firstGraph_nat (n a : ℕ) : firstGraph.val.Evalb ![n, a] ↔ a = first n := by
  rw [firstGraph_eval]
  constructor
  · rintro ⟨b, hn⟩
    simp only [hn, first_code]
  · intro ha
    exact ⟨second n, by rw [ha, code_first_second]⟩

@[simp] theorem secondGraph_nat (n b : ℕ) : secondGraph.val.Evalb ![n, b] ↔ b = second n := by
  rw [secondGraph_eval]
  constructor
  · rintro ⟨a, hn⟩
    simp only [hn, second_code]
  · intro hb
    exact ⟨first n, by rw [hb, code_first_second]⟩

def projectionsSentence : ArithmeticSentence :=
  let G := graph
  let F := firstGraph
  let S := secondGraph
  “∀ n a b, !G.val n a b ↔ !F.val n a ∧ !S.val n b”

def projectionTotalSentence (F : 𝚺₁.Semisentence 2) : ArithmeticSentence :=
  “∀ n, ∃ a, !F.val n a ∧ ∀ b, !F.val n b → b = a”

theorem projections_PA : 𝗣𝗔 ⊢ projectionsSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [projectionsSentence] using (graph_iff_projections (M := M))

theorem first_total_PA : 𝗣𝗔 ⊢ projectionTotalSentence firstGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  have hh : ∀ n : M, ∃ a : M, firstGraph.val.Evalb ![n, a] ∧
      ∀ b : M, firstGraph.val.Evalb ![n, b] → b = a := by
    intro n
    obtain ⟨a, ha, hu⟩ := firstGraph_existsUnique n
    exact ⟨a, ha, hu⟩
  simpa [projectionTotalSentence] using hh

theorem second_total_PA : 𝗣𝗔 ⊢ projectionTotalSentence secondGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  have hh : ∀ n : M, ∃ a : M, secondGraph.val.Evalb ![n, a] ∧
      ∀ b : M, secondGraph.val.Evalb ![n, b] → b = a := by
    intro n
    obtain ⟨a, ha, hu⟩ := secondGraph_existsUnique n
    exact ⟨a, ha, hu⟩
  simpa [projectionTotalSentence] using hh

end CategoricalEssentialIncompleteness.V46.ExponentialPairing
