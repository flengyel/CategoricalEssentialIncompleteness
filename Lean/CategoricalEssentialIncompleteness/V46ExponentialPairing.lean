/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import Foundation.FirstOrder.Arithmetic.Exponential

/-! # The exponential product pairing in every PA model -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ExponentialPairing

/-- The output code plus one is a power of two times an odd number. -/
def graph : 𝚺₁.Semisentence 3 :=
  let E := expDef
  .mkSigma “n a b. ∃ p, !E.val p a ∧ n + 1 = p * (2 * b + 1)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem exp_add (a b : M) : Exp.exp (a + b) = Exp.exp a * Exp.exp b :=
  Arithmetic.exp_of_exponential (Exponential.add_mul
    (Arithmetic.exponential_exp a) (Arithmetic.exponential_exp b))

/-- Internal arithmetic induction factors every positive number,
including nonstandard numbers, into a power of two and an odd number. -/
theorem odd_factor_exists (n : M) (hn : 0 < n) :
    ∃ a b : M, n = Exp.exp a * (2 * b + 1) := by
  have hh : ∀ z : M, 0 < z → ∃ a b : M, z = Exp.exp a * (2 * b + 1) := by
    intro z
    induction z using ISigma1.sigma1_order_induction
    · definability
    case ind z ih =>
      intro hz
      rcases Arithmetic.mod_two z with heven | hodd
      · have he : 2 * (z / 2) = z := by
          simpa [heven] using Arithmetic.div_add_mod z 2
        have hq : 0 < z / 2 := by
          apply pos_iff_ne_zero.mpr
          intro hzero
          have hz0 : z = 0 := by simpa [hzero] using he.symm
          exact (ne_of_gt hz) hz0
        obtain ⟨a, b, hab⟩ := ih (z / 2)
          (Arithmetic.div_lt_of_pos_of_one_lt hz (by simp)) hq
        refine ⟨a + 1, b, ?_⟩
        calc
          z = 2 * (z / 2) := he.symm
          _ = 2 * (Exp.exp a * (2 * b + 1)) := by rw [hab]
          _ = Exp.exp (a + 1) * (2 * b + 1) := by
            rw [Arithmetic.exp_succ, mul_assoc]
      · refine ⟨0, z / 2, ?_⟩
        simpa [hodd] using (Arithmetic.div_add_mod z 2).symm
  exact hh n hn

theorem odd_factor_lt_impossible (a b c d : M) (hac : a < c)
    (h : Exp.exp a * (2 * b + 1) = Exp.exp c * (2 * d + 1)) : False := by
  obtain ⟨k, hk⟩ := exists_add_of_le (Arithmetic.succ_le_iff_lt.mpr hac)
  have he : Exp.exp a * (2 * b + 1) =
      Exp.exp a * (2 * (Exp.exp k * (2 * d + 1))) := by
    simpa [hk, exp_add, Arithmetic.exp_succ, mul_assoc, mul_left_comm, mul_comm] using h
  have ho : 2 * b + 1 = 2 * (Exp.exp k * (2 * d + 1)) :=
    mul_left_cancel₀ (ne_of_gt (Arithmetic.exp_pos a)) he
  have hm := congrArg (fun z : M => z % 2) ho
  simp at hm

theorem odd_factor_injective {a b c d : M}
    (h : Exp.exp a * (2 * b + 1) = Exp.exp c * (2 * d + 1)) : a = c ∧ b = d := by
  rcases lt_trichotomy a c with ha | rfl | hc
  · exact (odd_factor_lt_impossible a b c d ha h).elim
  · have ho : 2 * b + 1 = 2 * d + 1 :=
      mul_left_cancel₀ (ne_of_gt (Arithmetic.exp_pos a)) h
    have hb : b = d := mul_left_cancel₀ (by simp : (2 : M) ≠ 0) (add_right_cancel ho)
    exact ⟨rfl, hb⟩
  · exact (odd_factor_lt_impossible c d a b hc h.symm).elim

noncomputable def code (a b : M) : M := Exp.exp a * (2 * b + 1) - 1

@[simp] theorem code_add_one (a b : M) : code a b + 1 = Exp.exp a * (2 * b + 1) := by
  have hp : 0 < Exp.exp a * (2 * b + 1) :=
    mul_pos (Arithmetic.exp_pos a) (by simp)
  simpa only [code, add_comm] using (Arithmetic.sub_spec_of_ge (pos_iff_one_le.mp hp)).symm

@[simp] theorem graph_eval (n a b : M) :
    graph.val.Evalb ![n, a, b] ↔ n = code a b := by
  have hh : graph.val.Evalb ![n, a, b] ↔ n + 1 = Exp.exp a * (2 * b + 1) := by
    simp [graph, expDef, ← Arithmetic.exponential_graph]
  rw [hh, ← code_add_one]
  exact add_right_cancel_iff

theorem code_injective {a b c d : M} (h : code a b = code c d) : a = c ∧ b = d := by
  have he := congrArg (fun n : M => n + 1) h
  simp only [code_add_one] at he
  exact odd_factor_injective he

theorem code_surjective (n : M) : ∃ a b : M, n = code a b := by
  obtain ⟨a, b, h⟩ := odd_factor_exists (n + 1) (by simp)
  exact ⟨a, b, add_right_cancel (h.trans (code_add_one a b).symm)⟩

theorem graph_existsUnique (a b : M) : ∃! n : M, graph.val.Evalb ![n, a, b] := by
  exact ⟨code a b, (graph_eval _ _ _).mpr rfl,
    fun n hn => (graph_eval n a b).mp hn⟩

theorem graph_inverse_existsUnique (n : M) :
    ∃! p : M × M, graph.val.Evalb ![n, p.1, p.2] := by
  obtain ⟨a, b, hn⟩ := code_surjective n
  refine ⟨(a, b), (graph_eval n a b).mpr hn, ?_⟩
  intro p hp
  exact Prod.ext ((code_injective (((graph_eval n p.1 p.2).mp hp).symm.trans hn)).1)
    ((code_injective (((graph_eval n p.1 p.2).mp hp).symm.trans hn)).2)

end Models

def totalSentence : ArithmeticSentence :=
  let G := graph
  “∀ a b, ∃ n, !G.val n a b ∧ ∀ m, !G.val m a b → m = n”

def inverseSentence : ArithmeticSentence :=
  let G := graph
  “∀ n, ∃ a b, !G.val n a b ∧ ∀ c d, !G.val n c d → c = a ∧ d = b”

theorem total_PA : 𝗣𝗔 ⊢ totalSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simp [totalSentence]

theorem inverse_PA : 𝗣𝗔 ⊢ inverseSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  have hh : ∀ n : M, ∃ a b : M, graph.val.Evalb ![n, a, b] ∧
      ∀ c d : M, graph.val.Evalb ![n, c, d] → c = a ∧ d = b := by
    intro n
    obtain ⟨a, b, hn⟩ := code_surjective n
    refine ⟨a, b, (graph_eval n a b).mpr hn, ?_⟩
    intro c d h
    exact code_injective (((graph_eval n c d).mp h).symm.trans hn)
  simpa [inverseSentence] using hh

end CategoricalEssentialIncompleteness.V46.ExponentialPairing
