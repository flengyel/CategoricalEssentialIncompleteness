/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticFiniteLookup
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! # Finite positive supports for the arithmetic diagonal pair -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedFiniteSupport

section Models

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem mem_append (x a b : M) :
    MemVec x (SyntacticSyntax.Words.append a b) ↔ MemVec x a ∨ MemVec x b := by
  induction a using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin y a ih =>
    simp [SyntacticSyntax.Words.append_adjoin, memVec_adjoin_iff, ih, or_assoc]

theorem all_entries_iff (A : FiniteSigmaOne.Carrier) (l : M) :
    (FiniteSigmaOne.allEntriesCondition A).Evalb ![l] ↔
      ∀ x : M, MemVec x l → A.val.Evalb ![x] := by
  rw [FiniteSigmaOne.allEntriesCondition_eval]
  constructor
  · rintro h x ⟨i, hi, hx⟩
    exact hx ▸ h i hi
  · intro h i hi
    exact h (nth l i) ⟨i, hi, rfl⟩

theorem all_entries_append (A : FiniteSigmaOne.Carrier) (a b : M) :
    (FiniteSigmaOne.allEntriesCondition A).Evalb ![SyntacticSyntax.Words.append a b] ↔
      (FiniteSigmaOne.allEntriesCondition A).Evalb ![a] ∧
        (FiniteSigmaOne.allEntriesCondition A).Evalb ![b] := by
  simp only [all_entries_iff, mem_append]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨ha, hb⟩ x (hx | hx)
    · exact ha x hx
    · exact hb x hx

theorem positive_from_left (x a b : M) (h : MemVec x a) :
    ArithmeticFiniteLookup.graph.val.Evalb ![1, x, SyntacticSyntax.Words.append a b] :=
  (ArithmeticFiniteLookup.one_iff _ _).mpr ((mem_append x a b).mpr (Or.inl h))

theorem positive_from_right (x a b : M) (h : MemVec x b) :
    ArithmeticFiniteLookup.graph.val.Evalb ![1, x, SyntacticSyntax.Words.append a b] :=
  (ArithmeticFiniteLookup.one_iff _ _).mpr ((mem_append x a b).mpr (Or.inr h))

theorem negative_value (l : M)
    (support : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![l])
    (x : M) (negative : ArithmeticDiagonalCodes.beta.val.Evalb ![x]) :
    ArithmeticFiniteLookup.graph.val.Evalb ![0, x, l] :=
  ArithmeticFiniteLookup.negative_label_value ArithmeticDiagonalCodes.alpha
    ArithmeticDiagonalCodes.beta
    (fun y ha hb => ArithmeticDiagonalCodes.output_disjoint y ⟨ha, hb⟩)
    l support x negative

theorem negative_on_combined_support (a b : M)
    (ha : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![a])
    (hb : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![b])
    (x : M) (hx : ArithmeticDiagonalCodes.beta.val.Evalb ![x]) :
    ArithmeticFiniteLookup.graph.val.Evalb ![0, x, SyntacticSyntax.Words.append a b] :=
  negative_value _ ((all_entries_append ArithmeticDiagonalCodes.alpha a b).mpr ⟨ha, hb⟩) x hx

end Models

def negativeSentence : ArithmeticSentence :=
  “∀ l, !(FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha) l →
    ∀ x, !ArithmeticDiagonalCodes.beta.val x → !ArithmeticFiniteLookup.graph.val 0 x l”

theorem negative_PA : 𝗣𝗔 ⊢ negativeSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [negativeSentence] using (negative_value (M := M))

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedFiniteSupport
