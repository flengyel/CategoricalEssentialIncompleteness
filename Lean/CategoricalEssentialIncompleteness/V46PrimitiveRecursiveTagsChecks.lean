/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PrimitiveRecursiveTags

/-! # Primitive-recursive representation and tagged membership statements -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.PrimitiveRecursiveTags

namespace CategoricalEssentialIncompleteness.V46.PrimitiveRecursiveTags.StatementChecks

example {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ (A : Graph) (P : 𝚷₁.Semisentence 2),
      (𝗣𝗔 ⊢ totalSentence A) ∧ (𝗣𝗔 ⊢ piTotalSentence P) ∧
      (𝗣𝗔 ⊢ graphAgreementSentence A P) ∧
      ∀ x y : ℕ, (A.val.Evalb ![y, x] ↔ y = f x) ∧
        (P.val.Evalb ![y, x] ↔ y = f x) :=
  natPrimrec_representation hf

example {f : ℕ → ℕ} (hf : _root_.Primrec f) :
    ∃ (A : Graph) (P : 𝚷₁.Semisentence 2),
      (𝗣𝗔 ⊢ totalSentence A) ∧ (𝗣𝗔 ⊢ piTotalSentence P) ∧
      (𝗣𝗔 ⊢ graphAgreementSentence A P) ∧
      ∀ x y : ℕ, (A.val.Evalb ![y, x] ↔ y = f x) ∧
        (P.val.Evalb ![y, x] ↔ y = f x) :=
  primrec_representation hf

example {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : Code) (x : M) : ∃! y : M, c.graph.val.Evalb ![y, x] :=
  c.graph_existsUnique x

example {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : Code) (x : M) : ∃! y : M, (deltaGraph c).pi.val.Evalb ![y, x] := by
  simp only [deltaGraph_pi_eval]
  exact ⟨_, rfl, fun _ h => h⟩

example {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c d : Code) (z n : M) :
    interpret (.prec c d) ⟪z, n + 1⟫ =
      interpret d ⟪z, ⟪n, interpret (.prec c d) ⟪z, n⟫⟫⟫ :=
  interpret_prec_succ c d z n

example {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ) :
    𝗣𝗔 ⊢ tagCoherentSentence hf j := tag_coherent_PA hf j

example {f : ℕ → ℕ} (hf : _root_.Primrec f) (j x : ℕ) :
    (primrecTagPi hf j).val.Evalb ![x] ↔ f x = j := primrecTagPi_nat hf j x

example {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.Carrier) :
    𝗣𝗔 ⊢ CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.finiteMembershipSentence
      (selectedCondition hf C) := selected_membership_PA hf C

example {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (selectedList hf C).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin k,
        ORingStructure.numeral j.val = interpret (codeFor hf) (nth a i) ∧
          (C j).val.Evalb ![nth a i] := selectedList_eval hf C a

example {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.Carrier) (a : ℕ) :
    (selectedList hf C).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin k,
        j.val = f (nth a i) ∧ (C j).val.Evalb ![nth a i] := by
  simpa only [interpret_nat, codeFor_spec, Nat.numeral_eq] using selectedList_eval hf C a

end CategoricalEssentialIncompleteness.V46.PrimitiveRecursiveTags.StatementChecks
