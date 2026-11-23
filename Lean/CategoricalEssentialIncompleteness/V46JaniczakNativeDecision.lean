/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakNativeCoding
public import CategoricalEssentialIncompleteness.V46JaniczakDecision
public import CategoricalEssentialIncompleteness.V46JaniczakFOL

/-!
# Decidable syntactic theoremhood for the selected class spectrum

The decision procedure acts on all natural numbers in Foundation’s sentence coding. On the complete theory of the canonical model it recognizes exactly the codes of derivable sentences.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.NativeInput
open FFL FFL.FirstOrder FFL.FirstOrder.Language FFL.Entailment

/-- The complete first-order theory of the equivalence structure with finite
spectrum `C`, in Foundation's native sentence syntax. -/
def completeTheory (C : Set ℕ) : Theory FOL.L :=
  let M := canonical C
  let _ := FOL.model M
  {φ | Semiformula.Realize M.Carrier φ}

private theorem completeTheory_models (C : Set ℕ) :
    let M := canonical C
    let _ := M.inhabited
    let _ := FOL.model M
    M.Carrier↓[FOL.L] ⊧* completeTheory C := by
  let M := canonical C
  let _ := M.inhabited
  let _ := FOL.model M
  exact ⟨fun _ h ↦ h⟩

theorem completeTheory_consistent (C : Set ℕ) : Entailment.Consistent (completeTheory C) := by
  let M := canonical C
  let _ := M.inhabited
  let _ := FOL.model M
  let _ := completeTheory_models C
  exact FFL.FirstOrder.consistent_of_model (completeTheory C) M.Carrier

theorem completeTheory_extends {P N C : Set ℕ} (hp : P ⊆ C) (hn : Disjoint C N) :
    FOL.theory (Signed P N) ⊆ completeTheory C := by
  let M := canonical C
  let _ := M.inhabited
  let _ := FOL.model M
  have hm := FOL.translated_models M (Signed P N) (Canonical.models_signed hp hn)
  exact fun _ h ↦ hm.models _ h

theorem completeTheory_proves (C : Set ℕ) (p : Sentence FOL.L) :
    (completeTheory C ⊢ p) ↔ (canonical C).Valid (named p) := by
  let M := canonical C
  let _ := M.inhabited
  let _ := FOL.model M
  let _ := FOL.equality_in_model M
  have native (v : ℕ → M.Carrier) :
      (named p).Holds M.rel v ↔ Semiformula.Realize M.Carrier p :=
    named_correct p ![] v (fun i ↦ i.elim0)
  constructor
  · intro h v
    exact (native v).mpr (consequence_iff.mp (Theory.Proof.sound h) M.Carrier (completeTheory_models C))
  · intro h
    obtain ⟨v⟩ := M.hasValuation
    exact Entailment.by_axm ((native v).mp (h v))

/-- Test whether a natural number is a canonical Foundation sentence code. -/
noncomputable def nativeCodeTest (w : ℕ) : Bool :=
  open Classical in decide (∃ p : Sentence FOL.L, Encodable.encode p = w)

private theorem computable_nativeCodeTest : Computable nativeCodeTest := by
  classical
  exact (primrec_validWord.comp ((Primrec.const 0).pair Primrec.id)).decide.to_comp

/-- On all natural inputs the native decision procedure recognizes canonical
Gödel codes of theorems, returning false for every other word. -/
noncomputable def nativeDecision (d : ℕ → Bool) (w : ℕ) :=
  nativeCodeTest w && decideSpectrum d (namedWord (0,w))

theorem computable_nativeDecision {d : ℕ → Bool} (h : Computable d) :
    Computable (nativeDecision d) :=
  Primrec.and.to_comp.comp computable_nativeCodeTest ((computable_decideSpectrum h).comp
    (primrec_namedWord.comp ((Primrec.const 0).pair Primrec.id)).to_comp)

theorem nativeDecision_words {C : Set ℕ} {d : ℕ → Bool} (hd : ∀ i, d i = true ↔ i ∈ C) (w : ℕ) :
    nativeDecision d w = true ↔ ∃ p : Sentence FOL.L, Encodable.encode p = w ∧ completeTheory C ⊢ p := by
  classical
  simp only [nativeDecision, Bool.and_eq_true, nativeCodeTest, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,rfl⟩,hy⟩
    rw [namedWord_encode] at hy
    exact ⟨p,rfl,(completeTheory_proves C p).mpr ((decideSpectrum_correct hd _).mp hy)⟩
  · rintro ⟨p,rfl,hp⟩
    refine ⟨⟨p,rfl⟩,?_⟩
    rw [namedWord_encode]
    exact (decideSpectrum_correct hd _).mpr ((completeTheory_proves C p).mp hp)

theorem computable_completeTheory_words {C : Set ℕ} (hc : ComputablePred (· ∈ C)) :
    ComputablePred (fun w ↦ ∃ p : Sentence FOL.L, Encodable.encode p = w ∧ completeTheory C ⊢ p) := by
  obtain ⟨d,hd,h⟩ := ComputablePred.computable_iff.mp hc
  have dec (i : ℕ) : d i = true ↔ i ∈ C := Iff.of_eq (congrFun h i).symm
  exact ComputablePred.computable_iff.mpr ⟨nativeDecision d, computable_nativeDecision hd,
    funext fun w ↦ propext (nativeDecision_words dec w).symm⟩

end Janiczak.NativeInput
