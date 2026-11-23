/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakNativeTheories
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-! # A primitive recursive axiomatization of the signed theory -/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.Entailment Encodable
namespace Janiczak.FOL

private theorem relational_codes {k c : ℕ} :
    c ∈ Set.range (encode : L.Rel k → ℕ) ↔ (k = 2 ∧ c = 0) ∨ (k = 2 ∧ c = 1) := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r with | eq => exact Or.inl ⟨rfl,rfl⟩ | mem => exact Or.inr ⟨rfl,rfl⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨Language.Set.Rel.eq,rfl⟩
    · exact ⟨Language.Set.Rel.mem,rfl⟩

private instance : L.LORDefinable where
  func := .mkSigma “k f. 0 = 1”
  rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} := by
    constructor
    · rintro ⟨f,-⟩
      exact Empty.elim f
    · simp
  rel_iff {k c} := by simpa [models_iff] using! @relational_codes k c

/-- Craig's companion has primitive recursive axiom words and the same consequences
in Foundation's classical proof calculus. -/
theorem signed_recursively_axiomatizable {P N : Set ℕ} (hP : REPred (· ∈ P)) (hN : REPred (· ∈ N)) :
    ∃ U : Theory L, PrimrecPred (fun w : ℕ => w ∈ encode '' U) ∧
      ∀ φ : Sentence L, (U ⊢ φ ↔ theory (Signed P N) ⊢ φ) := by
  let T := theory (Signed P N)
  let _ : T.RE := ⟨((signed_axiom_words_enumerable hP hN).comp Computable.encode).of_eq
    (fun φ => by simp [T])⟩
  refine ⟨T.craig, Theory.primrecPred_craig_codes (T := T), ?_⟩
  exact fun _ => ⟨(inferInstance : T.craig ⪯ T).wk, (inferInstance : T ⪯ T.craig).wk⟩

end Janiczak.FOL
