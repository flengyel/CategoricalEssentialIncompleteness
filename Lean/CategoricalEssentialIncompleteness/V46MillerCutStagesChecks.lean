/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutStages


/-! # Effective finite halting stages for the Miller diagonal -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example : Primrec (fun a : (ℕ × ℕ) × (ℕ × ℕ) =>
    Cut.boundedWords a.1.1 a.1.2 a.2.1 a.2.2) := Cut.boundedWords_primrec
example (e m : ℕ) (s : Word) :
    Unanimity.HaltsOn (e,e) m s ↔ ∃ t, s ∈ Cut.stageWords e m t :=
  ⟨Cut.stageWords_complete e m s,fun ⟨t,ht⟩ => Cut.stageWords_sound e m t s ht⟩
example (e m : ℕ) : Monotone (Cut.haltingStage e m) := fun _ _ h => Cut.haltingStage_mono e m h
example (e m t : ℕ) : IsOpen (Cut.haltingStage e m t) ∧ IsClosed (Cut.haltingStage e m t) :=
  ⟨Cut.haltingStage_isOpen e m t,Cut.haltingStage_isClosed e m t⟩
example (e m : ℕ) (p : Bits) :
    p ∈ ⋃ t, Cut.haltingStage e m t ↔ m ∈ OracleProgram.numberedEval e p e :=
  Cut.mem_halting_union e m p
