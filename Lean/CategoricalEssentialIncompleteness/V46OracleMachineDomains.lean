/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedTuring
public import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable

/-! # Oracle transition programs and finite-prefix semidecision programs -/

@[expose] public section

noncomputable section
open Encodable Denumerable
open Nat.Partrec (Code)
open CategoricalEssentialIncompleteness.V46.Miller
namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

/-- The binary name recording membership in an arbitrary oracle. -/
def bits (A : Set ℕ) : Bits := by
  classical
  exact fun i => if i ∈ A then 1 else 0

theorem numericalPrefix_bits (A : Set ℕ) (k : ℕ) :
    OracleProgram.numericalPrefix (bits A) k = oraclePrefix A k := by
  classical
  apply List.ext_getElem
  · simp
  · intro i hi _
    by_cases ha : i ∈ A <;>
      simp [OracleProgram.numericalPrefix, bitPrefix, oraclePrefix, bits, answer, ha]

/-- A machine reads individual oracle bits and halts in a state containing its output. -/
def machineDomain (A : Set ℕ) (e x : ℕ) : Prop :=
  (OracleProgram.numberedEval e (bits A) x).Dom

/-- Specialization changes the input to the program and leaves its oracle unchanged. -/
theorem machine_section (A : Set ℕ) (e z x : ℕ) :
    machineDomain A (sectionIndex e z) x ↔ machineDomain A e (Nat.pair z x) := by
  change (OracleProgram.numberedEval (OracleProgram.specializationIndex e z) (bits A) x).Dom ↔ _
  rw [OracleProgram.specializationIndex_eval]
  rfl

/-- Simulate a transition program against the finite oracle table. A single ordinary
compiler works for all oracles and all numerical inputs. -/
theorem exists_prefix_compiler :
    ∃ tr : ℕ → ℕ, Computable tr ∧ ∀ A e x, oracleDomain A (tr e) x ↔ machineDomain A e x := by
  let F (p : ℕ × (ℕ × List ℕ)) :=
    OracleProgram.finiteEval (ofNat Code p.1) p.2.2 p.2.1
  have hF : Partrec F := OracleProgram.finiteEval_partrec.comp (Computable.pair
    (Computable.pair ((Computable.ofNat Code).comp Computable.fst) (Computable.snd.comp Computable.snd))
    (Computable.fst.comp Computable.snd))
  obtain ⟨c, hc⟩ := predicate_code hF.dom_re
  refine ⟨fun e => encode (c.curry e), Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.id), ?_⟩
  intro A e x
  rw [machineDomain, OracleProgram.numberedEval, OracleProgram.eval_domain]
  unfold oracleDomain
  apply exists_congr
  intro k
  rw [numericalPrefix_bits, ofNat_encode, Code.eval_curry]
  exact hc (e, (x, oraclePrefix A k))

/-- Dovetail the finite-prefix tests, returning zero on every accepting prefix. -/
theorem exists_machine_compiler :
    ∃ tr : ℕ → ℕ, Computable tr ∧ ∀ A e x, machineDomain A (tr e) x ↔ oracleDomain A e x := by
  let F (p : List ℕ × ℕ) :=
    ((ofNat Code p.2.unpair.1).eval (Nat.pair p.2.unpair.2 (encode p.1))).map (fun _ => 0)
  have hpair := Computable.unpair.comp (Computable.snd (α := List ℕ) (β := ℕ))
  have heval := Code.eval_part.comp ((Computable.ofNat Code).comp (Computable.fst.comp hpair))
    (Primrec₂.natPair.to_comp.comp (Computable.snd.comp hpair) (Computable.encode.comp Computable.fst))
  have hF : Partrec F := heval.map (Computable.const (0 : ℕ)).to₂
  let d := encode (OracleProgram.ofTable F hF)
  refine ⟨OracleProgram.specializationIndex d,
    OracleProgram.specializationIndex_computable.comp (Computable.const d) Computable.id, ?_⟩
  intro A e x
  rw [machineDomain, OracleProgram.specializationIndex_eval, OracleProgram.numberedEval_encode]
  have onlyZero (l : List ℕ) (y : ℕ) (hy : y ∈ F (l, Nat.pair e x)) : y = 0 := by
    obtain ⟨_, _, h⟩ := (Part.mem_map_iff _).mp hy
    exact h.symm
  simp only [Part.dom_iff_mem, OracleProgram.ofTable_graph_at F hF (bits A) (Nat.pair e x)
    (fun i j a b ha hb => (onlyZero _ _ ha).trans (onlyZero _ _ hb).symm)]
  unfold oracleDomain
  simp only [F, Nat.unpair_pair, numericalPrefix_bits, Part.mem_map_iff, Part.dom_iff_mem]
  constructor
  · rintro ⟨_, k, y, hy, _⟩
    exact ⟨k, y, hy⟩
  · rintro ⟨k, y, hy⟩
    exact ⟨0, k, y, hy, rfl⟩

/-- One transition program recognizes the entire relation. Its ordinary computable
specializations recognize all sections at the same oracle. -/
theorem machine_specialization (A : Set ℕ) {p : ℕ → Prop} (hp : FiniteOracleRE A p) :
    ∃ d, (∀ x, machineDomain A d x ↔ p x) ∧
      ∀ z x, machineDomain A (sectionIndex d z) x ↔ p (Nat.pair z x) := by
  obtain ⟨e, he⟩ := oracleDomain_surjective A hp
  obtain ⟨tr, _, htr⟩ := exists_machine_compiler
  have h (x : ℕ) := (htr A e x).trans (he x)
  exact ⟨tr e, h, fun z x => (machine_section A (tr e) z x).trans (h _)⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
