/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCoverEffective
public import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable

/-! # One oracle program for unanimity over all binary representations -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity

theorem unanimous_unique (z : Point) (a : Input) (m m' : ℕ)
    (hm : Unanimous z a m) (hm' : Unanimous z a m') : m = m' := by
  obtain ⟨q,hq⟩ := representations_nonempty z
  exact Part.mem_unique (hm q hq) (hm' q hq)

/-- The manuscript's partial function, with its literal all-representation
halting condition. Its domain is not replaced by a total switch. -/
def tau (z : Point) (e n : ℕ) : Part ℕ :=
  ⟨∃ m, Unanimous z (e,n) m, fun h => Classical.choose h⟩

theorem tau_graph (z : Point) (e n m : ℕ) :
    m ∈ tau z e n ↔ ∀ q ∈ representations z,
      m ∈ OracleProgram.numberedEval e q n := by
  change (∃ h : ∃ m', Unanimous z (e,n) m', Classical.choose h = m) ↔ Unanimous z (e,n) m
  constructor
  · rintro ⟨h,rfl⟩
    exact Classical.choose_spec h
  · intro hm
    let h : ∃ m', Unanimous z (e,n) m' := ⟨m,hm⟩
    exact ⟨h,unanimous_unique z (e,n) _ m (Classical.choose_spec h) hm⟩

/-- The ordinary numerical index is chosen BEFORE z, its representation,
and the numerical inputs. Both implications are proved from the actual
finite-cover semidecision and the concrete uniform oracle compiler. -/
theorem exists_program_graph :
    ∃ d : ℕ, ∀ z : Point, ∀ p : Bits, p ∈ representations z → ∀ e n m : ℕ,
      m ∈ OracleProgram.numberedEval d p (Nat.pair e n) ↔ Unanimous z (e,n) m := by
  obtain ⟨F,hF,hM,hFg⟩ := table_program
  obtain ⟨d,hd⟩ := OracleProgram.exists_uniform_index F hF hM
  refine ⟨d,?_⟩
  intro z p hp e n m
  calc
    m ∈ OracleProgram.numberedEval d p (Nat.pair e n) ↔
        ∃ k, m ∈ F (OracleProgram.numericalPrefix p k,Nat.pair e n) := hd p (Nat.pair e n) m
    _ ↔ ∃ k, Certified (bitPrefix p k) (e,n) m := by
      simp only [hFg,OracleProgram.numericalPrefix,normalizeWord_numericalPrefix,Nat.unpair_pair]
    _ ↔ Unanimous z (e,n) m := by rw [search_correct,hp]

def unanimityIndex : ℕ := Classical.choose exists_program_graph

theorem unanimityIndex_graph (z : Point) (p : Bits) (hp : p ∈ representations z)
    (e n m : ℕ) :
    m ∈ OracleProgram.numberedEval unanimityIndex p (Nat.pair e n) ↔
      ∀ q ∈ representations z, m ∈ OracleProgram.numberedEval e q n :=
  Classical.choose_spec exists_program_graph z p hp e n m

theorem unanimityIndex_eq_tau (z : Point) (p : Bits) (hp : p ∈ representations z)
    (e n : ℕ) : OracleProgram.numberedEval unanimityIndex p (Nat.pair e n) = tau z e n := by
  apply Part.ext
  intro m
  exact (unanimityIndex_graph z p hp e n m).trans (tau_graph z e n m).symm

theorem unanimityIndex_domain (z : Point) (p : Bits) (hp : p ∈ representations z)
    (e n : ℕ) :
    (OracleProgram.numberedEval unanimityIndex p (Nat.pair e n)).Dom ↔
      ∃ m, ∀ q ∈ representations z, m ∈ OracleProgram.numberedEval e q n := by
  rw [unanimityIndex_eq_tau z p hp e n]
  rfl

theorem representation_independent (z : Point) (p q : Bits)
    (hp : p ∈ representations z) (hq : q ∈ representations z) (e n : ℕ) :
    OracleProgram.numberedEval unanimityIndex p (Nat.pair e n) =
      OracleProgram.numberedEval unanimityIndex q (Nat.pair e n) := by
  rw [unanimityIndex_eq_tau z p hp e n,unanimityIndex_eq_tau z q hq e n]

/-- Lemma8.1 with its complete domain-and-value quantifiers. -/
theorem printed_unanimity :
    ∃ d : ℕ, ∀ z : ℕ → Set.Icc (0 : ℝ) 1,
      ∀ p : ℕ → Fin 2, rho p = z → ∀ e n : ℕ,
        OracleProgram.numberedEval d p (Nat.pair e n) = tau z e n :=
  ⟨unanimityIndex,fun z p hp e n => unanimityIndex_eq_tau z p hp e n⟩

end CategoricalEssentialIncompleteness.V46.Miller.Unanimity
