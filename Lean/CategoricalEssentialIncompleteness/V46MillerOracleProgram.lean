/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerBinaryCore
public import CategoricalEssentialIncompleteness.OracleApproximationSearch

/-! # A single indexed finite-query oracle interpreter

An index is ordinary partial-recursive transition code. A transition returns
`pair 0 y` to halt with `y`, or `pair (k+1) c` to query bit `k` and continue
at state `pair c bit`. Numerical input is held fixed across transitions.
Every index therefore describes a deterministic oracle program, without a
coherence condition on the index. Finite-table evaluation uses the very same
transition code and blocks when a requested bit is absent.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
namespace CategoricalEssentialIncompleteness.V46.Miller.OracleProgram

abbrev Code := Nat.Partrec.Code
abbrev Oracle := ℕ → Part ℕ

def execute (o : Oracle) (z : ℕ) : Part (ℕ ⊕ ℕ) :=
  (Nat.unpair z).1.casesOn (Part.some (.inl (Nat.unpair z).2))
    (fun k => (o k).map (fun b => .inr (Nat.pair (Nat.unpair z).2 b)))

def step (e : Code) (o : Oracle) (n s : ℕ) : Part (ℕ ⊕ ℕ) :=
  (e.eval (Nat.pair n s)).bind (execute o)

def run (e : Code) (o : Oracle) (n s : ℕ) : Part ℕ := PFun.fix (step e o n) s

def oracle (p : Bits) : Oracle := fun k => Part.some (p k).val

def eval (e : Code) (p : Bits) (n : ℕ) : Part ℕ := run e (oracle p) n 0

def tableOracle (l : List ℕ) : Oracle := fun k => ↑(l[k]?)

def finiteEval (e : Code) (l : List ℕ) (n : ℕ) : Part ℕ := run e (tableOracle l) n 0

def numericalPrefix (p : Bits) (k : ℕ) : List ℕ := (bitPrefix p k).map Fin.val

@[simp] theorem numericalPrefix_length (p : Bits) (k : ℕ) :
    (numericalPrefix p k).length = k := by simp [numericalPrefix]

theorem numericalPrefix_take (p : Bits) (n k : ℕ) :
    (numericalPrefix p n).take k = numericalPrefix p (min k n) := by
  simp only [numericalPrefix, ← List.map_take, prefix_take]

theorem numericalPrefix_le (p : Bits) {n k : ℕ} (h : n ≤ k) :
    numericalPrefix p n <+: numericalPrefix p k := by
  refine ⟨(numericalPrefix p k).drop n, ?_⟩
  rw [← show (numericalPrefix p k).take n = numericalPrefix p n by
    rw [numericalPrefix_take, Nat.min_eq_left h]]
  exact List.take_append_drop _ _

@[simp] theorem numericalPrefix_getElem? (p : Bits) (k i : ℕ) (hi : i < k) :
    (numericalPrefix p k)[i]? = some (p i).val := by
  simp [numericalPrefix, hi, prefix_getElem]

theorem tableOracle_mono {l l' : List ℕ} (h : l <+: l') (k b : ℕ) :
    b ∈ tableOracle l k → b ∈ tableOracle l' k := by
  rcases h with ⟨t,rfl⟩
  intro hb
  have he : l[k]? = some b := by simpa [tableOracle] using hb
  have hk : k < l.length := (List.getElem?_eq_some_iff.mp he).1
  simpa only [tableOracle, List.getElem?_append_left hk] using hb

theorem tableOracle_prefix (p : Bits) (k i b : ℕ) :
    b ∈ tableOracle (numericalPrefix p k) i → b ∈ oracle p i := by
  intro hb
  have he : (numericalPrefix p k)[i]? = some b := by simpa [tableOracle] using hb
  have hi : i < k := by
    simpa only [numericalPrefix_length] using (List.getElem?_eq_some_iff.mp he).1
  rw [numericalPrefix_getElem? p k i hi] at he
  exact Part.mem_some_iff.mpr (Option.some.inj he).symm

theorem execute_mono {o o' : Oracle}
    (h : ∀ k b, b ∈ o k → b ∈ o' k) (z : ℕ) (v : ℕ ⊕ ℕ) :
    v ∈ execute o z → v ∈ execute o' z := by
  unfold execute
  cases (Nat.unpair z).1 with
  | zero => exact id
  | succ k =>
    intro hv
    obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hv
    exact (Part.mem_map_iff _).mpr ⟨b,h k b hb,rfl⟩

theorem step_mono {o o' : Oracle} (h : ∀ k b, b ∈ o k → b ∈ o' k)
    (e : Code) (n s : ℕ) (v : ℕ ⊕ ℕ) :
    v ∈ step e o n s → v ∈ step e o' n s := by
  intro hv
  obtain ⟨z,hz,hv⟩ := Part.mem_bind_iff.mp hv
  exact Part.mem_bind_iff.mpr ⟨z,hz,execute_mono h z v hv⟩

theorem fix_mono {f g : ℕ → Part (ℕ ⊕ ℕ)}
    (h : ∀ s v, v ∈ f s → v ∈ g s) {s y : ℕ} (hy : y ∈ PFun.fix f s) :
    y ∈ PFun.fix g s := by
  exact PFun.fixInduction' (C := fun t => y ∈ PFun.fix g t) hy
    (fun t ht => PFun.fix_stop (h t (.inl y) ht))
    (fun t t' _ ht ih => PFun.mem_fix_iff.mpr (.inr ⟨t',h t (.inr t') ht,ih⟩))

theorem run_mono {o o' : Oracle} (h : ∀ k b, b ∈ o k → b ∈ o' k)
    (e : Code) (n s y : ℕ) : y ∈ run e o n s → y ∈ run e o' n s :=
  fix_mono (step_mono h e n)

theorem finiteEval_mono (e : Code) {l l' : List ℕ} (h : l <+: l') (n y : ℕ) :
    y ∈ finiteEval e l n → y ∈ finiteEval e l' n :=
  run_mono (tableOracle_mono h) e n 0 y

theorem finiteEval_sound (e : Code) (p : Bits) (k n y : ℕ) :
    y ∈ finiteEval e (numericalPrefix p k) n → y ∈ eval e p n :=
  run_mono (tableOracle_prefix p k) e n 0 y

theorem step_finite (e : Code) (p : Bits) (n s : ℕ) (v : ℕ ⊕ ℕ)
    (hv : v ∈ step e (oracle p) n s) :
    ∃ k, v ∈ step e (tableOracle (numericalPrefix p k)) n s := by
  obtain ⟨z,hz,hv⟩ := Part.mem_bind_iff.mp hv
  unfold execute at hv
  cases htag : (Nat.unpair z).1 with
  | zero =>
    rw [htag] at hv
    change v ∈ Part.some (.inl (Nat.unpair z).2) at hv
    refine ⟨0,Part.mem_bind_iff.mpr ⟨z,hz,?_⟩⟩
    rw [execute,htag]
    exact hv
  | succ i =>
    rw [htag] at hv
    change v ∈ (oracle p i).map (fun b => Sum.inr (Nat.pair (Nat.unpair z).2 b)) at hv
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hv
    have hb' : b ∈ tableOracle (numericalPrefix p (i+1)) i := by
      simpa only [tableOracle,numericalPrefix_getElem? p (i+1) i (by omega),
        Part.coe_some,oracle] using hb
    refine ⟨i+1,Part.mem_bind_iff.mpr ⟨z,hz,?_⟩⟩
    rw [execute,htag]
    exact (Part.mem_map_iff _).mpr ⟨b,hb',he⟩

theorem run_finite (e : Code) (p : Bits) (n s y : ℕ)
    (hy : y ∈ run e (oracle p) n s) :
    ∃ k, y ∈ run e (tableOracle (numericalPrefix p k)) n s := by
  refine PFun.fixInduction' (C := fun s =>
    ∃ k, y ∈ run e (tableOracle (numericalPrefix p k)) n s) hy ?_ ?_
  · intro s hs
    obtain ⟨k,hk⟩ := step_finite e p n s (.inl y) hs
    exact ⟨k,PFun.fix_stop hk⟩
  · intro s s' _ hs ih
    obtain ⟨k,hk⟩ := step_finite e p n s (.inr s') hs
    obtain ⟨l,hl⟩ := ih
    refine ⟨max k l,PFun.mem_fix_iff.mpr (.inr ⟨s',?_,?_⟩)⟩
    · exact step_mono (tableOracle_mono (numericalPrefix_le p (le_max_left k l))) e n s _ hk
    · exact run_mono (tableOracle_mono (numericalPrefix_le p (le_max_right k l))) e n s' y hl

/-- Every finite halting computation uses a finite oracle prefix, uniformly
for the SAME ordinary transition index. -/
theorem eval_graph (e : Code) (p : Bits) (n y : ℕ) :
    y ∈ eval e p n ↔ ∃ k, y ∈ finiteEval e (numericalPrefix p k) n :=
  ⟨run_finite e p n 0 y, fun ⟨k,hk⟩ => finiteEval_sound e p k n y hk⟩

theorem eval_domain (e : Code) (p : Bits) (n : ℕ) :
    (eval e p n).Dom ↔ ∃ k, (finiteEval e (numericalPrefix p k) n).Dom := by
  simp only [Part.dom_iff_mem,eval_graph]
  exact exists_comm

/-- Distinct outputs from compatible oracle tables are impossible. -/
theorem finiteEval_compatible (e : Code) (l l' : List ℕ) (h : l <+: l')
    (n y y' : ℕ) (hy : y ∈ finiteEval e l n) (hy' : y' ∈ finiteEval e l' n) :
    y = y' := Part.mem_unique (finiteEval_mono e h n y hy) hy'

end CategoricalEssentialIncompleteness.V46.Miller.OracleProgram
