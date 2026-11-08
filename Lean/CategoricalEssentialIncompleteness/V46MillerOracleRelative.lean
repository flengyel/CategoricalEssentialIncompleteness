/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable
import CategoricalEssentialIncompleteness.OracleDomainRecursion

/-! # Exact pointwise comparison of oracle machines and relative recursion

The dovetail keeps oracle-prefix length and ordinary evaluator fuel separate,
and returns the computed VALUE, rather than only detecting definedness. The
reverse index is chosen for a fixed oracle. It does not assert that an
arbitrary family of relative computations has one index for all oracles.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
namespace CategoricalEssentialIncompleteness.V46.Miller.OracleRelative

open LocalConnectedness.OracleComputation
abbrev Code := Nat.Partrec.Code

/-- The characteristic-set presentation of a binary oracle. -/
def oracleSupport (p : Bits) : Set ℕ := {k | p k = 1}

@[simp] theorem answer_support (p : Bits) (k : ℕ) :
    answer (oracleSupport p) k = (p k).val := by
  by_cases h : p k = 1
  · simp [answer,oracleSupport,h]
  · have hn : (p k).val ≠ 1 := fun he => h (Fin.ext he)
    have hz : (p k).val = 0 := by have hi := (p k).isLt; omega
    simp [answer,oracleSupport,h,hz]


theorem oracleFunction_eq (p : Bits) :
    oracleFunction (oracleSupport p) = OracleProgram.oracle p := by
  funext k
  simp [oracleFunction,OracleProgram.oracle]

/-- The old characteristic-oracle prefix and the actual binary word have
identical numerical entries, including negative oracle answers. -/
theorem oraclePrefix_eq (p : Bits) (k : ℕ) :
    oraclePrefix (oracleSupport p) k = OracleProgram.numericalPrefix p k := by
  apply List.ext_getElem
  · simp [oraclePrefix,OracleProgram.numericalPrefix]
  · intro i hi hj
    simp [oraclePrefix,OracleProgram.numericalPrefix]

/-- This code expects the old domain enumerator's argument order
`(numericalInput, encodedFinitePrefix)`. -/
private def valueCode (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) : Code :=
  .comp (OracleProgram.tableCode F hF) (.pair .right .left)

private theorem valueCode_eval (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (n : ℕ) (l : List ℕ) :
    (valueCode F hF).eval (Nat.pair n (encode l)) = F (l,n) := by
  simp only [valueCode,Nat.Partrec.Code.eval,Seq.seq,PFun.coe_val,Nat.unpair_pair,
    Part.map_eq_map,Part.bind_eq_bind,Part.map_some,Part.bind_some]
  exact OracleProgram.tableCode_eval F hF (l,n)

private def trialValueCode (c : Code) (p : ℕ) : ℕ :=
  (c.evaln (trialFuel p) (trialInput p)).getD 0

private theorem trialValueCode_computable (c : Code) : Computable (trialValueCode c) := by
  have hf : Computable trialFuel := Computable.snd.comp (Computable.unpair.comp
    (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair))))
  have hi : Computable trialInput := Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair)))
    (Computable.snd.comp Computable.unpair)
  have he : Computable (fun p : ℕ => c.evaln (trialFuel p) (trialInput p)) :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (Computable.pair (Computable.pair hf (Computable.const c)) hi)
  exact (Computable.option_getD he (Computable.const 0)).of_eq (fun _ => rfl)

private def trialValue (S : Set ℕ) (c : Code) (p : ℕ) : ℕ :=
  trialValueCode c (Nat.pair p (encode (oraclePrefix S (Nat.unpair (Nat.unpair p).2).1)))

private theorem trialValue_recursiveIn (S : Set ℕ) (c : Code) :
    Nat.RecursiveIn (oracleSet S) (fun p => Part.some (trialValue S c p)) := by
  have hn : Computable (fun p : ℕ => (Nat.unpair (Nat.unpair p).2).1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  refine (Nat.RecursiveIn.comp (recursiveIn_of_computable (trialValueCode_computable c))
    (.pair (recursiveIn_of_computable Computable.id)
      (.comp (prefixCode_recursiveIn S) (recursiveIn_of_computable hn)))).of_eq ?_
  intro p
  simp [trialValue,Seq.seq,Part.bind_eq_bind]

private theorem trialValue_pair (S : Set ℕ) (c : Code) (x n fuel : ℕ) :
    trialValue S c (Nat.pair x (Nat.pair n fuel)) =
      (c.evaln fuel (Nat.pair x (encode (oraclePrefix S n)))).getD 0 := by
  simp only [trialValue,trialValueCode,trialInput,trialFuel,Nat.unpair_pair]

private def searchValues (S : Set ℕ) (c : Code) (x : ℕ) : Part ℕ :=
  (numberedSemidecision S c x).bind (fun t =>
    Part.some (trialValue S c (Nat.pair x t)))

private theorem searchValues_recursiveIn (S : Set ℕ) (c : Code) :
    Nat.RecursiveIn (oracleSet S) (searchValues S c) := by
  have hstage := numberedSemidecision_recursiveIn S c
  refine (Nat.RecursiveIn.comp (trialValue_recursiveIn S c)
    (.pair (recursiveIn_of_computable Computable.id) hstage)).of_eq ?_
  intro x
  simp [searchValues,Seq.seq,Part.bind_eq_bind,Part.bind_map]

/-- The successful dovetail stage returns an actual value of the original
ordinary computation on the indicated finite oracle prefix. -/
private theorem successful_value (S : Set ℕ) (c : Code) (x t : ℕ)
    (ht : t ∈ numberedSemidecision S c x) :
    trialValue S c (Nat.pair x t) ∈ c.eval
      (Nat.pair x (encode (oraclePrefix S (Nat.unpair t).1))) := by
  have htest := Nat.rfind_spec ht
  have hz : trial S c (Nat.pair x t) = 0 := by simpa using htest
  have he : t = Nat.pair (Nat.unpair t).1 (Nat.unpair t).2 := (Nat.pair_unpair t).symm
  rw [he,trial_pair] at hz
  have hs : (c.evaln (Nat.unpair t).2
      (Nat.pair x (encode (oraclePrefix S (Nat.unpair t).1)))).isSome := by
    split_ifs at hz with h
    exact h
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp hs
  have hval : trialValue S c (Nat.pair x t) = y := by
    rw [he,trialValue_pair]
    rw [hy]
    rfl
  rw [hval]
  exact Nat.Partrec.Code.evaln_sound hy

private theorem searchValues_sound (S : Set ℕ) (c : Code) (x y : ℕ)
    (hy : y ∈ searchValues S c x) :
    ∃ k, y ∈ c.eval (Nat.pair x (encode (oraclePrefix S k))) := by
  obtain ⟨t,ht,hy⟩ := Part.mem_bind_iff.mp hy
  have he : y = trialValue S c (Nat.pair x t) := Part.mem_some_iff.mp hy
  exact ⟨(Nat.unpair t).1,he.symm ▸ successful_value S c x t ht⟩

private theorem searchValues_graph (S : Set ℕ) (c : Code) (x y : ℕ)
    (hcoh : ∀ i j a b,
      a ∈ c.eval (Nat.pair x (encode (oraclePrefix S i))) →
      b ∈ c.eval (Nat.pair x (encode (oraclePrefix S j))) → a=b) :
    y ∈ searchValues S c x ↔ ∃ k, y ∈ c.eval (Nat.pair x (encode (oraclePrefix S k))) := by
  constructor
  · exact searchValues_sound S c x y
  · rintro ⟨k,hk⟩
    have hd : (numberedSemidecision S c x).Dom := by
      apply (numberedSemidecision_domain S c x).mpr
      refine ⟨k,?_⟩
      rw [Denumerable.ofNat_encode]
      exact Part.dom_iff_mem.mpr ⟨y,hk⟩
    obtain ⟨t,ht⟩ := Part.dom_iff_mem.mp hd
    have hvalue := successful_value S c x t ht
    have he := hcoh (Nat.unpair t).1 k (trialValue S c (Nat.pair x t)) y hvalue hk
    exact Part.mem_bind_iff.mpr ⟨t,ht,Part.mem_some_iff.mpr he.symm⟩

/-- Value-complete converse of the finite-query approximation theorem.
The least successful search stage is an actual relative recursive
computation, with the same values and the same undefined inputs as `f`. -/
theorem hasApproximation_recursiveIn {S : Set ℕ} {f : ℕ → Part ℕ}
    (hf : HasApproximation S f) : Nat.RecursiveIn (oracleSet S) f := by
  obtain ⟨F,hF,hM,hf⟩ := hf
  let c := valueCode F hF
  have hcoh (x : ℕ) : ∀ i j a b,
      a ∈ c.eval (Nat.pair x (encode (oraclePrefix S i))) →
      b ∈ c.eval (Nat.pair x (encode (oraclePrefix S j))) → a=b := by
    intro i j a b ha hb
    have ha' : a ∈ F (oraclePrefix S i,x) :=
      Eq.mp (congrArg (fun v : Part ℕ => a ∈ v) (valueCode_eval F hF x _)) ha
    have hb' : b ∈ F (oraclePrefix S j,x) :=
      Eq.mp (congrArg (fun v : Part ℕ => b ∈ v) (valueCode_eval F hF x _)) hb
    exact Part.mem_unique
      (hM _ _ (prefix_le S (le_max_left i j)) x a ha')
      (hM _ _ (prefix_le S (le_max_right i j)) x b hb')
  apply (searchValues_recursiveIn S c).of_eq
  intro x
  apply Part.ext
  intro y
  have h := searchValues_graph S c x y (hcoh x)
  have hc : (∃ k, y ∈ c.eval (Nat.pair x (encode (oraclePrefix S k)))) ↔
      ∃ k, y ∈ F (oraclePrefix S k,x) :=
    exists_congr (fun k => Iff.of_eq (congrArg (fun v : Part ℕ => y ∈ v)
      (valueCode_eval F hF x (oraclePrefix S k))))
  exact h.trans (hc.trans (hf x y).symm)

theorem hasApproximation_iff_recursiveIn (S : Set ℕ) (f : ℕ → Part ℕ) :
    HasApproximation S f ↔ Nat.RecursiveIn (oracleSet S) f :=
  ⟨hasApproximation_recursiveIn,recursiveIn_hasApproximation⟩

/-- Every actual finite-query machine has the SAME value graph as a relative
recursive function at the fixed binary oracle. -/
theorem eval_hasApproximation (e : Code) (p : Bits) :
    HasApproximation (oracleSupport p) (OracleProgram.eval e p) := by
  have hinput : Computable (fun a : List ℕ × ℕ => ((e,a.1),a.2)) :=
    Computable.pair (Computable.pair (Computable.const e) Computable.fst) Computable.snd
  have hF : Partrec (fun a : List ℕ × ℕ => OracleProgram.finiteEval e a.1 a.2) :=
    (OracleProgram.finiteEval_partrec.comp hinput).of_eq (fun _ => rfl)
  refine ⟨(fun a => OracleProgram.finiteEval e a.1 a.2),hF,?_,?_⟩
  · intro l l' hl n y hy
    exact OracleProgram.finiteEval_mono e hl n y hy
  · intro n y
    exact (OracleProgram.eval_graph e p n y).trans (exists_congr (fun k =>
      Iff.of_eq (congrArg (fun l : List ℕ => y ∈ OracleProgram.finiteEval e l n)
        (oraclePrefix_eq p k).symm)))

theorem eval_recursiveIn (e : Code) (p : Bits) :
    Nat.RecursiveIn (oracleSet (oracleSupport p)) (OracleProgram.eval e p) :=
  hasApproximation_recursiveIn (eval_hasApproximation e p)

theorem numberedEval_recursiveIn (e : ℕ) (p : Bits) :
    Nat.RecursiveIn (oracleSet (oracleSupport p)) (OracleProgram.numberedEval e p) :=
  eval_recursiveIn (Denumerable.ofNat Code e) p

/-- The converse is POINTWISE in `p`. Its index may depend on this fixed
oracle and its relative-recursion proof. -/
theorem exists_index_of_recursiveIn (p : Bits) (f : ℕ → Part ℕ)
    (hf : Nat.RecursiveIn (oracleSet (oracleSupport p)) f) :
    ∃ e : ℕ, ∀ n, OracleProgram.numberedEval e p n = f n := by
  obtain ⟨F,hF,hM,hrep⟩ := recursiveIn_hasApproximation hf
  obtain ⟨e,he⟩ := OracleProgram.exists_uniform_index F hF hM
  refine ⟨e,fun n => Part.ext (fun y => ?_)⟩
  have h := he p n y
  have hc : (∃ k, y ∈ F (OracleProgram.numericalPrefix p k,n)) ↔
      ∃ k, y ∈ F (oraclePrefix (oracleSupport p) k,n) :=
    exists_congr (fun k => Iff.of_eq (congrArg (fun l : List ℕ => y ∈ F (l,n))
      (oraclePrefix_eq p k).symm))
  exact h.trans (hc.trans (hrep n y).symm)

theorem recursiveIn_iff_index (p : Bits) (f : ℕ → Part ℕ) :
    Nat.RecursiveIn (oracleSet (oracleSupport p)) f ↔
      ∃ e : ℕ, ∀ n, OracleProgram.numberedEval e p n = f n := by
  constructor
  · exact exists_index_of_recursiveIn p f
  · rintro ⟨e,he⟩
    exact (numberedEval_recursiveIn e p).of_eq he

/-- Graph and domain comparison, rather than a domain-only enumeration. -/
theorem exists_index_graph_domain (p : Bits) (f : ℕ → Part ℕ)
    (hf : Nat.RecursiveIn (oracleSet (oracleSupport p)) f) :
    ∃ e : ℕ, (∀ n y, y ∈ OracleProgram.numberedEval e p n ↔ y ∈ f n) ∧
      (∀ n, (OracleProgram.numberedEval e p n).Dom ↔ (f n).Dom) := by
  obtain ⟨e,he⟩ := exists_index_of_recursiveIn p f hf
  exact ⟨e,fun n y => by rw [he n],fun n => by rw [he n]⟩

end CategoricalEssentialIncompleteness.V46.Miller.OracleRelative
