/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OraclePrefixRecursion

/-! # The finite-query domain enumeration is exactly ordinary oracle enumerability -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Nat.Partrec (Code)
open Encodable Denumerable

def trialFuel (p : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair p).1).2).2
def trialInput (p : ℕ) : ℕ := Nat.pair (Nat.unpair (Nat.unpair p).1).1 (Nat.unpair p).2

def trialCode (c : Code) (p : ℕ) : ℕ := if (c.evaln (trialFuel p) (trialInput p)).isSome then 0 else 1

theorem trialCode_computable (c : Code) : Computable (trialCode c) := by
  have hf : Computable trialFuel := Computable.snd.comp (Computable.unpair.comp
    (Computable.snd.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair))))
  have hi : Computable trialInput := Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair)))
    (Computable.snd.comp Computable.unpair)
  have he : Computable (fun p : ℕ => c.evaln (trialFuel p) (trialInput p)) :=
    Code.primrec_evaln.to_comp.comp (Computable.pair (Computable.pair hf (Computable.const c)) hi)
  apply ((Primrec.option_isSome.to_comp.comp he).cond
    (Computable.const 0) (Computable.const 1)).of_eq
  intro p
  cases h : (c.evaln (trialFuel p) (trialInput p)).isSome <;> simp [trialCode,h]

def trial (S : Set ℕ) (c : Code) (p : ℕ) : ℕ :=
  trialCode c (Nat.pair p (encode (oraclePrefix S (Nat.unpair (Nat.unpair p).2).1)))

theorem trial_recursiveIn (S : Set ℕ) (c : Code) :
    Nat.RecursiveIn (oracleSet S) (fun p => Part.some (trial S c p)) := by
  have hn : Computable (fun p : ℕ => (Nat.unpair (Nat.unpair p).2).1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  refine (Nat.RecursiveIn.comp (recursiveIn_of_computable (trialCode_computable c))
    (.pair (recursiveIn_of_computable Computable.id)
      (.comp (prefixCode_recursiveIn S) (recursiveIn_of_computable hn)))).of_eq ?_
  intro p
  simp [trial,Seq.seq,Part.bind_eq_bind]

theorem trial_pair (S : Set ℕ) (c : Code) (x n k : ℕ) :
    trial S c (Nat.pair x (Nat.pair n k))=
      if (c.evaln k (Nat.pair x (encode (oraclePrefix S n)))).isSome then 0 else 1 := by
  simp only [trial,trialCode,trialInput,trialFuel,Nat.unpair_pair]

def numberedSemidecision (S : Set ℕ) (c : Code) (x : ℕ) : Part ℕ :=
  Nat.rfind (fun t => (Part.some (trial S c (Nat.pair x t))).map (fun m => decide (m=0)))

theorem numberedSemidecision_recursiveIn (S : Set ℕ) (c : Code) :
    Nat.RecursiveIn (oracleSet S) (numberedSemidecision S c) :=
  .rfind (trial_recursiveIn S c)

theorem numberedSemidecision_domain (S : Set ℕ) (c : Code) (x : ℕ) :
    (numberedSemidecision S c x).Dom ↔ oracleDomain S (encode c) x := by
  rw [numberedSemidecision,Nat.rfind_dom]
  constructor
  · rintro ⟨t,ht,_⟩
    have hz : trial S c (Nat.pair x t)=0 := by simpa using ht
    have hp : t=Nat.pair (Nat.unpair t).1 (Nat.unpair t).2 := (Nat.pair_unpair t).symm
    rw [hp,trial_pair] at hz
    have hs : (c.evaln (Nat.unpair t).2
        (Nat.pair x (encode (oraclePrefix S (Nat.unpair t).1)))).isSome := by
      split_ifs at hz with h
      exact h
    obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨(Nat.unpair t).1,?_⟩
    rw [Denumerable.ofNat_encode]
    exact Part.dom_iff_mem.mpr ⟨y,Code.evaln_sound hy⟩
  · rintro ⟨n,hn⟩
    rw [Denumerable.ofNat_encode] at hn
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp hn
    obtain ⟨k,hk⟩ := Code.evaln_complete.mp hy
    change c.evaln k (Nat.pair x (encode (oraclePrefix S n)))=some y at hk
    refine ⟨Nat.pair n k,?_,?_⟩
    · simp [trial_pair,hk]
    · intro m hm
      simp only [Part.map_some,Part.some_dom]

/-- Exact comparison with the existing minimal oracle-recursion definition.
Both positive and negative oracle answers are available through the characteristic
oracle; ordinary finite-query certificates give exactly its c.e. domains. -/
theorem finiteOracleRE_iff_recursiveIn_domain (S : Set ℕ) (p : ℕ → Prop) :
    FiniteOracleRE S p ↔ ∃ f : ℕ → Part ℕ,Nat.RecursiveIn (oracleSet S) f ∧
      ∀ x,p x ↔ (f x).Dom := by
  constructor
  · intro hp
    obtain ⟨a,ha⟩ := oracleDomain_surjective S hp
    refine ⟨numberedSemidecision S (ofNat Code a),numberedSemidecision_recursiveIn _ _,?_⟩
    intro x
    rw [numberedSemidecision_domain,Denumerable.encode_ofNat]
    exact (ha x).symm
  · rintro ⟨f,hf,hp⟩
    exact (recursiveIn_domain hf).of_eq (fun x => (hp x).symm)

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
