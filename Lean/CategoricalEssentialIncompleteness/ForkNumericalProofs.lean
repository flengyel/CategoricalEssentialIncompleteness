/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofRelabeling
public import CategoricalEssentialIncompleteness.FinitePowerCarriers

/-! # C.e. proof carriers and their actual recursive conclusion maps -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (natCarrier)
open EnumerableCarriers (Carrier val)

def proofCarrier (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) : Carrier :=
  EnumerableCarriers.codedCarrier {t | ProofTree.Valid A B t} (ProofTree.valid_re A B hA hB)

theorem mem_proofCarrier (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) (n : ℕ) :
    n ∈ (proofCarrier A B hA hB).support ↔ ProofTree.Valid A B (ProofTree.decode n) := by
  constructor
  · rintro ⟨t,ht,he⟩
    change ProofTree.encode t=n at he
    rw [← he,ProofTree.decode_encode]
    exact ht
  · intro h
    exact ⟨ProofTree.decode n,h,ProofTree.encode_decode n⟩

def conclusionCode (n : ℕ) : ℕ :=
  Formula.encode ((ProofTree.decode n).conclusion.getD (.atom 0))

theorem conclusionCode_computable : Computable conclusionCode :=
  Formula.encode_computable.comp (Primrec.option_getD.to_comp.comp
    (ProofTree.conclusion_computable.comp ProofTree.decode_computable)
    (Computable.const (Formula.atom 0)))

theorem conclusionCode_of_concludes {A B : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) : conclusionCode (ProofTree.encode t)=Formula.encode p := by
  unfold conclusionCode
  rw [ProofTree.decode_encode,ProofTree.concludes_conclusion h]
  rfl

def conclusionArrow (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    proofCarrier A B hA hB ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction conclusionCode conclusionCode_computable
    (fun x _ => Set.mem_univ (conclusionCode x))

theorem conclusionArrow_total (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    isTotal (conclusionArrow A B hA hB) :=
  EnumerableCarriers.totalFromFunction_total conclusionCode conclusionCode_computable
    (fun x _ => Set.mem_univ (conclusionCode x))

theorem conclusion_range (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) (n : ℕ) :
    n ∈ EnumerableCarriers.support (Ranges.range (conclusionArrow A B hA hB)) ↔
      Formula.decode n ∈ Theorems A B := by
  rw [EnumerableCarriers.support_range]
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨hs,he⟩ := (EnumerableCarriers.mem_totalFromFunction conclusionCode
      conclusionCode_computable (fun x _ => Set.mem_univ (conclusionCode x)) x n).mp hx
    obtain ⟨p,hp⟩ := (mem_proofCarrier A B hA hB x).mp hs
    have hc : conclusionCode x=Formula.encode p := by
      simpa only [ProofTree.encode_decode] using conclusionCode_of_concludes hp
    rw [he,hc,Formula.decode_encode]
    exact ⟨ProofTree.decode x,hp⟩
  · rintro ⟨t,ht⟩
    refine ⟨ProofTree.encode t,(EnumerableCarriers.mem_totalFromFunction conclusionCode
      conclusionCode_computable (fun x _ => Set.mem_univ (conclusionCode x)) _ n).mpr ?_⟩
    refine ⟨(mem_proofCarrier A B hA hB _).mpr ?_,?_⟩
    · rw [ProofTree.decode_encode]
      exact ⟨Formula.decode n,ht⟩
    · rw [conclusionCode_of_concludes ht,Formula.encode_decode]

def proofRelabelCode (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ProofTree.encode ((ProofTree.decode n).mapAtoms f)

theorem proofRelabelCode_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable (proofRelabelCode f) :=
  ProofTree.encode_computable.comp ((ProofTree.mapAtoms_computable hf).comp ProofTree.decode_computable)

theorem proofRelabel_valid {A B A' B' : Set ℕ} (f : ℕ → ℕ)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') (n : ℕ)
    (h : ProofTree.Valid A B (ProofTree.decode n)) :
    ProofTree.Valid A' B' (ProofTree.decode (proofRelabelCode f n)) := by
  obtain ⟨p,hp⟩ := h
  unfold proofRelabelCode
  rw [ProofTree.decode_encode]
  exact ⟨p.mapAtoms f,hp.mapAtoms f ha hb⟩

def proofMap {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') :
    proofCarrier A B hA hB ⟶ proofCarrier A' B' hA' hB' :=
  EnumerableCarriers.totalFromFunction (proofRelabelCode f) (proofRelabelCode_computable hf)
    (fun n hn => (mem_proofCarrier A' B' hA' hB' _).mpr
      (proofRelabel_valid f ha hb n ((mem_proofCarrier A B hA hB n).mp hn)))

theorem proofMap_total {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') :
    isTotal (proofMap hA hB hA' hB' f hf ha hb) :=
  EnumerableCarriers.totalFromFunction_total (proofRelabelCode f) (proofRelabelCode_computable hf)
    (fun n hn => (mem_proofCarrier A' B' hA' hB' _).mpr
      (proofRelabel_valid f ha hb n ((mem_proofCarrier A B hA hB n).mp hn)))

/-- Conclusion commutes with relabeling on valid proofs. Relabeling need not
reflect invalid premise matching when the atom map is noninjective. -/
theorem conclusion_relabel {A B A' B' : Set ℕ} (f : ℕ → ℕ)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') (n : ℕ)
    (h : ProofTree.Valid A B (ProofTree.decode n)) :
    conclusionCode (proofRelabelCode f n)=Formula.sigma f (conclusionCode n) := by
  obtain ⟨p,hp⟩ := h
  have hc : conclusionCode n=p.encode := by
    simpa only [ProofTree.encode_decode] using conclusionCode_of_concludes hp
  unfold proofRelabelCode
  rw [conclusionCode_of_concludes (hp.mapAtoms f ha hb),hc,sigma_encode]

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
