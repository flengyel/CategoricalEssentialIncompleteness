/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec
public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.Vorspiel.Computability

/-! # Finite membership conditions and explicit vectors of witnesses -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.FiniteSigmaOne

abbrev Carrier := 𝚺₁.Semisentence 1
abbrev Matrix := 𝚺₀.Semisentence 2

/-- The canonical list code is the pinned Foundation vector code:
zero for nil and one plus the arithmetic pair for adjoining an entry. -/
theorem canonical_adjoin {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x a : M) : adjoin x a = ⟪x, a⟫ + 1 := rfl

theorem canonical_adjoin_injective {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y a b : M) : adjoin x a = adjoin y b ↔ x = y ∧ a = b :=
  adjoin_inj x y a b

theorem canonical_adjoin_ne_nil {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x a : M) : adjoin x a ≠ 0 := adjoin_ne_zero x a

def normalPrenex (C : Carrier) : Prenex 𝚺 1 Empty 1 :=
  Classical.choose (exists_prenex_of_hierarchy 𝗣𝗔 C.sigma_prop)

theorem normalPrenex_spec (C : Carrier) :
    𝗣𝗔 ⊢ ∀¹* (C.val 🡘 (normalPrenex C).val) :=
  Classical.choose_spec (exists_prenex_of_hierarchy 𝗣𝗔 C.sigma_prop)

/-- The first variable is the witness and the second is the entry. -/
def witnessMatrix (C : Carrier) : Matrix :=
  .mkSigma (normalPrenex C).sigmaInv.val (normalPrenex C).sigmaInv.val_deltaZero

section Models

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem lenDef_eval (l a : M) :
    lenDef.val.Evalb ![l, a] ↔ l = len a := len_defined.iff

@[simp] theorem nthDef_eval (x a i : M) :
    nthDef.val.Evalb ![x, a, i] ↔ x = nth a i := nth_defined.iff

theorem witnessMatrix_eval (C : Carrier) (x : M) :
    C.val.Evalb ![x] ↔ ∃ w : M, (witnessMatrix C).val.Evalb ![w, x] := by
  have h := models_iff_of_provable_iff (normalPrenex_spec C) M ![x]
  exact h.trans (by simp [witnessMatrix])

/-- No global choice function is postulated: the pinned arithmetic
successor induction builds a numerical witness vector by adjoining one
witness at a time. Each read is bounded by its numerical vector code. -/
theorem witnessVector_exists (R : Matrix) (a : M)
    (h : ∀ i < len a, ∃ w : M, R.val.Evalb ![w, nth a i]) :
    ∃ b : M, len b = len a ∧ ∀ i < len a,
      nth a i < a ∧ nth b i < b ∧ R.val.Evalb ![nth b i, nth a i] := by
  have hR : 𝚺₁-Relation (fun i w : M => R.val.Evalb ![w, nth a i]) := by
    let N : 𝚺₁.Semiformula M 3 := nthDef.rew Rew.emb
    let R' : 𝚺₀.Semiformula M 2 := R.rew Rew.emb
    refine ⟨.mkSigma “i w. ∃ x, !N.val x &a i ∧ !R'.val w x”, ?_⟩
    intro v
    simp [N, R']
  obtain ⟨b, hb, hbody⟩ := sigmaOne_skolem_vec hR h
  refine ⟨b, hb, ?_⟩
  intro i hi
  exact ⟨nth_lt_self hi, nth_lt_self (by simpa only [hb] using hi), hbody i hi⟩

end Models

/-- The direct membership assertion is deliberately an ordinary formula;
the implication from an entry graph is not assumed Sigma-one. -/
def allEntriesCondition (C : Carrier) : ArithmeticSemisentence 1 :=
  “a. ∀ l, !lenDef.val l a → ∀ i < l, ∀ x < a,
    !nthDef.val x a i → !C.val x”

/-- The sole unbounded data are the witness-vector code and common length.
The indices and both kinds of entries have explicit numerical bounds. -/
def witnessListFormula (R : Matrix) : Carrier := .mkSigma
  “a. ∃ b l, !lenDef.val l a ∧ !lenDef.val l b ∧
    ∀ i < l, ∃ x < a, ∃ w < b,
      !nthDef.val x a i ∧ !nthDef.val w b i ∧ !R.val w x”

def finiteMembership (C : Carrier) : Carrier := witnessListFormula (witnessMatrix C)

section Models

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem allEntriesCondition_eval (C : Carrier) (a : M) :
    (allEntriesCondition C).Evalb ![a] ↔
      ∀ i < len a, C.val.Evalb ![nth a i] := by
  have hraw : (allEntriesCondition C).Evalb ![a] ↔
      ∀ l : M, l = len a → ∀ i < l, ∀ x < a,
        x = nth a i → C.val.Evalb ![x] := by
    simp [allEntriesCondition]
  rw [hraw]
  constructor
  · intro h i hi
    exact h (len a) rfl i hi (nth a i) (nth_lt_self hi) rfl
  · intro h l hl i hi x _ hx
    subst l
    subst x
    exact h i hi

theorem witnessListFormula_eval_raw (R : Matrix) (a : M) :
    (witnessListFormula R).val.Evalb ![a] ↔
      ∃ b l : M, l = len a ∧ l = len b ∧
        ∀ i < l, ∃ x < a, ∃ w < b,
          x = nth a i ∧ w = nth b i ∧ R.val.Evalb ![w, x] := by
  simp [witnessListFormula]

@[simp] theorem witnessListFormula_eval (R : Matrix) (a : M) :
    (witnessListFormula R).val.Evalb ![a] ↔
      ∃ b : M, len b = len a ∧
        ∀ i < len a, R.val.Evalb ![nth b i, nth a i] := by
  rw [witnessListFormula_eval_raw]
  constructor
  · rintro ⟨b, l, hla, hlb, h⟩
    subst l
    refine ⟨b, hlb.symm, ?_⟩
    intro i hi
    obtain ⟨x, _, w, _, hx, hw, hR⟩ := h i hi
    simpa only [hx, hw] using hR
  · rintro ⟨b, hb, h⟩
    refine ⟨b, len a, rfl, hb.symm, ?_⟩
    intro i hi
    exact ⟨nth a i, nth_lt_self hi, nth b i,
      nth_lt_self (by simpa only [hb] using hi), rfl, rfl, h i hi⟩

theorem finite_membership_model (C : Carrier) (a : M) :
    (allEntriesCondition C).Evalb ![a] ↔ (finiteMembership C).val.Evalb ![a] := by
  rw [allEntriesCondition_eval, finiteMembership, witnessListFormula_eval]
  constructor
  · intro h
    have hw : ∀ i < len a, ∃ w : M, (witnessMatrix C).val.Evalb ![w, nth a i] :=
      fun i hi => (witnessMatrix_eval C (nth a i)).mp (h i hi)
    obtain ⟨b, hb, hbody⟩ := witnessVector_exists (witnessMatrix C) a hw
    exact ⟨b, hb, fun i hi => (hbody i hi).2.2⟩
  · rintro ⟨b, _, h⟩ i hi
    exact (witnessMatrix_eval C (nth a i)).mpr ⟨nth b i, h i hi⟩

end Models

def finiteMembershipSentence (C : Carrier) : ArithmeticSentence :=
  “∀ a, !(allEntriesCondition C) a ↔ !(finiteMembership C).val a”

@[simp] theorem finiteMembershipSentence_eval {M : Type*} [ORingStructure M] (C : Carrier) :
    (finiteMembershipSentence C).Evalb (M := M) ![] ↔
      ∀ a : M, (allEntriesCondition C).Evalb ![a] ↔
        (finiteMembership C).val.Evalb ![a] := by
  simp [finiteMembershipSentence]

/-- Lemma 6.4 for an arbitrary Sigma-one entry condition, using explicit canonical vector
codes and a vector of witnesses for its bounded matrix. -/
theorem finite_membership_PA (C : Carrier) : 𝗣𝗔 ⊢ finiteMembershipSentence C := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, finiteMembershipSentence_eval]
  exact finite_membership_model C


/-- A finite case distinction uses Pi-one tag tests. In particular this
includes bounded tag tests, and the Pi-one presentations of primitive
recursive tag tests. Each implication is syntactically Sigma-one. -/
def finiteCaseCondition {ι : Type*} [Fintype ι]
    (tags : ι → 𝚷₁.Semisentence 1) (conditions : ι → Carrier) : Carrier :=
  .mkSigma (Finset.uconj (fun j => (tags j).val 🡒 (conditions j).val)) (by
    simp only [Hierarchy.finset_uconj_iff, Hierarchy.imp_iff]
    intro j
    exact ⟨(tags j).pi_prop, (conditions j).sigma_prop⟩)

@[simp] theorem finiteCaseCondition_eval {ι : Type*} [Fintype ι]
    {M : Type*} [ORingStructure M] (tags : ι → 𝚷₁.Semisentence 1)
    (conditions : ι → Carrier) (x : M) :
    (finiteCaseCondition tags conditions).val.Evalb ![x] ↔
      ∀ j : ι, (tags j).val.Evalb ![x] → (conditions j).val.Evalb ![x] := by
  simp [finiteCaseCondition]

/-- Finite tagged conditions have an explicit vector-of-witnesses
Sigma-one presentation, proved equivalent in PA. -/
theorem finite_tagged_membership_PA {ι : Type*} [Fintype ι]
    (tags : ι → 𝚷₁.Semisentence 1) (conditions : ι → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (finiteCaseCondition tags conditions) :=
  finite_membership_PA _

theorem finite_tagged_membership_model {ι : Type*} [Fintype ι]
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (tags : ι → 𝚷₁.Semisentence 1) (conditions : ι → Carrier) (a : M) :
    (finiteMembership (finiteCaseCondition tags conditions)).val.Evalb ![a] ↔
      ∀ i < len a, ∀ j : ι,
        (tags j).val.Evalb ![nth a i] → (conditions j).val.Evalb ![nth a i] := by
  rw [← finite_membership_model, allEntriesCondition_eval]
  simp only [finiteCaseCondition_eval]

/-- A closed numeral inserted into any finite tuple of bound variables. -/
def numeralTerm (j : ℕ) {n : ℕ} : ArithmeticSemiterm Empty n :=
  (Semiterm.Operator.numeral ℒₒᵣ j).operator ![]

/-- Concrete primitive-recursive tags are the first coordinates of
canonical arithmetic pairs. The payload is bounded by the whole record. -/
def pairTag (j : ℕ) : 𝚺₀.Semisentence 1 := .mkSigma
  “r. ∃ x < r + 1, !pairDef.val r !!(numeralTerm j) x”

def pairTagPi (j : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi (pairTag j).val (pairTag j).sigma_prop.of_zero

@[simp] theorem pairTag_eval {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (j : ℕ) (r : M) :
    (pairTag j).val.Evalb ![r] ↔ π₁ r = ORingStructure.numeral j := by
  have hraw : (pairTag j).val.Evalb ![r] ↔
      ∃ x < r + 1, r = ⟪ORingStructure.numeral j, x⟫ := by
    simp [pairTag, numeralTerm]
  rw [hraw]
  constructor
  · rintro ⟨x, _, he⟩
    simpa only [pi₁_pair] using congrArg pi₁ he
  · intro he
    refine ⟨π₂ r, Arithmetic.lt_succ_iff_le.mpr (pi₂_le_self r), ?_⟩
    rw [← he]
    simp

theorem nat_pi₁_eq (r : ℕ) : π₁ r = r.unpair.1 := by
  have hp : Nat.pair (π₁ r) (π₂ r) = r := by
    simpa only [nat_pair_eq] using pair_unpair r
  have hu : (π₁ r, π₂ r) = r.unpair := by
    simpa only [Nat.unpair_pair] using congrArg Nat.unpair hp
  exact congrArg Prod.fst hu

/-- The concrete arithmetic tag reader is primitive recursive on the
standard codes, and the preceding theorem proves its PA-model semantics. -/
theorem pairTag_primrec (j : ℕ) :
    PrimrecPred (fun r : ℕ => (pairTag j).val.Evalb ![r]) := by
  have hp : Primrec (fun r : ℕ => π₁ r) := by
    simpa only [nat_pi₁_eq] using (Primrec.fst.comp Primrec.unpair)
  simpa only [pairTag_eval, Nat.numeral_eq] using
    (Primrec.eq.comp hp (Primrec.const j))

theorem pair_tagged_membership_model {k : ℕ} (conditions : Fin k → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (finiteMembership (finiteCaseCondition
      (fun j : Fin k => pairTagPi j.val) conditions)).val.Evalb ![a] ↔
      ∀ i < len a, ∀ j : Fin k,
        π₁ (nth a i) = ORingStructure.numeral j.val →
          (conditions j).val.Evalb ![nth a i] := by
  rw [finite_tagged_membership_model]
  simp only [pairTagPi, HierarchySymbol.Semiformula.val_mkPi, pairTag_eval]


/-- Apply an entry condition to the payload of a tagged record. Both
projections are bounded by the complete record code. -/
def onPayload (C : Carrier) : Carrier := .mkSigma
  “r. ∃ t < r + 1, ∃ x < r + 1, !pairDef.val r t x ∧ !C.val x”

@[simp] theorem onPayload_eval {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C : Carrier) (r : M) :
    (onPayload C).val.Evalb ![r] ↔ C.val.Evalb ![π₂ r] := by
  have hraw : (onPayload C).val.Evalb ![r] ↔
      ∃ t < r + 1, ∃ x < r + 1, r = ⟪t, x⟫ ∧ C.val.Evalb ![x] := by
    simp [onPayload]
  rw [hraw]
  constructor
  · rintro ⟨t, _, x, _, he, hc⟩
    have hp : π₂ r = x := by simpa only [pi₂_pair] using congrArg pi₂ he
    simpa only [hp] using hc
  · intro hc
    exact ⟨π₁ r, Arithmetic.lt_succ_iff_le.mpr (pi₁_le_self r),
      π₂ r, Arithmetic.lt_succ_iff_le.mpr (pi₂_le_self r),
      by simp, hc⟩

theorem pair_payload_tagged_membership_model {k : ℕ} (conditions : Fin k → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (finiteMembership (finiteCaseCondition
      (fun j : Fin k => pairTagPi j.val) (fun j => onPayload (conditions j)))).val.Evalb ![a] ↔
      ∀ i < len a, ∀ j : Fin k,
        π₁ (nth a i) = ORingStructure.numeral j.val →
          (conditions j).val.Evalb ![π₂ (nth a i)] := by
  simpa only [onPayload_eval] using
    pair_tagged_membership_model (fun j => onPayload (conditions j)) a


/-- The selected-case version requires a tag in the finite range; records with any other
tag are excluded by this Sigma-one predicate. -/
def selectedPayloadCondition {k : ℕ} (conditions : Fin k → Carrier) : Carrier :=
  .mkSigma (Finset.udisj (fun j : Fin k =>
    (pairTag j.val).val ⋏ (onPayload (conditions j)).val)) (by
      simp only [Hierarchy.finset_udisj_iff, Hierarchy.and_iff]
      intro j
      exact ⟨(pairTag j.val).sigma_prop.of_zero, (onPayload (conditions j)).sigma_prop⟩)

@[simp] theorem selectedPayloadCondition_eval {k : ℕ} (conditions : Fin k → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (r : M) :
    (selectedPayloadCondition conditions).val.Evalb ![r] ↔
      ∃ j : Fin k, π₁ r = ORingStructure.numeral j.val ∧
        (conditions j).val.Evalb ![π₂ r] := by
  simp [selectedPayloadCondition]

def selectedTaggedList {k : ℕ} (conditions : Fin k → Carrier) : Carrier :=
  finiteMembership (selectedPayloadCondition conditions)

theorem selectedTaggedList_model {k : ℕ} (conditions : Fin k → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (selectedTaggedList conditions).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin k,
        π₁ (nth a i) = ORingStructure.numeral j.val ∧
          (conditions j).val.Evalb ![π₂ (nth a i)] := by
  rw [selectedTaggedList, ← finite_membership_model, allEntriesCondition_eval]
  simp only [selectedPayloadCondition_eval]

theorem selected_tagged_membership_PA {k : ℕ} (conditions : Fin k → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (selectedPayloadCondition conditions) :=
  finite_membership_PA _

end CategoricalEssentialIncompleteness.V46.FiniteSigmaOne
