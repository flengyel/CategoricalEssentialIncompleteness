/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.CodedObjectMembership
public import FailureOfComposition.SigmaOneRealization
public import FailureOfComposition.UniformIndexQuotient
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The typed program category obtained from coded-object restrictions

Every coded object is represented inside the uniform-provability program
quotient by a selected partial identity.  A morphism from `Q` to `R` is a
quotient class fixed by the source idempotent on the right and by the target
idempotent on the left.  Composition is multiplication in the quotient, with
the right factor executed first.

The construction retains global uniform provable equality of the normalized
production programs.  It is a concrete split-idempotent category associated
with the accepted `Nat.Partrec.Code` numbering; no comparison with the
manuscript's category `S_T`, categorical product or coproduct law, range,
restriction-category structure, or numbering translation is asserted here.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedProgramCategory

open CodedObjectMembership ProofSearch ConcreteEvaluator
open SigmaOneRealization UniformIndexQuotient NumericalProofBridge

noncomputable section

/-! ## Partial identities for coded objects -/

/-- The graph of the partial identity whose domain is the coded object `Q`.
The variables are input and output, in that order. -/
def objectIdentityGraph (Q : STObjectCode) : Graph :=
  .mkSigma “x y. !(memberFormula Q).val x ∧ y = x”

@[simp] theorem objectIdentityGraph_eval
    {M : Type*} [ORingStructure M] (Q : STObjectCode) (x y : M) :
    (objectIdentityGraph Q).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧ y = x := by
  simp [objectIdentityGraph]

/-- The partial-identity graph of a coded object is functional in PA. -/
theorem objectIdentityGraph_functional (Q : STObjectCode) :
    Functional (objectIdentityGraph Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((objectIdentityGraph_eval Q x y).mp hy).2.trans
    ((objectIdentityGraph_eval Q x z).mp hz).2.symm

/-- A production index selected from the existing realization theorem for the
partial identity of `Q`.  The selection is external and need not be effective
in a numerical code for object expressions. -/
def deltaIndex (Q : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (objectIdentityGraph Q)
    (objectIdentityGraph_functional Q))

/-- PA proves that `deltaIndex Q` has exactly the partial-identity graph of
`Q`. -/
theorem deltaIndex_uniform (Q : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (deltaIndex Q)) (objectIdentityGraph Q) :=
  Classical.choose_spec (realize_graph (objectIdentityGraph Q)
    (objectIdentityGraph_functional Q))

/-- The graph equation for `deltaIndex Q` in every model of PA. -/
@[simp] theorem eventualGraph_deltaIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (x y : M) :
    (eventualGraph (deltaIndex Q)).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧ y = x := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (deltaIndex_uniform Q)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (objectIdentityGraph_eval Q x y)

/-- Relational composition of the partial identity of `Q` with itself is the
same partial identity, uniformly in PA. -/
theorem objectIdentityGraph_comp_self (Q : STObjectCode) :
    Uniform 𝗣𝗔 (comp (objectIdentityGraph Q) (objectIdentityGraph Q))
      (objectIdentityGraph Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [comp_eval]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    obtain ⟨hQ, hzx⟩ := (objectIdentityGraph_eval Q x z).mp hxz
    obtain ⟨-, hyz⟩ := (objectIdentityGraph_eval Q z y).mp hzy
    exact (objectIdentityGraph_eval Q x y).mpr ⟨hQ, hyz.trans hzx⟩
  · intro hxy
    obtain ⟨hQ, hyx⟩ := (objectIdentityGraph_eval Q x y).mp hxy
    refine ⟨x, (objectIdentityGraph_eval Q x x).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (objectIdentityGraph_eval Q x y).mpr ⟨hQ, hyx⟩

/-- The omega partial-identity graph is the total identity graph. -/
theorem objectIdentityGraph_omega_identity :
    Uniform 𝗣𝗔 (objectIdentityGraph .omega) identity := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, uniformSentence_eval, objectIdentityGraph]

/-- In PA, the selected omega restriction index is uniformly equivalent to
the production identity index. -/
theorem deltaIndex_omega_eq_identity :
    EqIndex 𝗣𝗔 (deltaIndex .omega) Kleene.identityIndex :=
  uniform_trans (deltaIndex_uniform .omega)
    (uniform_trans objectIdentityGraph_omega_identity
      (uniform_symm eventualGraph_identity))

/-- In PA, canonical self-composition of a selected object restriction is
uniformly equivalent to that restriction. -/
theorem deltaIndex_comp_self (Q : STObjectCode) :
    EqIndex 𝗣𝗔 (compIndex (deltaIndex Q) (deltaIndex Q)) (deltaIndex Q) :=
  uniform_trans (eventualGraph_composition (deltaIndex Q) (deltaIndex Q))
    (uniform_trans
      (uniform_comp_congr (deltaIndex_uniform Q) (deltaIndex_uniform Q))
      (uniform_trans (objectIdentityGraph_comp_self Q)
        (uniform_symm (deltaIndex_uniform Q))))

/-- The omega restriction remains the quotient identity in every theory whose
provability includes PA. -/
theorem deltaIndex_omega_eq_identity_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (deltaIndex .omega) Kleene.identityIndex :=
  WeakerThan.pbl deltaIndex_omega_eq_identity

/-- Object restrictions remain idempotent in every theory whose provability
includes PA. -/
theorem deltaIndex_comp_self_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    EqIndex T (compIndex (deltaIndex Q) (deltaIndex Q)) (deltaIndex Q) :=
  WeakerThan.pbl (deltaIndex_comp_self Q)

/-! ## Source restriction and source-target normalization -/

/-- Restrict the input of program `q` to the coded object `Q`. -/
def restrictIndex (Q : STObjectCode) (q : ℕ) : ℕ :=
  compIndex q (deltaIndex Q)

/-- Restrict the input of `q` to `Q` and its output to `R`. -/
def normalizeIndex (Q R : STObjectCode) (q : ℕ) : ℕ :=
  compIndex (deltaIndex R) (restrictIndex Q q)

/-- The graph formula for the source restriction of `q` to `Q`. -/
def sourceRestrictedGraph (Q : STObjectCode) (q : ℕ) : Graph :=
  .mkSigma “x y. !(memberFormula Q).val x ∧ !(eventualGraph q).val x y”

/-- The graph formula for normalization from source `Q` to target `R`. -/
def normalizedGraph (Q R : STObjectCode) (q : ℕ) : Graph :=
  .mkSigma “x y. !(memberFormula Q).val x ∧
    !(eventualGraph q).val x y ∧ !(memberFormula R).val y”

@[simp] theorem sourceRestrictedGraph_eval
    {M : Type*} [ORingStructure M] (Q : STObjectCode) (q : ℕ) (x y : M) :
    (sourceRestrictedGraph Q q).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧
        (eventualGraph q).val.Evalb ![x, y] := by
  simp [sourceRestrictedGraph]

@[simp] theorem normalizedGraph_eval
    {M : Type*} [ORingStructure M] (Q R : STObjectCode) (q : ℕ) (x y : M) :
    (normalizedGraph Q R q).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧
        (eventualGraph q).val.Evalb ![x, y] ∧
        (memberFormula R).val.Evalb ![y] := by
  simp [normalizedGraph]

/-- The source-restriction graph equation in every model of PA. -/
@[simp] theorem eventualGraph_restrictIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (q : ℕ) (x y : M) :
    (eventualGraph (restrictIndex Q q)).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧
        (eventualGraph q).val.Evalb ![x, y] := by
  rw [restrictIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hz, hq⟩
    obtain ⟨hQ, rfl⟩ := (eventualGraph_deltaIndex_eval Q x z).mp hz
    exact ⟨hQ, hq⟩
  · rintro ⟨hQ, hq⟩
    exact ⟨x, (eventualGraph_deltaIndex_eval Q x x).mpr ⟨hQ, rfl⟩, hq⟩

/-- The source-target normalization graph equation in every model of PA. -/
@[simp] theorem eventualGraph_normalizeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (x y : M) :
    (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧
        (eventualGraph q).val.Evalb ![x, y] ∧
        (memberFormula R).val.Evalb ![y] := by
  rw [normalizeIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hz, hR⟩
    obtain ⟨hQ, hq⟩ := (eventualGraph_restrictIndex_eval Q q x z).mp hz
    obtain ⟨hRz, rfl⟩ := (eventualGraph_deltaIndex_eval R z y).mp hR
    exact ⟨hQ, hq, hRz⟩
  · rintro ⟨hQ, hq, hR⟩
    exact ⟨y, (eventualGraph_restrictIndex_eval Q q x y).mpr ⟨hQ, hq⟩,
      (eventualGraph_deltaIndex_eval R y y).mpr ⟨hR, rfl⟩⟩

/-- PA proves the source-restriction graph equation uniformly. -/
theorem restrictIndex_uniform (Q : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (restrictIndex Q q))
      (sourceRestrictedGraph Q q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (eventualGraph_restrictIndex_eval Q q x y).trans
    (sourceRestrictedGraph_eval Q q x y).symm

/-- PA proves the source-target normalization graph equation uniformly. -/
theorem normalizeIndex_uniform (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (normalizeIndex Q R q))
      (normalizedGraph Q R q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (eventualGraph_normalizeIndex_eval Q R q x y).trans
    (normalizedGraph_eval Q R q x y).symm

/-- Canonical composition is primitive recursive in both external indices. -/
theorem primrec₂_compIndex : Primrec₂ compIndex := by
  have hp : Primrec₂ (fun f g : ℕ => Nat.pair f g) := Primrec₂.natPair
  have h₁ : Primrec₂ (fun f g : ℕ => 2 * Nat.pair f g) :=
    Primrec.nat_mul.comp (Primrec.const 2) hp
  have h₂ : Primrec₂ (fun f g : ℕ => 2 * Nat.pair f g + 1) :=
    Primrec.succ.comp h₁
  have h₃ : Primrec₂ (fun f g : ℕ => 2 * (2 * Nat.pair f g + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 2) h₂
  have h₄ : Primrec₂ (fun f g : ℕ => 2 * (2 * Nat.pair f g + 1) + 4) :=
    Primrec.nat_add.comp h₃ (Primrec.const 4)
  apply h₄.of_eq
  intro f g
  exact (canonicalPartrecCompIndex_eq f g).symm

/-- For fixed `Q`, source restriction is primitive recursive in the program
index. -/
theorem primrec_restrictIndex (Q : STObjectCode) :
    Primrec (restrictIndex Q) :=
  primrec₂_compIndex.comp Primrec.id (Primrec.const (deltaIndex Q))

/-- For fixed `Q` and `R`, normalization is primitive recursive in the
program index. -/
theorem primrec_normalizeIndex (Q R : STObjectCode) :
    Primrec (normalizeIndex Q R) :=
  primrec₂_compIndex.comp (Primrec.const (deltaIndex R))
    (primrec_restrictIndex Q)

/-- Normalization is idempotent modulo PA-uniform graph equality. -/
theorem normalizeIndex_idempotent (Q R : STObjectCode) (q : ℕ) :
    EqIndex 𝗣𝗔 (normalizeIndex Q R (normalizeIndex Q R q))
      (normalizeIndex Q R q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_normalizeIndex_eval,
    eventualGraph_normalizeIndex_eval]
  tauto

/-! ## Exact support and equality comparisons -/

/-- The object-language assertion that `q` maps members of `Q` only to
members of `R`. -/
def supportSentence (Q R : STObjectCode) (q : ℕ) : ArithmeticSentence :=
  “∀ x y, !(eventualGraph q).val x y →
    (!(memberFormula Q).val x ∧ !(memberFormula R).val y)”

/-- Equality of two raw graphs after restricting their common source to `Q`.
-/
def sourceEqualitySentence (Q : STObjectCode) (q r : ℕ) : ArithmeticSentence :=
  “∀ x y, !(memberFormula Q).val x →
    (!(eventualGraph q).val x y ↔ !(eventualGraph r).val x y)”

/-- The assertion that target restriction does not remove any computation of
the source-restricted program. -/
def targetPreservationSentence
    (Q R : STObjectCode) (q : ℕ) : ArithmeticSentence :=
  “∀ x y, (!(memberFormula Q).val x ∧ !(eventualGraph q).val x y) →
    !(memberFormula R).val y”

@[simp] theorem supportSentence_eval
    {M : Type*} [ORingStructure M] (Q R : STObjectCode) (q : ℕ) :
    (supportSentence Q R q).Evalb (M := M) ![] ↔
      ∀ x y : M, (eventualGraph q).val.Evalb ![x, y] →
        (memberFormula Q).val.Evalb ![x] ∧
        (memberFormula R).val.Evalb ![y] := by
  simp [supportSentence]

@[simp] theorem sourceEqualitySentence_eval
    {M : Type*} [ORingStructure M] (Q : STObjectCode) (q r : ℕ) :
    (sourceEqualitySentence Q q r).Evalb (M := M) ![] ↔
      ∀ x y : M, (memberFormula Q).val.Evalb ![x] →
        ((eventualGraph q).val.Evalb ![x, y] ↔
          (eventualGraph r).val.Evalb ![x, y]) := by
  simp [sourceEqualitySentence]

@[simp] theorem targetPreservationSentence_eval
    {M : Type*} [ORingStructure M] (Q R : STObjectCode) (q : ℕ) :
    (targetPreservationSentence Q R q).Evalb (M := M) ![] ↔
      ∀ x y : M,
        (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] →
        (memberFormula R).val.Evalb ![y] := by
  simp [targetPreservationSentence]

/-- A representative is `T`-supported from `Q` to `R` exactly when it is
uniformly `T`-equivalent to its normalization. -/
theorem proves_support_iff_eqIndex_normalize
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    T ⊢ supportSentence Q R q ↔
      EqIndex T (normalizeIndex Q R q) q := by
  constructor
  · intro hs
    apply complete.{0} T
    intro M _ hM
    have hsM := consequence_iff.mp (Theory.Proof.sound hs) M hM
    have hnM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (normalizeIndex_uniform Q R q))) M hM
    rw [models_iff, supportSentence_eval] at hsM
    rw [models_iff, uniformSentence_eval] at hnM ⊢
    intro x y
    have hnorm :
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] ∧
          (memberFormula R).val.Evalb ![y] :=
      (hnM x y).trans (normalizedGraph_eval Q R q x y)
    constructor
    · exact fun hn => (hnorm.mp hn).2.1
    · intro hq
      obtain ⟨hQ, hR⟩ := hsM x y hq
      exact hnorm.mpr ⟨hQ, hq, hR⟩
  · intro heq
    apply complete.{0} T
    intro M _ hM
    have heqM := consequence_iff.mp (Theory.Proof.sound heq) M hM
    have hnM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (normalizeIndex_uniform Q R q))) M hM
    rw [models_iff, uniformSentence_eval] at heqM hnM
    rw [models_iff, supportSentence_eval]
    intro x y hq
    have hnorm :
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] ∧
          (memberFormula R).val.Evalb ![y] :=
      (hnM x y).trans (normalizedGraph_eval Q R q x y)
    exact ⟨(hnorm.mp ((heqM x y).mpr hq)).1,
      (hnorm.mp ((heqM x y).mpr hq)).2.2⟩

/-- Equality of two source restrictions is exactly uniform equality of the
raw graphs under the internal source-membership hypothesis. -/
theorem eqIndex_restrict_iff_proves_sourceEquality
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : STObjectCode) (q r : ℕ) :
    EqIndex T (restrictIndex Q q) (restrictIndex Q r) ↔
      T ⊢ sourceEqualitySentence Q q r := by
  constructor
  · intro heq
    apply complete.{0} T
    intro M _ hM
    have heqM := consequence_iff.mp (Theory.Proof.sound heq) M hM
    have hqM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q q))) M hM
    have hrM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q r))) M hM
    rw [models_iff, uniformSentence_eval] at heqM hqM hrM
    rw [models_iff, sourceEqualitySentence_eval]
    intro x y hQ
    have hq :
        (eventualGraph (restrictIndex Q q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] :=
      (hqM x y).trans (sourceRestrictedGraph_eval Q q x y)
    have hr :
        (eventualGraph (restrictIndex Q r)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph r).val.Evalb ![x, y] :=
      (hrM x y).trans (sourceRestrictedGraph_eval Q r x y)
    constructor
    · intro hraw
      exact (hr.mp ((heqM x y).mp (hq.mpr ⟨hQ, hraw⟩))).2
    · intro hraw
      exact (hq.mp ((heqM x y).mpr (hr.mpr ⟨hQ, hraw⟩))).2
  · intro hsource
    apply complete.{0} T
    intro M _ hM
    have hsM := consequence_iff.mp (Theory.Proof.sound hsource) M hM
    have hqM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q q))) M hM
    have hrM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q r))) M hM
    rw [models_iff, sourceEqualitySentence_eval] at hsM
    rw [models_iff, uniformSentence_eval] at hqM hrM ⊢
    intro x y
    have hq :
        (eventualGraph (restrictIndex Q q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] :=
      (hqM x y).trans (sourceRestrictedGraph_eval Q q x y)
    have hr :
        (eventualGraph (restrictIndex Q r)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph r).val.Evalb ![x, y] :=
      (hrM x y).trans (sourceRestrictedGraph_eval Q r x y)
    constructor
    · intro h
      obtain ⟨hQ, hraw⟩ := hq.mp h
      exact hr.mpr ⟨hQ, (hsM x y hQ).mp hraw⟩
    · intro h
      obtain ⟨hQ, hraw⟩ := hr.mp h
      exact hq.mpr ⟨hQ, (hsM x y hQ).mpr hraw⟩

/-- Target restriction preserves a source-restricted program exactly when `T`
proves that all of its outputs belong to the target object. -/
theorem eqIndex_normalize_restrict_iff_proves_targetPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T (normalizeIndex Q R q) (restrictIndex Q q) ↔
      T ⊢ targetPreservationSentence Q R q := by
  constructor
  · intro heq
    apply complete.{0} T
    intro M _ hM
    have heqM := consequence_iff.mp (Theory.Proof.sound heq) M hM
    have hnM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (normalizeIndex_uniform Q R q))) M hM
    have hsM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q q))) M hM
    rw [models_iff, uniformSentence_eval] at heqM hnM hsM
    rw [models_iff, targetPreservationSentence_eval]
    intro x y hsource
    have hnorm :
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] ∧
          (memberFormula R).val.Evalb ![y] :=
      (hnM x y).trans (normalizedGraph_eval Q R q x y)
    have hres :
        (eventualGraph (restrictIndex Q q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] :=
      (hsM x y).trans (sourceRestrictedGraph_eval Q q x y)
    exact (hnorm.mp ((heqM x y).mpr (hres.mpr hsource))).2.2
  · intro htarget
    apply complete.{0} T
    intro M _ hM
    have htM := consequence_iff.mp (Theory.Proof.sound htarget) M hM
    have hnM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (normalizeIndex_uniform Q R q))) M hM
    have hsM := consequence_iff.mp
      (Theory.Proof.sound (WeakerThan.pbl (restrictIndex_uniform Q q))) M hM
    rw [models_iff, targetPreservationSentence_eval] at htM
    rw [models_iff, uniformSentence_eval] at hnM hsM ⊢
    intro x y
    have hnorm :
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] ∧
          (memberFormula R).val.Evalb ![y] :=
      (hnM x y).trans (normalizedGraph_eval Q R q x y)
    have hres :
        (eventualGraph (restrictIndex Q q)).val.Evalb ![x, y] ↔
          (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] :=
      (hsM x y).trans (sourceRestrictedGraph_eval Q q x y)
    constructor
    · exact fun hn => hres.mpr ⟨(hnorm.mp hn).1, (hnorm.mp hn).2.1⟩
    · intro hs
      obtain ⟨hQ, hq⟩ := hres.mp hs
      exact hnorm.mpr ⟨hQ, hq, htM x y ⟨hQ, hq⟩⟩

/-- PA proves that every normalized index has the declared source and target
support. -/
theorem pa_proves_normalized_support
    (Q R : STObjectCode) (q : ℕ) :
    𝗣𝗔 ⊢ supportSentence Q R (normalizeIndex Q R q) := by
  exact (proves_support_iff_eqIndex_normalize 𝗣𝗔 Q R
    (normalizeIndex Q R q)).mpr (normalizeIndex_idempotent Q R q)

/-! ## The split-idempotent category -/

/-- The quotient idempotent representing a coded object. -/
def objectIdempotent (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : STObjectCode) : ProgramQuotient T :=
  classOf T (deltaIndex Q)

@[simp] theorem objectIdempotent_mul_self
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    objectIdempotent T Q * objectIdempotent T Q = objectIdempotent T Q := by
  rw [objectIdempotent, mul_classOf, classOf_eq_classOf_iff]
  exact deltaIndex_comp_self_in T Q

@[simp] theorem objectIdempotent_omega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    objectIdempotent T .omega = 1 := by
  rw [objectIdempotent, one_eq_classOf, classOf_eq_classOf_iff]
  exact deltaIndex_omega_eq_identity_in T

/-- A type wrapper for coded objects, used to keep the category instance for a
fixed object theory local to that theory. -/
def CodedProgramCategory (_T : ArithmeticTheory) := STObjectCode

/-- Regard a coded object as an object of the typed program category. -/
def object (T : ArithmeticTheory) (Q : STObjectCode) : CodedProgramCategory T := Q

/-- Recover the coded object expression underlying a typed-category object. -/
def objectCode {T : ArithmeticTheory} (Q : CodedProgramCategory T) : STObjectCode := Q

@[simp] theorem objectCode_object (T : ArithmeticTheory) (Q : STObjectCode) :
    objectCode (object T Q) = Q :=
  rfl

/-- A morphism fixed by the target idempotent on the left and by the source
idempotent on the right. -/
def CodedHom (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :=
  {a : ProgramQuotient T //
    objectIdempotent T (objectCode R) * a = a ∧
      a * objectIdempotent T (objectCode Q) = a}

/-- Two typed morphisms are equal when their underlying quotient classes are
equal. -/
@[ext] theorem CodedHom.ext
    {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} {f g : CodedHom T Q R}
    (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- The category obtained by splitting the selected coded-object idempotents
inside `ProgramQuotient T`. -/
instance codedProgramCategoryCategory
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : Category (CodedProgramCategory T) where
  Hom := CodedHom T
  id Q := ⟨objectIdempotent T (objectCode Q),
    objectIdempotent_mul_self T _, objectIdempotent_mul_self T _⟩
  comp {Q _ S} f g :=
    ⟨g.1 * f.1,
      by
        calc
          objectIdempotent T (objectCode S) * (g.1 * f.1) =
              (objectIdempotent T (objectCode S) * g.1) * f.1 :=
            (mul_assoc _ _ _).symm
          _ = g.1 * f.1 := by rw [g.2.1],
      by
        calc
          (g.1 * f.1) * objectIdempotent T (objectCode Q) =
              g.1 * (f.1 * objectIdempotent T (objectCode Q)) :=
            mul_assoc _ _ _
          _ = g.1 * f.1 := by rw [f.2.2]⟩
  id_comp f := CodedHom.ext f.2.2
  comp_id f := CodedHom.ext f.2.1
  assoc f g h := CodedHom.ext (mul_assoc h.1 g.1 f.1).symm

@[simp] theorem id_val
    {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    (𝟙 Q : Q ⟶ Q).1 = objectIdempotent T (objectCode Q) :=
  rfl

@[simp] theorem comp_val
    {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {Q R S : CodedProgramCategory T} (f : Q ⟶ R) (g : R ⟶ S) :
    (f ≫ g).1 = g.1 * f.1 :=
  rfl

/-- The canonical typed arrow represented by the normalized program `q`. -/
def arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) : object T Q ⟶ object T R :=
  ⟨objectIdempotent T R * classOf T q * objectIdempotent T Q,
    by
      change objectIdempotent T R *
          (objectIdempotent T R * classOf T q * objectIdempotent T Q) =
        objectIdempotent T R * classOf T q * objectIdempotent T Q
      simp only [← mul_assoc, objectIdempotent_mul_self],
    by
      calc
        (objectIdempotent T R * classOf T q * objectIdempotent T Q) *
              objectIdempotent T Q =
            objectIdempotent T R * classOf T q *
              (objectIdempotent T Q * objectIdempotent T Q) := by
          rw [mul_assoc]
        _ = objectIdempotent T R * classOf T q * objectIdempotent T Q := by
          rw [objectIdempotent_mul_self]⟩

/-- The underlying class of `arrowOfIndex` is represented by the explicit
source-target normalizer. -/
theorem arrowOfIndex_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    (arrowOfIndex T Q R q).1 = classOf T (normalizeIndex Q R q) := by
  change (classOf T (deltaIndex R) * classOf T q) *
      classOf T (deltaIndex Q) =
    classOf T (compIndex (deltaIndex R) (compIndex q (deltaIndex Q)))
  rw [mul_assoc, mul_classOf, mul_classOf]

/-- A raw representative whose quotient class is the underlying class of an
arrow reconstructs that arrow through `arrowOfIndex`. -/
theorem arrowOfIndex_eq_of_class
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) (f : object T Q ⟶ object T R)
    (h : classOf T q = f.1) :
    arrowOfIndex T Q R q = f := by
  apply CodedHom.ext
  change objectIdempotent T R * classOf T q * objectIdempotent T Q = f.1
  have ht : objectIdempotent T R * f.1 = f.1 := by
    simpa only [objectCode_object] using f.2.1
  have hs : f.1 * objectIdempotent T Q = f.1 := by
    simpa only [objectCode_object] using f.2.2
  rw [h, ht, hs]

/-- Every typed arrow is obtained from an external production index. -/
theorem exists_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (f : object T Q ⟶ object T R) :
    ∃ q : ℕ, arrowOfIndex T Q R q = f := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep f.1
  exact ⟨q, arrowOfIndex_eq_of_class T Q R q f hq⟩

/-- Equality of canonical typed arrows is exactly global uniform equality of
their normalized production programs. -/
theorem arrowOfIndex_eq_iff_eqIndex_normalize
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q r : ℕ) :
    arrowOfIndex T Q R q = arrowOfIndex T Q R r ↔
      EqIndex T (normalizeIndex Q R q) (normalizeIndex Q R r) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [arrowOfIndex_val, arrowOfIndex_val] at hv
    exact (classOf_eq_classOf_iff T _ _).mp hv
  · intro h
    apply CodedHom.ext
    rw [arrowOfIndex_val, arrowOfIndex_val]
    exact (classOf_eq_classOf_iff T _ _).mpr h

/-- Composition is represented by composing the already normalized outer and
inner indices. -/
theorem arrowOfIndex_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S : STObjectCode) (q r : ℕ) :
    arrowOfIndex T Q R q ≫ arrowOfIndex T R S r =
      arrowOfIndex T Q S
        (compIndex (normalizeIndex R S r) (normalizeIndex Q R q)) := by
  symm
  apply arrowOfIndex_eq_of_class
  rw [comp_val, arrowOfIndex_val, arrowOfIndex_val, mul_classOf]

/-- The omega object in the typed program category. -/
def omegaObject (T : ArithmeticTheory) : CodedProgramCategory T :=
  object T .omega

/-- Omega endomorphisms are exactly the original untyped program quotient. -/
def omegaEndEquiv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (omegaObject T ⟶ omegaObject T) ≃ ProgramQuotient T where
  toFun f := f.1
  invFun a := ⟨a, by simp [omegaObject]⟩
  left_inv f := CodedHom.ext rfl
  right_inv _ := rfl

/-- Under `omegaEndEquiv`, the categorical identity is the quotient unit. -/
@[simp] theorem omegaEndEquiv_id
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaEndEquiv T (𝟙 (omegaObject T)) = 1 := by
  change objectIdempotent T .omega = 1
  exact objectIdempotent_omega T

/-- Diagrammatic composition of omega endomorphisms becomes quotient
multiplication with the later morphism on the left. -/
@[simp] theorem omegaEndEquiv_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f g : omegaObject T ⟶ omegaObject T) :
    omegaEndEquiv T (f ≫ g) = omegaEndEquiv T g * omegaEndEquiv T f :=
  rfl

/-! ## Numerical equality and closed computations -/

/-- The numerical proof predicate for equality of normalized typed
representatives. -/
def ArrowPrfEq
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Q R : STObjectCode) (p q r : ℕ) : Prop :=
  PrfEq T hRE p (normalizeIndex Q R q) (normalizeIndex Q R r)

/-- Typed-arrow equality is exactly existence of a numerical proof of global
uniform equality between the normalized indices. -/
theorem arrowOfIndex_eq_iff_exists_prfEq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Q R : STObjectCode) (q r : ℕ) :
    arrowOfIndex T Q R q = arrowOfIndex T Q R r ↔
      ∃ p : ℕ, ArrowPrfEq T hRE Q R p q r := by
  rw [arrowOfIndex_eq_iff_eqIndex_normalize]
  change EqIndex T (normalizeIndex Q R q) (normalizeIndex Q R r) ↔
    ∃ p : ℕ, PrfEq T hRE p (normalizeIndex Q R q) (normalizeIndex Q R r)
  exact (classOf_eq_classOf_iff T _ _).symm.trans
    (classOf_eq_classOf_iff_exists_prfEq T hRE _ _)

/-- For fixed objects and a selected r.e. presentation of `T`, the numerical
typed-equality proof predicate is primitive recursive. -/
theorem primrecPred_arrowPrfEq
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Q R : STObjectCode) :
    PrimrecPred (fun z : (ℕ × ℕ) × ℕ =>
      ArrowPrfEq T hRE Q R z.1.1 z.1.2 z.2) := by
  have hArgs : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      ((z.1.1, normalizeIndex Q R z.1.2), normalizeIndex Q R z.2)) :=
    ((Primrec.fst.comp Primrec.fst).pair
      ((primrec_normalizeIndex Q R).comp (Primrec.snd.comp Primrec.fst))).pair
      ((primrec_normalizeIndex Q R).comp Primrec.snd)
  simpa [ArrowPrfEq] using (primrecPred_prfEq T hRE).comp hArgs

/-- Provable computation of the quotient class underlying a typed arrow. -/
def ArrowProvableAt
    {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) (n m : ℕ) : Prop :=
  ProvableAt T f.1 n m

/-- PA proves the closed partial-identity graph at every accepted member
numeral. -/
theorem pa_proves_objectIdentityGraph_of_member
    (Q : STObjectCode) (n : ℕ) (h : Q.member n = true) :
    𝗣𝗔 ⊢ (objectIdentityGraph Q).val/[n, n] := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  have hm := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_member_of_true Q n h)) M hM
  rw [models_iff, memberFormula_instance_eval] at hm
  rw [models_iff, graph_instance_eval, objectIdentityGraph_eval]
  exact ⟨by simpa only [numeral_eq_natCast] using hm, rfl⟩

/-- The identity arrow at `Q` has a provable computation from every actual
member numeral to itself. -/
theorem identityArrow_provableAt_of_member
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : STObjectCode) (n : ℕ) (h : Q.member n = true) :
    ArrowProvableAt (T := T) (𝟙 (object T Q)) n n := by
  change ProvableAt T (classOf T (deltaIndex Q)) n n
  rw [provableAt_classOf]
  apply (uniform_instance_provable_iff
    (WeakerThan.pbl (deltaIndex_uniform Q)) n n).mpr
  exact WeakerThan.pbl (pa_proves_objectIdentityGraph_of_member Q n h)

/-- With an r.e. presentation of `T`, the same identity computation has a
proof at the accepted right-instance graph tag. -/
theorem exists_identityArrow_rightProof_of_member
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Q : STObjectCode) (n : ℕ) (h : Q.member n = true) :
    ∃ p : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (rightInstanceCode (deltaIndex Q) n n) := by
  apply (provableAt_classOf_iff_exists_rightProof
    T hRE (deltaIndex Q) n n).mp
  exact identityArrow_provableAt_of_member T Q n h

/-- PA refutes every closed graph instance of an object identity at a numeral
rejected by the external membership test. -/
theorem pa_proves_not_deltaGraph_of_not_member
    (Q : STObjectCode) (n m : ℕ) (h : Q.member n = false) :
    𝗣𝗔 ⊢ ∼(eventualGraph (deltaIndex Q)).val/[n, m] := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  have hn := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_not_member_of_false Q n h)) M hM
  rw [models_iff] at hn ⊢
  simp only [LogicalConnective.HomClass.map_neg, memberFormula_instance_eval,
    graph_instance_eval] at hn ⊢
  intro hg
  apply hn
  have hmem := (eventualGraph_deltaIndex_eval Q
    (ORingStructure.numeral n : M) (ORingStructure.numeral m : M)).mp hg |>.1
  simpa only [numeral_eq_natCast] using hmem

/-- The selected identity graph for a coproduct rejects the explicit invalid
tag `2`, in every theory whose provability includes PA. -/
theorem proves_not_coproductIdentity_invalidTag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (u : ℕ) :
    T ⊢ ∼(eventualGraph (deltaIndex (.coproduct Q R))).val/[
      Nat.pair u 2, Nat.pair u 2] := by
  apply WeakerThan.pbl (𝓢 := 𝗣𝗔)
  apply pa_proves_not_deltaGraph_of_not_member
  exact member_coproductCode_eq_false_of_tag_ne Q R u 2 (by omega) (by omega)

end

end FailureOfComposition.TypedProgramCategory
