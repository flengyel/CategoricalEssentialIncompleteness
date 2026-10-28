/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProgramGraph
import FailureOfComposition.TypedProgramCategory
import PCats.PCat

/-!
# The near product on the typed program category

This file equips `CodedProgramCategory T` with the maintained `P`-category
structure.  The numerical operations are the encodings of explicit
`Nat.Partrec.Code` constructors.  Consequently, their effectiveness does not
depend on the external choices used to realize coded-object restrictions.

The near product of coded objects is `STObjectCode.product`.  On arrows it is
computed by running the two normalized representatives on the two coordinates
of the input.  The restriction induced by this near product is identified with
the partial identity on the computation domain of the normalized arrow.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedNearProduct

open CodedObjectMembership ConcreteEvaluator ProgramGraph ProofSearch
open TypedProgramCategory UniformIndexQuotient

noncomputable section

abbrev PCode := Nat.Partrec.Code

/-! ## Effective numerical constructors -/

/-- The index of the program that pairs the outputs of `q` and `r` on a common
input.  This is the encoding of the actual `Nat.Partrec.Code.pair`
constructor. -/
def pairIndex (q r : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.pair
    (Denumerable.ofNat PCode q) (Denumerable.ofNat PCode r))

/-- The index of the program that applies `q` to the left input coordinate,
applies `r` to the right coordinate, and pairs the two outputs. -/
def tensorIndex (q r : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.pair
    (Nat.Partrec.Code.comp (Denumerable.ofNat PCode q) Nat.Partrec.Code.left)
    (Nat.Partrec.Code.comp (Denumerable.ofNat PCode r) Nat.Partrec.Code.right))

/-- The index of the partial identity whose domain is the computation domain
of `q`. -/
def domainIndex (q : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.comp Nat.Partrec.Code.left
    (Nat.Partrec.Code.pair Nat.Partrec.Code.id (Denumerable.ofNat PCode q)))

/-- The effective diagonal program. -/
def diagonalIndex : ℕ := pairIndex Kleene.identityIndex Kleene.identityIndex

/-- The effective first projection program. -/
def firstProjectionIndex : ℕ := encode Nat.Partrec.Code.left

/-- The effective second projection program. -/
def secondProjectionIndex : ℕ := encode Nat.Partrec.Code.right

@[simp] theorem pairIndex_eq_canonical (q r : ℕ) :
    pairIndex q r = canonicalPartrecPairIndex q r := by
  simp only [pairIndex, encode_pair_eq, Denumerable.encode_ofNat]

@[simp] theorem tensorIndex_eq_canonical (q r : ℕ) :
    tensorIndex q r = pairIndex (compIndex q firstProjectionIndex)
      (compIndex r secondProjectionIndex) := by
  simp only [tensorIndex, pairIndex, firstProjectionIndex, secondProjectionIndex,
    compIndex, canonicalPartrecCompIndex, Denumerable.ofNat_encode]

@[simp] theorem domainIndex_eq_canonical (q : ℕ) :
    domainIndex q = compIndex firstProjectionIndex
      (pairIndex Kleene.identityIndex q) := by
  simp only [domainIndex, pairIndex, firstProjectionIndex, compIndex,
    canonicalPartrecCompIndex, Kleene.identityIndex, Denumerable.ofNat_encode]

/-- Pairing is primitive recursive in its two numerical program indices. -/
theorem primrec₂_pairIndex : Primrec₂ pairIndex := by
  have hp : Primrec₂ (fun q r : ℕ => Nat.pair q r) := Primrec₂.natPair
  have hmul : Primrec₂ (fun q r : ℕ => 4 * Nat.pair q r) :=
    Primrec.nat_mul.comp (Primrec.const 4) hp
  have hadd : Primrec₂ (fun q r : ℕ => 4 * Nat.pair q r + 4) :=
    Primrec.nat_add.comp hmul (Primrec.const 4)
  apply hadd.of_eq
  intro q r
  rw [pairIndex_eq_canonical, canonicalPartrecPairIndex_eq]

/-- Tensoring is primitive recursive in its two numerical program indices. -/
theorem primrec₂_tensorIndex : Primrec₂ tensorIndex := by
  rw [show tensorIndex = fun q r => pairIndex
      (compIndex q firstProjectionIndex) (compIndex r secondProjectionIndex) by
    funext q r
    exact tensorIndex_eq_canonical q r]
  exact primrec₂_pairIndex.comp
    (primrec₂_compIndex.comp Primrec.fst (Primrec.const firstProjectionIndex))
    (primrec₂_compIndex.comp Primrec.snd (Primrec.const secondProjectionIndex))

/-- Taking the computation-domain partial identity is primitive recursive in
the numerical program index. -/
theorem primrec_domainIndex : Primrec domainIndex := by
  rw [show domainIndex = fun q => compIndex firstProjectionIndex
      (pairIndex Kleene.identityIndex q) by
    funext q
    exact domainIndex_eq_canonical q]
  exact primrec₂_compIndex.comp (Primrec.const firstProjectionIndex)
    (primrec₂_pairIndex.comp (Primrec.const Kleene.identityIndex) Primrec.id)

/-! ## Graphs and their PA-uniform semantics -/

/-- The graph obtained by pairing the outputs of `q` and `r` on a common
input.  Variables are input and output, in that order. -/
def pairGraph (q r : ℕ) : Graph :=
  .mkSigma “x z. ∃ y, ∃ w,
    !(eventualGraph q).val x y ∧ !(eventualGraph r).val x w ∧
      !natPairFormula.val z y w”

/-- The graph of the tensor program on an arbitrary encoded input pair. -/
def tensorGraph (q r : ℕ) : Graph :=
  .mkSigma “s z. ∃ x, ∃ u, ∃ y, ∃ v,
    !natPairFormula.val s x u ∧ !(eventualGraph q).val x y ∧
      !(eventualGraph r).val u v ∧ !natPairFormula.val z y v”

/-- The graph of the partial identity on the computation domain of `q`. -/
def domainGraph (q : ℕ) : Graph :=
  .mkSigma “x y. y = x ∧ ∃ z, !(eventualGraph q).val x z”

@[simp] theorem pairGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x z : M) :
    (pairGraph q r).val.Evalb ![x, z] ↔
      ∃ y w : M, (eventualGraph q).val.Evalb ![x, y] ∧
        (eventualGraph r).val.Evalb ![x, w] ∧ z = pair y w := by
  simp [pairGraph]

@[simp] theorem tensorGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (s z : M) :
    (tensorGraph q r).val.Evalb ![s, z] ↔
      ∃ x u y v : M, s = pair x u ∧
        (eventualGraph q).val.Evalb ![x, y] ∧
        (eventualGraph r).val.Evalb ![u, v] ∧ z = pair y v := by
  simp [tensorGraph]

@[simp] theorem domainGraph_eval
    {M : Type*} [ORingStructure M] (q : ℕ) (x y : M) :
    (domainGraph q).val.Evalb ![x, y] ↔
      y = x ∧ ∃ z : M, (eventualGraph q).val.Evalb ![x, z] := by
  simp [domainGraph]

private noncomputable instance modelISigmaOne
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance

/-- The pairing constructor has the stated graph in every model of PA. -/
@[simp] theorem eventualGraph_pairIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x z : M) :
    (eventualGraph (pairIndex q r)).val.Evalb ![x, z] ↔
      ∃ y w : M, (eventualGraph q).val.Evalb ![x, y] ∧
        (eventualGraph r).val.Evalb ![x, w] ∧ z = pair y w := by
  rw [pairIndex_eq_canonical]
  exact eventualGraph_pair_eval q r x z

/-- The tensor constructor has the stated graph on arbitrary inputs. -/
@[simp] theorem eventualGraph_tensorIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (s z : M) :
    (eventualGraph (tensorIndex q r)).val.Evalb ![s, z] ↔
      ∃ y v : M, (eventualGraph q).val.Evalb ![pi₁ s, y] ∧
        (eventualGraph r).val.Evalb ![pi₂ s, v] ∧ z = pair y v := by
  change Computes
      (.pair (.comp (Denumerable.ofNat PCode q) .left)
        (.comp (Denumerable.ofNat PCode r) .right)) s z ↔ _
  rw [computes_pair]
  constructor
  · rintro ⟨y, v, hq, hr, rfl⟩
    change Computes (.comp (Denumerable.ofNat PCode q) .left) s y at hq
    change Computes (.comp (Denumerable.ofNat PCode r) .right) s v at hr
    rw [computes_comp] at hq hr
    obtain ⟨a, ha, hq⟩ := hq
    obtain ⟨b, hb, hr⟩ := hr
    have ha' : a = pi₁ s := (computes_left s a).mp ha
    have hb' : b = pi₂ s := (computes_right s b).mp hb
    subst a
    subst b
    exact ⟨y, v, by simpa only [Computes, Denumerable.encode_ofNat] using hq,
      by simpa only [Computes, Denumerable.encode_ofNat] using hr, rfl⟩
  · rintro ⟨y, v, hq, hr, rfl⟩
    refine ⟨y, v, ?_, ?_, rfl⟩
    · apply (computes_comp _ _ _ _).mpr
      exact ⟨pi₁ s, (computes_left s _).mpr rfl,
        by simpa only [Computes, Denumerable.encode_ofNat] using hq⟩
    · apply (computes_comp _ _ _ _).mpr
      exact ⟨pi₂ s, (computes_right s _).mpr rfl,
        by simpa only [Computes, Denumerable.encode_ofNat] using hr⟩

/-- General-input graph law for tensoring, phrased with the arithmetic pairing
graph shared with coded-object membership. -/
@[simp] theorem eventualGraph_tensorIndex_iff_tensorGraph
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (s z : M) :
    (eventualGraph (tensorIndex q r)).val.Evalb ![s, z] ↔
      (tensorGraph q r).val.Evalb ![s, z] := by
  rw [eventualGraph_tensorIndex_eval, tensorGraph_eval]
  constructor
  · rintro ⟨y, v, hq, hr, rfl⟩
    exact ⟨pi₁ s, pi₂ s, y, v, pair_unpair s |>.symm, hq, hr, rfl⟩
  · rintro ⟨x, u, y, v, rfl, hq, hr, rfl⟩
    simpa only [pi₁_pair, pi₂_pair] using ⟨y, v, hq, hr, rfl⟩

/-- Paired-input specialization of the tensor graph law. -/
@[simp] theorem eventualGraph_tensorIndex_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x u y v : M) :
    (eventualGraph (tensorIndex q r)).val.Evalb
        ![pair x u, pair y v] ↔
      (eventualGraph q).val.Evalb ![x, y] ∧
        (eventualGraph r).val.Evalb ![u, v] := by
  rw [eventualGraph_tensorIndex_eval]
  simp only [pi₁_pair, pi₂_pair]
  constructor
  · rintro ⟨a, b, hq, hr, hab⟩
    obtain ⟨hay, hbv⟩ := (pair_eq_pair_iff y v a b).mp hab
    simpa only [hay, hbv] using ⟨hq, hr⟩
  · rintro ⟨hq, hr⟩
    exact ⟨y, v, hq, hr, rfl⟩

/-- The domain constructor has the graph of a partial identity in every model
of PA. -/
@[simp] theorem eventualGraph_domainIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (x y : M) :
    (eventualGraph (domainIndex q)).val.Evalb ![x, y] ↔
      y = x ∧ ∃ z : M, (eventualGraph q).val.Evalb ![x, z] := by
  change Computes
      (.comp .left (.pair .id (Denumerable.ofNat PCode q))) x y ↔ _
  rw [computes_comp]
  constructor
  · rintro ⟨w, hw, hy⟩
    obtain ⟨a, z, ha, hq, rfl⟩ := (computes_pair _ _ _ _).mp hw
    have hax : a = x := (computes_id x a).mp ha
    subst a
    have hyx : y = x := by
      simpa only [pi₁_pair] using (computes_left (pair x z) y).mp hy
    exact ⟨hyx, z,
      by simpa only [Computes, Denumerable.encode_ofNat] using hq⟩
  · rintro ⟨hyx, z, hq⟩
    subst y
    refine ⟨pair x z, ?_, (computes_left _ _).mpr (by simp only [pi₁_pair])⟩
    apply (computes_pair _ _ _ _).mpr
    exact ⟨x, z, (computes_id _ _).mpr rfl,
      by simpa only [Computes, Denumerable.encode_ofNat] using hq, rfl⟩

/-- PA proves the pairing graph law uniformly. -/
theorem pairIndex_uniform (q r : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (pairIndex q r)) (pairGraph q r) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x z
  exact (eventualGraph_pairIndex_eval q r x z).trans
    (pairGraph_eval q r x z).symm

/-- PA proves the general-input tensor graph law uniformly. -/
theorem tensorIndex_uniform (q r : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (tensorIndex q r)) (tensorGraph q r) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  exact eventualGraph_tensorIndex_iff_tensorGraph q r

/-- PA proves the computation-domain graph law uniformly. -/
theorem domainIndex_uniform (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (domainIndex q)) (domainGraph q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  exact (eventualGraph_domainIndex_eval q x y).trans
    (domainGraph_eval q x y).symm

/-! ## Congruence for uniform graph equality -/

/-- The production identity has its expected graph in every model of PA. -/
@[simp] theorem eventualGraph_identityIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph Kleene.identityIndex).val.Evalb ![x, y] ↔ y = x := by
  simpa only [Computes, Kleene.identityIndex] using
    (computes_id (M := M) x y)

/-- The first projection index has its expected graph in every model of PA. -/
@[simp] theorem eventualGraph_firstProjectionIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph firstProjectionIndex).val.Evalb ![x, y] ↔
      y = pi₁ x := by
  simpa only [Computes, firstProjectionIndex] using
    (computes_left (M := M) x y)

/-- The second projection index has its expected graph in every model of PA. -/
@[simp] theorem eventualGraph_secondProjectionIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph secondProjectionIndex).val.Evalb ![x, y] ↔
      y = pi₂ x := by
  simpa only [Computes, secondProjectionIndex] using
    (computes_right (M := M) x y)

/-- Pairing respects uniform `T`-provable graph equality. -/
theorem eqIndex_pair_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {q q' r r' : ℕ} (hq : EqIndex T q q') (hr : EqIndex T r r') :
    EqIndex T (pairIndex q r) (pairIndex q' r') := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hq' := consequence_iff.mp (Theory.Proof.sound hq) M hM
  have hr' := consequence_iff.mp (Theory.Proof.sound hr) M hM
  simp only [models_iff, uniformSentence_eval] at hq' hr' ⊢
  intro x z
  rw [eventualGraph_pairIndex_eval, eventualGraph_pairIndex_eval]
  exact exists_congr fun y => exists_congr fun w =>
    and_congr (hq' x y) (and_congr (hr' x w) Iff.rfl)

/-- Tensoring respects uniform `T`-provable graph equality. -/
theorem eqIndex_tensor_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {q q' r r' : ℕ} (hq : EqIndex T q q') (hr : EqIndex T r r') :
    EqIndex T (tensorIndex q r) (tensorIndex q' r') := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hq' := consequence_iff.mp (Theory.Proof.sound hq) M hM
  have hr' := consequence_iff.mp (Theory.Proof.sound hr) M hM
  simp only [models_iff, uniformSentence_eval] at hq' hr' ⊢
  intro x z
  rw [eventualGraph_tensorIndex_eval, eventualGraph_tensorIndex_eval]
  exact exists_congr fun y => exists_congr fun w =>
    and_congr (hq' (pi₁ x) y) (and_congr (hr' (pi₂ x) w) Iff.rfl)

/-- Taking a computation domain respects uniform `T`-provable graph
equality. -/
theorem eqIndex_domain_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {q r : ℕ} (h : EqIndex T q r) :
    EqIndex T (domainIndex q) (domainIndex r) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
  simp only [models_iff, uniformSentence_eval] at h' ⊢
  intro x y
  rw [eventualGraph_domainIndex_eval, eventualGraph_domainIndex_eval]
  exact and_congr Iff.rfl (exists_congr fun z => h' x z)

/-! ## Operations on quotient classes -/

/-- Pair two quotient programs on a common input. -/
def pairClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T → ProgramQuotient T → ProgramQuotient T :=
  Quotient.lift₂
    (fun q r => classOf T (pairIndex q r))
    (fun _ _ _ _ hq hr => Quotient.sound (eqIndex_pair_congr T hq hr))

/-- Tensor two quotient programs, using the two input coordinates. -/
def tensorClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T → ProgramQuotient T → ProgramQuotient T :=
  Quotient.lift₂
    (fun q r => classOf T (tensorIndex q r))
    (fun _ _ _ _ hq hr => Quotient.sound (eqIndex_tensor_congr T hq hr))

/-- Take the computation-domain partial identity of a quotient program. -/
def domainClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T → ProgramQuotient T :=
  Quotient.lift
    (fun q => classOf T (domainIndex q))
    (fun _ _ h => Quotient.sound (eqIndex_domain_congr T h))

@[simp] theorem pairClass_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    pairClass T (classOf T q) (classOf T r) =
      classOf T (pairIndex q r) :=
  rfl

@[simp] theorem tensorClass_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    tensorClass T (classOf T q) (classOf T r) =
      classOf T (tensorIndex q r) :=
  rfl

@[simp] theorem domainClass_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    domainClass T (classOf T q) = classOf T (domainIndex q) :=
  rfl

/-! ## Algebra of the tensor programs -/

/-- Tensoring the two production identities is uniformly the production
identity. -/
theorem eqIndex_tensor_identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (tensorIndex Kleene.identityIndex Kleene.identityIndex)
      Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_tensorIndex_eval, eventualGraph_identityIndex_eval]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    have ha' : a = pi₁ x := (eventualGraph_identityIndex_eval _ _).mp ha
    have hb' : b = pi₂ x := (eventualGraph_identityIndex_eval _ _).mp hb
    rw [ha', hb']
    exact pair_unpair x
  · intro hyx
    subst y
    exact ⟨pi₁ x, pi₂ x,
      (eventualGraph_identityIndex_eval _ _).mpr rfl,
      (eventualGraph_identityIndex_eval _ _).mpr rfl,
      (pair_unpair x).symm⟩

@[simp] theorem tensorClass_one_one
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    tensorClass T (1 : ProgramQuotient T) 1 = 1 := by
  change tensorClass T (classOf T Kleene.identityIndex)
      (classOf T Kleene.identityIndex) = classOf T Kleene.identityIndex
  rw [tensorClass_classOf, classOf_eq_classOf_iff]
  exact eqIndex_tensor_identity T

/-- Tensoring commutes with program composition.  In each `compIndex`, the
right-hand argument is executed first. -/
theorem eqIndex_tensor_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b c d : ℕ) :
    EqIndex T (tensorIndex (compIndex a b) (compIndex c d))
      (compIndex (tensorIndex a c) (tensorIndex b d)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x z
  constructor
  · intro h
    obtain ⟨y, v, hy, hv, rfl⟩ :=
      (eventualGraph_tensorIndex_eval _ _ _ _).mp h
    obtain ⟨u, hbu, hay⟩ := (eventualGraph_comp_eval a b _ _).mp hy
    obtain ⟨w, hdw, hcv⟩ := (eventualGraph_comp_eval c d _ _).mp hv
    apply (eventualGraph_comp_eval _ _ _ _).mpr
    refine ⟨pair u w, ?_, ?_⟩
    · exact (eventualGraph_tensorIndex_eval b d x _).mpr
        ⟨u, w, hbu, hdw, rfl⟩
    · apply (eventualGraph_tensorIndex_eval a c _ _).mpr
      exact ⟨y, v, by simpa only [pi₁_pair] using hay,
        by simpa only [pi₂_pair] using hcv, rfl⟩
  · intro h
    obtain ⟨p, hp, hz⟩ := (eventualGraph_comp_eval _ _ _ _).mp h
    obtain ⟨u, w, hbu, hdw, hp'⟩ :=
      (eventualGraph_tensorIndex_eval b d x p).mp hp
    obtain ⟨y, v, hay, hcv, hz'⟩ :=
      (eventualGraph_tensorIndex_eval a c p z).mp hz
    subst p
    simp only [pi₁_pair, pi₂_pair] at hay hcv
    apply (eventualGraph_tensorIndex_eval _ _ _ _).mpr
    exact ⟨y, v, (eventualGraph_comp_eval a b _ _).mpr ⟨u, hbu, hay⟩,
      (eventualGraph_comp_eval c d _ _).mpr ⟨w, hdw, hcv⟩, hz'⟩

/-- Tensoring quotient programs is multiplicative in both variables. -/
theorem tensorClass_mul
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b c d : ProgramQuotient T) :
    tensorClass T (a * b) (c * d) =
      tensorClass T a c * tensorClass T b d := by
  refine Quotient.inductionOn a ?_
  intro a
  refine Quotient.inductionOn b ?_
  intro b
  refine Quotient.inductionOn c ?_
  intro c
  refine Quotient.inductionOn d ?_
  intro d
  change classOf T (tensorIndex (compIndex a b) (compIndex c d)) =
    classOf T (compIndex (tensorIndex a c) (tensorIndex b d))
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_tensor_comp T a b c d)

/-! ## Product-object restrictions -/

/-- Tensoring the selected partial identities of `Q` and `R` gives the
selected partial identity of `Q.product R`, modulo uniform PA-provable graph
equality. -/
theorem eqIndex_tensor_delta
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    EqIndex T (tensorIndex (deltaIndex Q) (deltaIndex R))
      (deltaIndex (.product Q R)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨a, b, hQa, hRb, rfl⟩ :=
      (eventualGraph_tensorIndex_eval _ _ _ _).mp h
    obtain ⟨hQ, ha⟩ := (eventualGraph_deltaIndex_eval Q _ _).mp hQa
    obtain ⟨hR, hb⟩ := (eventualGraph_deltaIndex_eval R _ _).mp hRb
    rw [ha, hb]
    apply (eventualGraph_deltaIndex_eval (.product Q R) _ _).mpr
    refine ⟨?_, pair_unpair x⟩
    exact (memberFormula_product_eval Q R x).mpr
      ⟨pi₁ x, pi₂ x, (pair_unpair x).symm, hQ, hR⟩
  · intro h
    obtain ⟨hQR, hyx⟩ :=
      (eventualGraph_deltaIndex_eval (.product Q R) x y).mp h
    obtain ⟨u, v, hx, hQ, hR⟩ :=
      (memberFormula_product_eval Q R x).mp hQR
    have hxu : pi₁ x = u := by rw [hx, pi₁_pair]
    have hxv : pi₂ x = v := by rw [hx, pi₂_pair]
    apply (eventualGraph_tensorIndex_eval _ _ _ _).mpr
    exact ⟨u, v,
      (eventualGraph_deltaIndex_eval Q (pi₁ x) u).mpr
        ⟨by simpa only [hxu] using hQ, hxu.symm⟩,
      (eventualGraph_deltaIndex_eval R (pi₂ x) v).mpr
        ⟨by simpa only [hxv] using hR, hxv.symm⟩,
      hyx.trans hx⟩

/-- The quotient idempotent of a product object is the tensor of the two
factor idempotents. -/
theorem objectIdempotent_product
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    objectIdempotent T (.product Q R) =
      tensorClass T (objectIdempotent T Q) (objectIdempotent T R) := by
  change classOf T (deltaIndex (.product Q R)) =
    tensorClass T (classOf T (deltaIndex Q)) (classOf T (deltaIndex R))
  rw [tensorClass_classOf, classOf_eq_classOf_iff]
  exact eqIndex_symm (eqIndex_tensor_delta T Q R)

/-! ## Typed near-product data -/

/-- Tensor two typed arrows.  Their underlying quotient classes already are
their normalized representatives, and the tensor multiplication laws verify
the source and target support equations. -/
def typedNearProdMap
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y Z : CodedProgramCategory T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    object T (.product (objectCode W) (objectCode Y)) ⟶
      object T (.product (objectCode X) (objectCode Z)) :=
  ⟨tensorClass T f.1 g.1, by
    constructor
    · change objectIdempotent T (.product (objectCode X) (objectCode Z)) *
          tensorClass T f.1 g.1 = tensorClass T f.1 g.1
      rw [objectIdempotent_product, ← tensorClass_mul]
      rw [f.2.1, g.2.1]
    · change tensorClass T f.1 g.1 *
          objectIdempotent T (.product (objectCode W) (objectCode Y)) =
        tensorClass T f.1 g.1
      rw [objectIdempotent_product, ← tensorClass_mul]
      rw [f.2.2, g.2.2]⟩

/-- The typed diagonal at a coded object. -/
def typedDiag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    Q ⟶ object T (.product (objectCode Q) (objectCode Q)) :=
  arrowOfIndex T (objectCode Q) (.product (objectCode Q) (objectCode Q))
    diagonalIndex

/-- The typed first projection. -/
def typedP0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    object T (.product (objectCode Q) (objectCode R)) ⟶ Q :=
  arrowOfIndex T (.product (objectCode Q) (objectCode R)) (objectCode Q)
    firstProjectionIndex

/-- The typed second projection. -/
def typedP1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    object T (.product (objectCode Q) (objectCode R)) ⟶ R :=
  arrowOfIndex T (.product (objectCode Q) (objectCode R)) (objectCode R)
    secondProjectionIndex

/-- The concrete near-product data on the typed program category. -/
instance codedProgramCategoryPCategoryStruct
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PCategoryStruct (CodedProgramCategory T) where
  nearProd Q R := object T (.product (objectCode Q) (objectCode R))
  nearProd_map := typedNearProdMap T
  diag := typedDiag T
  p0 := typedP0 T
  p1 := typedP1 T

open PCategoryStruct

@[simp] theorem nearProd_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    nearProd (object T Q) (object T R) = object T (.product Q R) :=
  rfl

@[simp] theorem objectCode_nearProd
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    objectCode (nearProd Q R) = .product (objectCode Q) (objectCode R) :=
  rfl

@[simp] theorem typedNearProdMap_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y Z : CodedProgramCategory T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    (typedNearProdMap T f g).1 = tensorClass T f.1 g.1 :=
  rfl

/-- Representative equation for the near-product map.  The raw arguments are
normalized before they are tensored. -/
theorem typedNearProdMap_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S U : STObjectCode) (q r : ℕ) :
    typedNearProdMap T (arrowOfIndex T Q R q) (arrowOfIndex T S U r) =
      arrowOfIndex T (.product Q S) (.product R U)
        (tensorIndex (normalizeIndex Q R q) (normalizeIndex S U r)) := by
  symm
  apply arrowOfIndex_eq_of_class
  rw [typedNearProdMap_val, arrowOfIndex_val, arrowOfIndex_val,
    tensorClass_classOf]

@[simp] theorem nearProd_map_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S U : STObjectCode) (q r : ℕ) :
    nearProd_map (arrowOfIndex T Q R q) (arrowOfIndex T S U r) =
      arrowOfIndex T (.product Q S) (.product R U)
        (tensorIndex (normalizeIndex Q R q) (normalizeIndex S U r)) :=
  typedNearProdMap_arrowOfIndex T Q R S U q r

@[simp] theorem diag_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    diag (object T Q) =
      arrowOfIndex T Q (.product Q Q) diagonalIndex :=
  rfl

@[simp] theorem p0_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    p0 (object T Q) (object T R) =
      arrowOfIndex T (.product Q R) Q firstProjectionIndex :=
  rfl

@[simp] theorem p1_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    p1 (object T Q) (object T R) =
      arrowOfIndex T (.product Q R) R secondProjectionIndex :=
  rfl

/-! ## Structural program equations -/

/-- The diagonal program maps `x` to the arithmetic pair of `x` with itself. -/
@[simp] theorem eventualGraph_diagonalIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph diagonalIndex).val.Evalb ![x, y] ↔
      y = pair x x := by
  rw [diagonalIndex, eventualGraph_pairIndex_eval]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [(eventualGraph_identityIndex_eval _ _).mp ha,
      (eventualGraph_identityIndex_eval _ _).mp hb]
  · intro hy
    exact ⟨x, x, (eventualGraph_identityIndex_eval _ _).mpr rfl,
      (eventualGraph_identityIndex_eval _ _).mpr rfl, hy⟩

/-- First projection after program pairing retains the first computation and
requires both computations to be defined. -/
theorem eventualGraph_comp_pair_first_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x y : M) :
    (eventualGraph (compIndex firstProjectionIndex (pairIndex q r))).val.Evalb
        ![x, y] ↔
      ∃ a b : M, (eventualGraph q).val.Evalb ![x, a] ∧
        (eventualGraph r).val.Evalb ![x, b] ∧ y = a := by
  rw [eventualGraph_comp_eval]
  constructor
  · rintro ⟨p, hp, hy⟩
    obtain ⟨a, b, hq, hr, rfl⟩ :=
      (eventualGraph_pairIndex_eval q r x p).mp hp
    exact ⟨a, b, hq, hr,
      (eventualGraph_firstProjectionIndex_eval _ _).mp hy |>.trans (pi₁_pair a b)⟩
  · rintro ⟨a, b, hq, hr, hya⟩
    exact ⟨pair a b, (eventualGraph_pairIndex_eval q r x _).mpr
      ⟨a, b, hq, hr, rfl⟩,
      (eventualGraph_firstProjectionIndex_eval _ _).mpr
        (hya.trans (pi₁_pair a b).symm)⟩

/-- Second projection after program pairing retains the second computation and
requires both computations to be defined. -/
theorem eventualGraph_comp_pair_second_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x y : M) :
    (eventualGraph (compIndex secondProjectionIndex (pairIndex q r))).val.Evalb
        ![x, y] ↔
      ∃ a b : M, (eventualGraph q).val.Evalb ![x, a] ∧
        (eventualGraph r).val.Evalb ![x, b] ∧ y = b := by
  rw [eventualGraph_comp_eval]
  constructor
  · rintro ⟨p, hp, hy⟩
    obtain ⟨a, b, hq, hr, rfl⟩ :=
      (eventualGraph_pairIndex_eval q r x p).mp hp
    exact ⟨a, b, hq, hr,
      (eventualGraph_secondProjectionIndex_eval _ _).mp hy |>.trans (pi₂_pair a b)⟩
  · rintro ⟨a, b, hq, hr, hyb⟩
    exact ⟨pair a b, (eventualGraph_pairIndex_eval q r x _).mpr
      ⟨a, b, hq, hr, rfl⟩,
      (eventualGraph_secondProjectionIndex_eval _ _).mpr
        (hyb.trans (pi₂_pair a b).symm)⟩

/-- First projection after the diagonal is the identity. -/
theorem eqIndex_first_diagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (compIndex firstProjectionIndex diagonalIndex)
      Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval, eventualGraph_identityIndex_eval]
  constructor
  · rintro ⟨p, hp, hy⟩
    rw [(eventualGraph_diagonalIndex_eval _ _).mp hp] at hy
    simpa only [pi₁_pair] using
      (eventualGraph_firstProjectionIndex_eval _ _).mp hy
  · intro hyx
    subst y
    exact ⟨pair x x, (eventualGraph_diagonalIndex_eval _ _).mpr rfl,
      (eventualGraph_firstProjectionIndex_eval _ _).mpr (pi₁_pair x x).symm⟩

/-- Second projection after the diagonal is the identity. -/
theorem eqIndex_second_diagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (compIndex secondProjectionIndex diagonalIndex)
      Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval, eventualGraph_identityIndex_eval]
  constructor
  · rintro ⟨p, hp, hy⟩
    rw [(eventualGraph_diagonalIndex_eval _ _).mp hp] at hy
    simpa only [pi₂_pair] using
      (eventualGraph_secondProjectionIndex_eval _ _).mp hy
  · intro hyx
    subst y
    exact ⟨pair x x, (eventualGraph_diagonalIndex_eval _ _).mpr rfl,
      (eventualGraph_secondProjectionIndex_eval _ _).mpr (pi₂_pair x x).symm⟩

/-- Duplicating an input and then selecting its two coordinates reconstructs
the input. -/
theorem eqIndex_tensor_projections_diagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex (tensorIndex firstProjectionIndex secondProjectionIndex)
        diagonalIndex)
      Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    have hp' : p = pair x x := (eventualGraph_diagonalIndex_eval x p).mp hp
    obtain ⟨a, b, ha, hb, hy'⟩ :=
      (eventualGraph_tensorIndex_eval _ _ p y).mp hy
    rw [hp'] at ha hb
    have ha' : a = pi₁ x := by
      simpa only [pi₁_pair] using
        (eventualGraph_firstProjectionIndex_eval _ _).mp ha
    have hb' : b = pi₂ x := by
      simpa only [pi₂_pair] using
        (eventualGraph_secondProjectionIndex_eval _ _).mp hb
    apply (eventualGraph_identityIndex_eval x y).mpr
    rw [hy', ha', hb', pair_unpair]
  · intro h
    have hyx : y = x := (eventualGraph_identityIndex_eval x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x x, (eventualGraph_diagonalIndex_eval _ _).mpr rfl, ?_⟩
    apply (eventualGraph_tensorIndex_eval _ _ _ _).mpr
    refine ⟨pi₁ x, pi₂ x, ?_, ?_, ?_⟩
    · apply (eventualGraph_firstProjectionIndex_eval _ _).mpr
      simp only [pi₁_pair]
    · apply (eventualGraph_secondProjectionIndex_eval _ _).mpr
      simp only [pi₂_pair]
    · exact hyx.trans (pair_unpair x).symm

/-- Quotient class of the effective diagonal program. -/
def diagonalClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T :=
  classOf T diagonalIndex

/-- Quotient class of the effective first projection. -/
def firstProjectionClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T :=
  classOf T firstProjectionIndex

/-- Quotient class of the effective second projection. -/
def secondProjectionClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T :=
  classOf T secondProjectionIndex

@[simp] theorem firstProjectionClass_mul_diagonalClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    firstProjectionClass T * diagonalClass T = 1 := by
  change classOf T (compIndex firstProjectionIndex diagonalIndex) =
    classOf T Kleene.identityIndex
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_first_diagonal T)

@[simp] theorem secondProjectionClass_mul_diagonalClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    secondProjectionClass T * diagonalClass T = 1 := by
  change classOf T (compIndex secondProjectionIndex diagonalIndex) =
    classOf T Kleene.identityIndex
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_second_diagonal T)

@[simp] theorem tensorProjectionsClass_mul_diagonalClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
      diagonalClass T = 1 := by
  change classOf T
      (compIndex (tensorIndex firstProjectionIndex secondProjectionIndex)
        diagonalIndex) = classOf T Kleene.identityIndex
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_tensor_projections_diagonal T)

/-- The diagonal is natural for every program class. -/
theorem eqIndex_diagonal_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T (compIndex diagonalIndex q)
      (compIndex (tensorIndex q q) diagonalIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x z
  constructor
  · intro h
    obtain ⟨y, hq, hz⟩ := (eventualGraph_comp_eval _ _ x z).mp h
    have hz' : z = pair y y := (eventualGraph_diagonalIndex_eval y z).mp hz
    apply (eventualGraph_comp_eval _ _ x z).mpr
    refine ⟨pair x x, (eventualGraph_diagonalIndex_eval x _).mpr rfl, ?_⟩
    apply (eventualGraph_tensorIndex_eval q q _ z).mpr
    refine ⟨y, y, ?_, ?_, hz'⟩ <;>
      simpa only [pi₁_pair, pi₂_pair] using hq
  · intro h
    obtain ⟨p, hp, hz⟩ := (eventualGraph_comp_eval _ _ x z).mp h
    have hp' : p = pair x x := (eventualGraph_diagonalIndex_eval x p).mp hp
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (eventualGraph_tensorIndex_eval q q p z).mp hz
    rw [hp'] at ha hb
    simp only [pi₁_pair, pi₂_pair] at ha hb
    have hab' : a = b := eventualGraph_output_unique q x a b ha hb
    apply (eventualGraph_comp_eval _ _ x z).mpr
    refine ⟨a, ha, (eventualGraph_diagonalIndex_eval a z).mpr ?_⟩
    simpa only [hab'] using hab

/-- First projection is half-natural for the tensor program. -/
theorem eqIndex_first_tensor_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T
      (compIndex firstProjectionIndex
        (tensorIndex q Kleene.identityIndex))
      (compIndex q firstProjectionIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨a, b, hq, hb, hp'⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x p).mp hp
    have hya : y = a := by
      rw [hp'] at hy
      simpa only [pi₁_pair] using
        (eventualGraph_firstProjectionIndex_eval _ _).mp hy
    apply (eventualGraph_comp_eval q firstProjectionIndex x y).mpr
    exact ⟨pi₁ x, (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl,
      by simpa only [hya] using hq⟩
  · intro h
    obtain ⟨u, hu, hq⟩ :=
      (eventualGraph_comp_eval q firstProjectionIndex x y).mp h
    have hu' : u = pi₁ x :=
      (eventualGraph_firstProjectionIndex_eval x u).mp hu
    apply (eventualGraph_comp_eval firstProjectionIndex _ x y).mpr
    refine ⟨pair y (pi₂ x), ?_,
      (eventualGraph_firstProjectionIndex_eval _ _).mpr (pi₁_pair _ _).symm⟩
    apply (eventualGraph_tensorIndex_eval _ _ x _).mpr
    exact ⟨y, pi₂ x, by simpa only [hu'] using hq,
      (eventualGraph_identityIndex_eval _ _).mpr rfl, rfl⟩

/-- Second projection is half-natural for the tensor program. -/
theorem eqIndex_second_tensor_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T
      (compIndex secondProjectionIndex
        (tensorIndex Kleene.identityIndex q))
      (compIndex q secondProjectionIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨a, b, ha, hq, hp'⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x p).mp hp
    have hyb : y = b := by
      rw [hp'] at hy
      simpa only [pi₂_pair] using
        (eventualGraph_secondProjectionIndex_eval _ _).mp hy
    apply (eventualGraph_comp_eval q secondProjectionIndex x y).mpr
    exact ⟨pi₂ x, (eventualGraph_secondProjectionIndex_eval _ _).mpr rfl,
      by simpa only [hyb] using hq⟩
  · intro h
    obtain ⟨u, hu, hq⟩ :=
      (eventualGraph_comp_eval q secondProjectionIndex x y).mp h
    have hu' : u = pi₂ x :=
      (eventualGraph_secondProjectionIndex_eval x u).mp hu
    apply (eventualGraph_comp_eval secondProjectionIndex _ x y).mpr
    refine ⟨pair (pi₁ x) y, ?_,
      (eventualGraph_secondProjectionIndex_eval _ _).mpr (pi₂_pair _ _).symm⟩
    apply (eventualGraph_tensorIndex_eval _ _ x _).mpr
    exact ⟨pi₁ x, y, (eventualGraph_identityIndex_eval _ _).mpr rfl,
      by simpa only [hu'] using hq, rfl⟩

theorem diagonalClass_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) :
    diagonalClass T * a = tensorClass T a a * diagonalClass T := by
  refine Quotient.inductionOn a ?_
  intro q
  change classOf T (compIndex diagonalIndex q) =
    classOf T (compIndex (tensorIndex q q) diagonalIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_diagonal_natural T q)

theorem firstProjectionClass_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) :
    firstProjectionClass T * tensorClass T a 1 =
      a * firstProjectionClass T := by
  refine Quotient.inductionOn a ?_
  intro q
  change classOf T
      (compIndex firstProjectionIndex (tensorIndex q Kleene.identityIndex)) =
    classOf T (compIndex q firstProjectionIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_first_tensor_natural T q)

theorem secondProjectionClass_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) :
    secondProjectionClass T * tensorClass T 1 a =
      a * secondProjectionClass T := by
  refine Quotient.inductionOn a ?_
  intro q
  change classOf T
      (compIndex secondProjectionIndex (tensorIndex Kleene.identityIndex q)) =
    classOf T (compIndex q secondProjectionIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_second_tensor_natural T q)

/-- The computation domain of the first projection is the total identity. -/
theorem eqIndex_domain_firstProjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (domainIndex firstProjectionIndex) Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_domainIndex_eval, eventualGraph_identityIndex_eval]
  constructor
  · exact And.left
  · intro hyx
    exact ⟨hyx, pi₁ x,
      (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl⟩

/-- The computation domain of the second projection is the total identity. -/
theorem eqIndex_domain_secondProjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (domainIndex secondProjectionIndex) Kleene.identityIndex := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_domainIndex_eval, eventualGraph_identityIndex_eval]
  constructor
  · exact And.left
  · intro hyx
    exact ⟨hyx, pi₂ x,
      (eventualGraph_secondProjectionIndex_eval _ _).mpr rfl⟩

/-- A tensor whose right component is total does not change its first
projection. -/
theorem eqIndex_first_tensor_of_domain
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ)
    (hq : EqIndex T (domainIndex q) Kleene.identityIndex) :
    EqIndex T
      (compIndex firstProjectionIndex
        (tensorIndex Kleene.identityIndex q))
      firstProjectionIndex := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hq' := consequence_iff.mp (Theory.Proof.sound hq) M hM
  simp only [models_iff, uniformSentence_eval] at hq'
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨a, b, ha, hb, hp'⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x p).mp hp
    have ha' : a = pi₁ x := (eventualGraph_identityIndex_eval _ _).mp ha
    have hy' : y = a := by
      rw [hp'] at hy
      simpa only [pi₁_pair] using
        (eventualGraph_firstProjectionIndex_eval _ _).mp hy
    exact (eventualGraph_firstProjectionIndex_eval x y).mpr (hy'.trans ha')
  · intro hy
    have hy' : y = pi₁ x :=
      (eventualGraph_firstProjectionIndex_eval x y).mp hy
    have hid : (eventualGraph Kleene.identityIndex).val.Evalb
        ![pi₂ x, pi₂ x] :=
      (eventualGraph_identityIndex_eval _ _).mpr rfl
    have hdom := (hq' (pi₂ x) (pi₂ x)).mpr hid
    obtain ⟨-, b, hb⟩ := (eventualGraph_domainIndex_eval q _ _).mp hdom
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair (pi₁ x) b, ?_, ?_⟩
    · exact (eventualGraph_tensorIndex_eval _ _ x _).mpr
        ⟨pi₁ x, b, (eventualGraph_identityIndex_eval _ _).mpr rfl,
          hb, rfl⟩
    · exact (eventualGraph_firstProjectionIndex_eval _ _).mpr
        (hy'.trans (pi₁_pair _ _).symm)

/-- A tensor whose left component is total does not change its second
projection. -/
theorem eqIndex_second_tensor_of_domain
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ)
    (hq : EqIndex T (domainIndex q) Kleene.identityIndex) :
    EqIndex T
      (compIndex secondProjectionIndex
        (tensorIndex q Kleene.identityIndex))
      secondProjectionIndex := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hq' := consequence_iff.mp (Theory.Proof.sound hq) M hM
  simp only [models_iff, uniformSentence_eval] at hq'
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨a, b, ha, hb, hp'⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x p).mp hp
    have hb' : b = pi₂ x := (eventualGraph_identityIndex_eval _ _).mp hb
    have hy' : y = b := by
      rw [hp'] at hy
      simpa only [pi₂_pair] using
        (eventualGraph_secondProjectionIndex_eval _ _).mp hy
    exact (eventualGraph_secondProjectionIndex_eval x y).mpr (hy'.trans hb')
  · intro hy
    have hy' : y = pi₂ x :=
      (eventualGraph_secondProjectionIndex_eval x y).mp hy
    have hid : (eventualGraph Kleene.identityIndex).val.Evalb
        ![pi₁ x, pi₁ x] :=
      (eventualGraph_identityIndex_eval _ _).mpr rfl
    have hdom := (hq' (pi₁ x) (pi₁ x)).mpr hid
    obtain ⟨-, a, ha⟩ := (eventualGraph_domainIndex_eval q _ _).mp hdom
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair a (pi₂ x), ?_, ?_⟩
    · exact (eventualGraph_tensorIndex_eval _ _ x _).mpr
        ⟨a, pi₂ x, ha,
          (eventualGraph_identityIndex_eval _ _).mpr rfl, rfl⟩
    · exact (eventualGraph_secondProjectionIndex_eval _ _).mpr
        (hy'.trans (pi₂_pair _ _).symm)

/-- The first projection ignores either total projection in the right tensor
coordinate. -/
theorem eqIndex_first_tensor_first
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex firstProjectionIndex
        (tensorIndex Kleene.identityIndex firstProjectionIndex))
      firstProjectionIndex :=
  eqIndex_first_tensor_of_domain T firstProjectionIndex
    (eqIndex_domain_firstProjection T)

theorem eqIndex_first_tensor_second
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex firstProjectionIndex
        (tensorIndex Kleene.identityIndex secondProjectionIndex))
      firstProjectionIndex :=
  eqIndex_first_tensor_of_domain T secondProjectionIndex
    (eqIndex_domain_secondProjection T)

/-- The second projection ignores either total projection in the left tensor
coordinate. -/
theorem eqIndex_second_tensor_first
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex secondProjectionIndex
        (tensorIndex firstProjectionIndex Kleene.identityIndex))
      secondProjectionIndex :=
  eqIndex_second_tensor_of_domain T firstProjectionIndex
    (eqIndex_domain_firstProjection T)

theorem eqIndex_second_tensor_second
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex secondProjectionIndex
        (tensorIndex secondProjectionIndex Kleene.identityIndex))
      secondProjectionIndex :=
  eqIndex_second_tensor_of_domain T secondProjectionIndex
    (eqIndex_domain_secondProjection T)

@[simp] theorem firstProjectionClass_tensor_first
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    firstProjectionClass T *
      tensorClass T 1 (firstProjectionClass T) = firstProjectionClass T := by
  change classOf T
      (compIndex firstProjectionIndex
        (tensorIndex Kleene.identityIndex firstProjectionIndex)) =
    classOf T firstProjectionIndex
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_first_tensor_first T)

@[simp] theorem firstProjectionClass_tensor_second
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    firstProjectionClass T *
      tensorClass T 1 (secondProjectionClass T) = firstProjectionClass T := by
  change classOf T
      (compIndex firstProjectionIndex
        (tensorIndex Kleene.identityIndex secondProjectionIndex)) =
    classOf T firstProjectionIndex
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_first_tensor_second T)

@[simp] theorem secondProjectionClass_tensor_first
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    secondProjectionClass T *
      tensorClass T (firstProjectionClass T) 1 = secondProjectionClass T := by
  change classOf T
      (compIndex secondProjectionIndex
        (tensorIndex firstProjectionIndex Kleene.identityIndex)) =
    classOf T secondProjectionIndex
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_second_tensor_first T)

@[simp] theorem secondProjectionClass_tensor_second
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    secondProjectionClass T *
      tensorClass T (secondProjectionClass T) 1 = secondProjectionClass T := by
  change classOf T
      (compIndex secondProjectionIndex
        (tensorIndex secondProjectionIndex Kleene.identityIndex)) =
    classOf T secondProjectionIndex
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_second_tensor_second T)

/-! ## Simplified representatives of the typed structural arrows -/

@[simp] theorem diag_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    (diag Q).1 = diagonalClass T * objectIdempotent T (objectCode Q) := by
  change objectIdempotent T
        (.product (objectCode Q) (objectCode Q)) * diagonalClass T *
      objectIdempotent T (objectCode Q) = _
  rw [objectIdempotent_product]
  rw [← diagonalClass_natural]
  rw [mul_assoc, objectIdempotent_mul_self]

@[simp] theorem p0_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    (p0 Q R).1 = firstProjectionClass T *
      objectIdempotent T (.product (objectCode Q) (objectCode R)) := by
  change objectIdempotent T (objectCode Q) * firstProjectionClass T *
      objectIdempotent T (.product (objectCode Q) (objectCode R)) = _
  rw [objectIdempotent_product]
  calc
    (objectIdempotent T (objectCode Q) * firstProjectionClass T) *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) =
        (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Q)) 1) *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) := by
              rw [firstProjectionClass_natural]
    _ = firstProjectionClass T *
          (tensorClass T (objectIdempotent T (objectCode Q)) 1 *
            tensorClass T (objectIdempotent T (objectCode Q))
              (objectIdempotent T (objectCode R))) := by
            rw [mul_assoc]
    _ = firstProjectionClass T *
          tensorClass T
            (objectIdempotent T (objectCode Q) *
              objectIdempotent T (objectCode Q))
            (1 * objectIdempotent T (objectCode R)) := by
          rw [tensorClass_mul]
    _ = firstProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) := by
          rw [objectIdempotent_mul_self, one_mul]

@[simp] theorem p1_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    (p1 Q R).1 = secondProjectionClass T *
      objectIdempotent T (.product (objectCode Q) (objectCode R)) := by
  change objectIdempotent T (objectCode R) * secondProjectionClass T *
      objectIdempotent T (.product (objectCode Q) (objectCode R)) = _
  rw [objectIdempotent_product]
  calc
    (objectIdempotent T (objectCode R) * secondProjectionClass T) *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) =
        (secondProjectionClass T *
            tensorClass T 1 (objectIdempotent T (objectCode R))) *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) := by
              rw [secondProjectionClass_natural]
    _ = secondProjectionClass T *
          (tensorClass T 1 (objectIdempotent T (objectCode R)) *
            tensorClass T (objectIdempotent T (objectCode Q))
              (objectIdempotent T (objectCode R))) := by
            rw [mul_assoc]
    _ = secondProjectionClass T *
          tensorClass T
            (1 * objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R) *
              objectIdempotent T (objectCode R)) := by
          rw [tensorClass_mul]
    _ = secondProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode Q))
            (objectIdempotent T (objectCode R)) := by
          rw [objectIdempotent_mul_self, one_mul]

/-! ## The concrete `P`-category laws -/

theorem typed_nearProd_id
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y : CodedProgramCategory T) :
    nearProd_map (𝟙 X) (𝟙 Y) = 𝟙 (nearProd X Y) := by
  apply CodedHom.ext
  change tensorClass T (objectIdempotent T (objectCode X))
      (objectIdempotent T (objectCode Y)) =
    objectIdempotent T (.product (objectCode X) (objectCode Y))
  exact (objectIdempotent_product T _ _).symm

theorem typed_nearProd_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {U V W X Y Z : CodedProgramCategory T}
    (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    nearProd_map f h ≫ nearProd_map g k =
      nearProd_map (f ≫ g) (h ≫ k) := by
  apply CodedHom.ext
  change tensorClass T g.1 k.1 * tensorClass T f.1 h.1 =
    tensorClass T (g.1 * f.1) (k.1 * h.1)
  exact (tensorClass_mul T g.1 f.1 k.1 h.1).symm

theorem typed_diag_p0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X : CodedProgramCategory T) :
    diag X ≫ p0 X X = 𝟙 X := by
  apply CodedHom.ext
  rw [comp_val, p0_val, diag_val, id_val]
  rw [objectIdempotent_product]
  let e := objectIdempotent T (objectCode X)
  change (firstProjectionClass T * tensorClass T e e) *
      (diagonalClass T * e) = e
  calc
    (firstProjectionClass T * tensorClass T e e) *
          (diagonalClass T * e) =
        firstProjectionClass T *
          (tensorClass T e e * diagonalClass T) * e := by
            simp only [mul_assoc]
    _ = firstProjectionClass T * (diagonalClass T * e) * e := by
          rw [← diagonalClass_natural]
    _ = (firstProjectionClass T * diagonalClass T) * (e * e) := by
          simp only [mul_assoc]
    _ = e := by
          rw [firstProjectionClass_mul_diagonalClass,
            objectIdempotent_mul_self, one_mul]

theorem typed_diag_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X : CodedProgramCategory T) :
    diag X ≫ p1 X X = 𝟙 X := by
  apply CodedHom.ext
  rw [comp_val, p1_val, diag_val, id_val]
  rw [objectIdempotent_product]
  let e := objectIdempotent T (objectCode X)
  change (secondProjectionClass T * tensorClass T e e) *
      (diagonalClass T * e) = e
  calc
    (secondProjectionClass T * tensorClass T e e) *
          (diagonalClass T * e) =
        secondProjectionClass T *
          (tensorClass T e e * diagonalClass T) * e := by
            simp only [mul_assoc]
    _ = secondProjectionClass T * (diagonalClass T * e) * e := by
          rw [← diagonalClass_natural]
    _ = (secondProjectionClass T * diagonalClass T) * (e * e) := by
          simp only [mul_assoc]
    _ = e := by
          rw [secondProjectionClass_mul_diagonalClass,
            objectIdempotent_mul_self, one_mul]

theorem typed_diag_p0_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y : CodedProgramCategory T) :
    diag (nearProd X Y) ≫ nearProd_map (p0 X Y) (p1 X Y) =
      𝟙 (nearProd X Y) := by
  apply CodedHom.ext
  change tensorClass T (p0 X Y).1 (p1 X Y).1 *
      (diag (nearProd X Y)).1 =
    objectIdempotent T (.product (objectCode X) (objectCode Y))
  rw [p0_val, p1_val, diag_val]
  let e := objectIdempotent T
    (.product (objectCode X) (objectCode Y))
  change tensorClass T
        (firstProjectionClass T * e) (secondProjectionClass T * e) *
      (diagonalClass T * e) = e
  have he : e * e = e := objectIdempotent_mul_self T _
  have hte : tensorClass T e e * tensorClass T e e = tensorClass T e e := by
    calc
      tensorClass T e e * tensorClass T e e =
          tensorClass T (e * e) (e * e) :=
        (tensorClass_mul T e e e e).symm
      _ = tensorClass T e e := by rw [he]
  calc
    tensorClass T (firstProjectionClass T * e)
          (secondProjectionClass T * e) * (diagonalClass T * e) =
        (tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
          tensorClass T e e) * (diagonalClass T * e) := by
            rw [tensorClass_mul]
    _ = tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
          (tensorClass T e e * (tensorClass T e e * diagonalClass T)) := by
            rw [diagonalClass_natural]
            simp only [mul_assoc]
    _ = tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
          (tensorClass T e e * diagonalClass T) := by
            rw [← mul_assoc (tensorClass T e e), hte]
    _ = tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
          (diagonalClass T * e) := by
            rw [← diagonalClass_natural]
    _ = tensorClass T (firstProjectionClass T) (secondProjectionClass T) *
          diagonalClass T * e := by
            rw [mul_assoc]
    _ = e := by
          rw [tensorProjectionsClass_mul_diagonalClass, one_mul]

/-- Algebraic form of the two left-nested projection identities. -/
theorem firstProjectionClass_tensor_first_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (e a : ProgramQuotient T) :
    firstProjectionClass T *
      tensorClass T e (firstProjectionClass T * a) =
    firstProjectionClass T * tensorClass T e a := by
  have hfactor₁ : tensorClass T e (firstProjectionClass T * a) =
      tensorClass T e (firstProjectionClass T) * tensorClass T 1 a := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T e 1 (firstProjectionClass T) a)
  have hfactor₂ : tensorClass T e (firstProjectionClass T) =
      tensorClass T e 1 * tensorClass T 1 (firstProjectionClass T) := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T e 1 1 (firstProjectionClass T))
  have hfactor₃ : tensorClass T e a =
      tensorClass T e 1 * tensorClass T 1 a := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T e 1 1 a)
  calc
    firstProjectionClass T *
          tensorClass T e (firstProjectionClass T * a) =
        (firstProjectionClass T * tensorClass T e
          (firstProjectionClass T)) * tensorClass T 1 a := by
            rw [hfactor₁, ← mul_assoc]
    _ = ((firstProjectionClass T * tensorClass T e 1) *
          tensorClass T 1 (firstProjectionClass T)) *
          tensorClass T 1 a := by
            rw [hfactor₂, ← mul_assoc]
    _ = ((e * firstProjectionClass T) *
          tensorClass T 1 (firstProjectionClass T)) *
          tensorClass T 1 a := by
            rw [firstProjectionClass_natural]
    _ = (e * (firstProjectionClass T *
          tensorClass T 1 (firstProjectionClass T))) *
          tensorClass T 1 a := by simp only [mul_assoc]
    _ = (e * firstProjectionClass T) * tensorClass T 1 a := by
          rw [firstProjectionClass_tensor_first]
    _ = (firstProjectionClass T * tensorClass T e 1) *
          tensorClass T 1 a := by rw [firstProjectionClass_natural]
    _ = firstProjectionClass T * tensorClass T e a := by
          rw [hfactor₃, ← mul_assoc]

theorem firstProjectionClass_tensor_second_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (e a : ProgramQuotient T) :
    firstProjectionClass T *
      tensorClass T e (secondProjectionClass T * a) =
    firstProjectionClass T * tensorClass T e a := by
  have hfactor₁ : tensorClass T e (secondProjectionClass T * a) =
      tensorClass T e (secondProjectionClass T) * tensorClass T 1 a := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T e 1 (secondProjectionClass T) a)
  have hfactor₂ : tensorClass T e (secondProjectionClass T) =
      tensorClass T e 1 * tensorClass T 1 (secondProjectionClass T) := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T e 1 1 (secondProjectionClass T))
  have hfactor₃ : tensorClass T e a =
      tensorClass T e 1 * tensorClass T 1 a := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T e 1 1 a)
  calc
    firstProjectionClass T *
          tensorClass T e (secondProjectionClass T * a) =
        ((firstProjectionClass T * tensorClass T e 1) *
          tensorClass T 1 (secondProjectionClass T)) *
          tensorClass T 1 a := by
            rw [hfactor₁, hfactor₂, ← mul_assoc, ← mul_assoc]
    _ = ((e * firstProjectionClass T) *
          tensorClass T 1 (secondProjectionClass T)) *
          tensorClass T 1 a := by rw [firstProjectionClass_natural]
    _ = (e * (firstProjectionClass T *
          tensorClass T 1 (secondProjectionClass T))) *
          tensorClass T 1 a := by simp only [mul_assoc]
    _ = (e * firstProjectionClass T) * tensorClass T 1 a := by
          rw [firstProjectionClass_tensor_second]
    _ = (firstProjectionClass T * tensorClass T e 1) *
          tensorClass T 1 a := by rw [firstProjectionClass_natural]
    _ = firstProjectionClass T * tensorClass T e a := by
          rw [hfactor₃, ← mul_assoc]

/-- Algebraic form of the two right-nested projection identities. -/
theorem secondProjectionClass_tensor_first_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a e : ProgramQuotient T) :
    secondProjectionClass T *
      tensorClass T (firstProjectionClass T * a) e =
    secondProjectionClass T * tensorClass T a e := by
  have hfactor₁ : tensorClass T (firstProjectionClass T * a) e =
      tensorClass T (firstProjectionClass T) 1 * tensorClass T a e := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T (firstProjectionClass T) a 1 e)
  calc
    secondProjectionClass T *
          tensorClass T (firstProjectionClass T * a) e =
        (secondProjectionClass T *
          tensorClass T (firstProjectionClass T) 1) *
          tensorClass T a e := by rw [hfactor₁, ← mul_assoc]
    _ = secondProjectionClass T * tensorClass T a e := by
          rw [secondProjectionClass_tensor_first]

theorem secondProjectionClass_tensor_second_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a e : ProgramQuotient T) :
    secondProjectionClass T *
      tensorClass T (secondProjectionClass T * a) e =
    secondProjectionClass T * tensorClass T a e := by
  have hfactor₁ : tensorClass T (secondProjectionClass T * a) e =
      tensorClass T (secondProjectionClass T) 1 * tensorClass T a e := by
    simpa only [mul_one, one_mul] using
      (tensorClass_mul T (secondProjectionClass T) a 1 e)
  calc
    secondProjectionClass T *
          tensorClass T (secondProjectionClass T * a) e =
        (secondProjectionClass T *
          tensorClass T (secondProjectionClass T) 1) *
          tensorClass T a e := by rw [hfactor₁, ← mul_assoc]
    _ = secondProjectionClass T * tensorClass T a e := by
          rw [secondProjectionClass_tensor_second]

theorem typed_p0_p0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    nearProd_map (𝟙 X) (p0 Y Z) ≫ p0 X Y =
      p0 X (nearProd Y Z) := by
  have hm := (typedNearProdMap T (𝟙 X) (p0 Y Z)).2.1
  change objectIdempotent T (.product (objectCode X) (objectCode Y)) *
      tensorClass T ((𝟙 X : X ⟶ X)).1 (p0 Y Z).1 =
    tensorClass T ((𝟙 X : X ⟶ X)).1 (p0 Y Z).1 at hm
  rw [id_val, p0_val] at hm
  simp only [objectIdempotent_product] at hm
  apply CodedHom.ext
  rw [comp_val]
  change (p0 X Y).1 *
      tensorClass T ((𝟙 X : X ⟶ X)).1 (p0 Y Z).1 =
    (p0 X (nearProd Y Z)).1
  simp only [id_val, p0_val]
  change (firstProjectionClass T *
        objectIdempotent T (.product (objectCode X) (objectCode Y))) *
      tensorClass T (objectIdempotent T (objectCode X))
        (firstProjectionClass T *
          objectIdempotent T (.product (objectCode Y) (objectCode Z))) =
    firstProjectionClass T *
      objectIdempotent T
        (.product (objectCode X) (.product (objectCode Y) (objectCode Z)))
  simp only [objectIdempotent_product]
  calc
    (firstProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode X))
            (objectIdempotent T (objectCode Y))) *
        tensorClass T (objectIdempotent T (objectCode X))
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z))) =
      firstProjectionClass T *
        (tensorClass T (objectIdempotent T (objectCode X))
          (objectIdempotent T (objectCode Y)) *
        tensorClass T (objectIdempotent T (objectCode X))
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z)))) := by
        rw [mul_assoc]
    _ = firstProjectionClass T *
        tensorClass T (objectIdempotent T (objectCode X))
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z))) := by rw [hm]
    _ = firstProjectionClass T *
        tensorClass T (objectIdempotent T (objectCode X))
          (tensorClass T (objectIdempotent T (objectCode Y))
            (objectIdempotent T (objectCode Z))) :=
      firstProjectionClass_tensor_first_comp T _ _

theorem typed_p0_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    nearProd_map (𝟙 X) (p1 Y Z) ≫ p0 X Z =
      p0 X (nearProd Y Z) := by
  have hm := (typedNearProdMap T (𝟙 X) (p1 Y Z)).2.1
  change objectIdempotent T (.product (objectCode X) (objectCode Z)) *
      tensorClass T ((𝟙 X : X ⟶ X)).1 (p1 Y Z).1 =
    tensorClass T ((𝟙 X : X ⟶ X)).1 (p1 Y Z).1 at hm
  rw [id_val, p1_val] at hm
  simp only [objectIdempotent_product] at hm
  apply CodedHom.ext
  rw [comp_val]
  change (p0 X Z).1 *
      tensorClass T ((𝟙 X : X ⟶ X)).1 (p1 Y Z).1 =
    (p0 X (nearProd Y Z)).1
  simp only [id_val, p0_val, p1_val]
  change (firstProjectionClass T *
        objectIdempotent T (.product (objectCode X) (objectCode Z))) *
      tensorClass T (objectIdempotent T (objectCode X))
        (secondProjectionClass T *
          objectIdempotent T (.product (objectCode Y) (objectCode Z))) =
    firstProjectionClass T *
      objectIdempotent T
        (.product (objectCode X) (.product (objectCode Y) (objectCode Z)))
  simp only [objectIdempotent_product]
  calc
    (firstProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode X))
            (objectIdempotent T (objectCode Z))) *
        tensorClass T (objectIdempotent T (objectCode X))
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z))) =
      firstProjectionClass T *
        (tensorClass T (objectIdempotent T (objectCode X))
          (objectIdempotent T (objectCode Z)) *
        tensorClass T (objectIdempotent T (objectCode X))
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z)))) := by rw [mul_assoc]
    _ = firstProjectionClass T *
        tensorClass T (objectIdempotent T (objectCode X))
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode Y))
              (objectIdempotent T (objectCode Z))) := by rw [hm]
    _ = firstProjectionClass T *
        tensorClass T (objectIdempotent T (objectCode X))
          (tensorClass T (objectIdempotent T (objectCode Y))
            (objectIdempotent T (objectCode Z))) :=
      firstProjectionClass_tensor_second_comp T _ _

theorem typed_p1_p0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    nearProd_map (p0 X Y) (𝟙 Z) ≫ p1 X Z =
      p1 (nearProd X Y) Z := by
  have hm := (typedNearProdMap T (p0 X Y) (𝟙 Z)).2.1
  change objectIdempotent T (.product (objectCode X) (objectCode Z)) *
      tensorClass T (p0 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 =
    tensorClass T (p0 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 at hm
  rw [p0_val, id_val] at hm
  simp only [objectIdempotent_product] at hm
  apply CodedHom.ext
  rw [comp_val]
  change (p1 X Z).1 *
      tensorClass T (p0 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 =
    (p1 (nearProd X Y) Z).1
  simp only [id_val, p0_val, p1_val]
  change (secondProjectionClass T *
        objectIdempotent T (.product (objectCode X) (objectCode Z))) *
      tensorClass T
        (firstProjectionClass T *
          objectIdempotent T (.product (objectCode X) (objectCode Y)))
        (objectIdempotent T (objectCode Z)) =
    secondProjectionClass T *
      objectIdempotent T
        (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))
  simp only [objectIdempotent_product]
  calc
    (secondProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode X))
            (objectIdempotent T (objectCode Z))) *
        tensorClass T
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) =
      secondProjectionClass T *
        (tensorClass T (objectIdempotent T (objectCode X))
          (objectIdempotent T (objectCode Z)) *
        tensorClass T
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z))) := by rw [mul_assoc]
    _ = secondProjectionClass T *
        tensorClass T
          (firstProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) := by rw [hm]
    _ = secondProjectionClass T *
        tensorClass T
          (tensorClass T (objectIdempotent T (objectCode X))
            (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) :=
      secondProjectionClass_tensor_first_comp T _ _

theorem typed_p1_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    nearProd_map (p1 X Y) (𝟙 Z) ≫ p1 Y Z =
      p1 (nearProd X Y) Z := by
  have hm := (typedNearProdMap T (p1 X Y) (𝟙 Z)).2.1
  change objectIdempotent T (.product (objectCode Y) (objectCode Z)) *
      tensorClass T (p1 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 =
    tensorClass T (p1 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 at hm
  rw [p1_val, id_val] at hm
  simp only [objectIdempotent_product] at hm
  apply CodedHom.ext
  rw [comp_val]
  change (p1 Y Z).1 *
      tensorClass T (p1 X Y).1 ((𝟙 Z : Z ⟶ Z)).1 =
    (p1 (nearProd X Y) Z).1
  simp only [id_val, p1_val]
  change (secondProjectionClass T *
        objectIdempotent T (.product (objectCode Y) (objectCode Z))) *
      tensorClass T
        (secondProjectionClass T *
          objectIdempotent T (.product (objectCode X) (objectCode Y)))
        (objectIdempotent T (objectCode Z)) =
    secondProjectionClass T *
      objectIdempotent T
        (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))
  simp only [objectIdempotent_product]
  calc
    (secondProjectionClass T *
          tensorClass T (objectIdempotent T (objectCode Y))
            (objectIdempotent T (objectCode Z))) *
        tensorClass T
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) =
      secondProjectionClass T *
        (tensorClass T (objectIdempotent T (objectCode Y))
          (objectIdempotent T (objectCode Z)) *
        tensorClass T
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z))) := by rw [mul_assoc]
    _ = secondProjectionClass T *
        tensorClass T
          (secondProjectionClass T *
            tensorClass T (objectIdempotent T (objectCode X))
              (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) := by rw [hm]
    _ = secondProjectionClass T *
        tensorClass T
          (tensorClass T (objectIdempotent T (objectCode X))
            (objectIdempotent T (objectCode Y)))
          (objectIdempotent T (objectCode Z)) :=
      secondProjectionClass_tensor_second_comp T _ _

theorem typed_diag_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y : CodedProgramCategory T} (f : X ⟶ Y) :
    f ≫ diag Y = diag X ≫ nearProd_map f f := by
  apply CodedHom.ext
  rw [comp_val, comp_val]
  change (diag Y).1 * f.1 = tensorClass T f.1 f.1 * (diag X).1
  simp only [diag_val]
  have ht : objectIdempotent T (objectCode Y) * f.1 = f.1 := f.2.1
  have hs : f.1 * objectIdempotent T (objectCode X) = f.1 := f.2.2
  calc
    (diagonalClass T * objectIdempotent T (objectCode Y)) * f.1 =
        diagonalClass T *
          (objectIdempotent T (objectCode Y) * f.1) := by rw [mul_assoc]
    _ = diagonalClass T * f.1 := by rw [ht]
    _ = tensorClass T f.1 f.1 * diagonalClass T :=
      diagonalClass_natural T f.1
    _ = tensorClass T f.1 f.1 * diagonalClass T *
          objectIdempotent T (objectCode X) := by
        rw [← diagonalClass_natural, mul_assoc, hs]
    _ = tensorClass T f.1 f.1 *
          (diagonalClass T * objectIdempotent T (objectCode X)) := by
        rw [mul_assoc]

theorem firstProjection_supported_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a e d z : ProgramQuotient T)
    (ht : d * a = a) (hs : a * e = a) (hz : z * z = z) :
    (firstProjectionClass T * tensorClass T d z) * tensorClass T a z =
      a * (firstProjectionClass T * tensorClass T e z) := by
  have hleft : tensorClass T d z * tensorClass T a z =
      tensorClass T a z := by
    rw [← tensorClass_mul, ht, hz]
  have hfactorA : tensorClass T a z =
      tensorClass T a 1 * tensorClass T 1 z := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T a 1 1 z)
  have hfactorE : tensorClass T e z =
      tensorClass T e 1 * tensorClass T 1 z := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T e 1 1 z)
  calc
    (firstProjectionClass T * tensorClass T d z) * tensorClass T a z =
        firstProjectionClass T *
          (tensorClass T d z * tensorClass T a z) := by rw [mul_assoc]
    _ = firstProjectionClass T * tensorClass T a z := by rw [hleft]
    _ = (firstProjectionClass T * tensorClass T a 1) *
          tensorClass T 1 z := by rw [hfactorA, ← mul_assoc]
    _ = (a * firstProjectionClass T) * tensorClass T 1 z := by
          rw [firstProjectionClass_natural]
    _ = a * (firstProjectionClass T * tensorClass T 1 z) := by
          rw [mul_assoc]
    _ = (a * e) * (firstProjectionClass T * tensorClass T 1 z) := by
          rw [hs]
    _ = a * (e * (firstProjectionClass T * tensorClass T 1 z)) := by
          rw [mul_assoc]
    _ = a * ((e * firstProjectionClass T) * tensorClass T 1 z) := by
          rw [mul_assoc]
    _ = a * ((firstProjectionClass T * tensorClass T e 1) *
          tensorClass T 1 z) := by rw [firstProjectionClass_natural]
    _ = a * (firstProjectionClass T * tensorClass T e z) := by
          rw [hfactorE]
          simp only [mul_assoc]

theorem secondProjection_supported_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a e d z : ProgramQuotient T)
    (ht : d * a = a) (hs : a * e = a) (hz : z * z = z) :
    (secondProjectionClass T * tensorClass T z d) * tensorClass T z a =
      a * (secondProjectionClass T * tensorClass T z e) := by
  have hleft : tensorClass T z d * tensorClass T z a =
      tensorClass T z a := by
    rw [← tensorClass_mul, hz, ht]
  have hfactorA : tensorClass T z a =
      tensorClass T 1 a * tensorClass T z 1 := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T 1 z a 1)
  have hfactorE : tensorClass T z e =
      tensorClass T 1 e * tensorClass T z 1 := by
    simpa only [mul_one, one_mul] using (tensorClass_mul T 1 z e 1)
  calc
    (secondProjectionClass T * tensorClass T z d) * tensorClass T z a =
        secondProjectionClass T *
          (tensorClass T z d * tensorClass T z a) := by rw [mul_assoc]
    _ = secondProjectionClass T * tensorClass T z a := by rw [hleft]
    _ = (secondProjectionClass T * tensorClass T 1 a) *
          tensorClass T z 1 := by rw [hfactorA, ← mul_assoc]
    _ = (a * secondProjectionClass T) * tensorClass T z 1 := by
          rw [secondProjectionClass_natural]
    _ = a * (secondProjectionClass T * tensorClass T z 1) := by
          rw [mul_assoc]
    _ = (a * e) * (secondProjectionClass T * tensorClass T z 1) := by
          rw [hs]
    _ = a * (e * (secondProjectionClass T * tensorClass T z 1)) := by
          rw [mul_assoc]
    _ = a * ((e * secondProjectionClass T) * tensorClass T z 1) := by
          rw [mul_assoc]
    _ = a * ((secondProjectionClass T * tensorClass T 1 e) *
          tensorClass T z 1) := by rw [secondProjectionClass_natural]
    _ = a * (secondProjectionClass T * tensorClass T z e) := by
          rw [hfactorE]
          simp only [mul_assoc]

theorem typed_p0_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (f : X ⟶ Y) :
    nearProd_map f (𝟙 Z) ≫ p0 Y Z = p0 X Z ≫ f := by
  apply CodedHom.ext
  rw [comp_val, comp_val]
  change (p0 Y Z).1 * tensorClass T f.1 ((𝟙 Z : Z ⟶ Z)).1 =
    f.1 * (p0 X Z).1
  simp only [id_val, p0_val]
  simp only [objectIdempotent_product]
  exact firstProjection_supported_natural T f.1
    (objectIdempotent T (objectCode X))
    (objectIdempotent T (objectCode Y))
    (objectIdempotent T (objectCode Z)) f.2.1 f.2.2
    (objectIdempotent_mul_self T _)

theorem typed_p1_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (f : X ⟶ Y) :
    nearProd_map (𝟙 Z) f ≫ p1 Z Y = p1 Z X ≫ f := by
  apply CodedHom.ext
  rw [comp_val, comp_val]
  change (p1 Z Y).1 * tensorClass T ((𝟙 Z : Z ⟶ Z)).1 f.1 =
    f.1 * (p1 Z X).1
  simp only [id_val, p1_val]
  simp only [objectIdempotent_product]
  exact secondProjection_supported_natural T f.1
    (objectIdempotent T (objectCode X))
    (objectIdempotent T (objectCode Y))
    (objectIdempotent T (objectCode Z)) f.2.1 f.2.2
    (objectIdempotent_mul_self T _)

/-! ## Pairing, symmetry, and association -/

/-- Pairing on a common input is tensoring after the diagonal. -/
theorem eqIndex_pair_tensor_diagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    EqIndex T (pairIndex q r)
      (compIndex (tensorIndex q r) diagonalIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨a, b, hq, hr, hy⟩ :=
      (eventualGraph_pairIndex_eval q r x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x x, (eventualGraph_diagonalIndex_eval _ _).mpr rfl, ?_⟩
    apply (eventualGraph_tensorIndex_eval q r _ _).mpr
    exact ⟨a, b, by simpa only [pi₁_pair] using hq,
      by simpa only [pi₂_pair] using hr, hy⟩
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    have hp' : p = pair x x := (eventualGraph_diagonalIndex_eval x p).mp hp
    obtain ⟨a, b, hq, hr, hy'⟩ :=
      (eventualGraph_tensorIndex_eval q r p y).mp hy
    rw [hp'] at hq hr
    apply (eventualGraph_pairIndex_eval q r x y).mpr
    exact ⟨a, b, by simpa only [pi₁_pair] using hq,
      by simpa only [pi₂_pair] using hr, hy'⟩

theorem pairClass_eq_tensor_diagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b : ProgramQuotient T) :
    pairClass T a b = tensorClass T a b * diagonalClass T := by
  refine Quotient.inductionOn a ?_
  intro q
  refine Quotient.inductionOn b ?_
  intro r
  change classOf T (pairIndex q r) =
    classOf T (compIndex (tensorIndex q r) diagonalIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_pair_tensor_diagonal T q r)

/-- Pairing two programs after a common program equals pairing first and then
executing that common program. -/
theorem pairClass_mul_common
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b e : ProgramQuotient T) :
    pairClass T (a * e) (b * e) = pairClass T a b * e := by
  rw [pairClass_eq_tensor_diagonal, pairClass_eq_tensor_diagonal]
  rw [tensorClass_mul]
  calc
    (tensorClass T a b * tensorClass T e e) * diagonalClass T =
        tensorClass T a b *
          (tensorClass T e e * diagonalClass T) := by rw [mul_assoc]
    _ = tensorClass T a b * (diagonalClass T * e) := by
          rw [← diagonalClass_natural]
    _ = (tensorClass T a b * diagonalClass T) * e := by rw [mul_assoc]

/-- The underlying class of categorical partial pairing is the quotient
pairing operation on the two underlying arrow classes. -/
@[simp] theorem partialPairing_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y : CodedProgramCategory T} (f : W ⟶ X) (g : W ⟶ Y) :
    (partialPairing f g).1 = pairClass T f.1 g.1 := by
  rw [show partialPairing f g = diag W ≫ nearProd_map f g from rfl, comp_val]
  change tensorClass T f.1 g.1 * (diag W).1 = _
  rw [diag_val]
  calc
    tensorClass T f.1 g.1 *
          (diagonalClass T * objectIdempotent T (objectCode W)) =
        (tensorClass T f.1 g.1 * diagonalClass T) *
          objectIdempotent T (objectCode W) := by rw [mul_assoc]
    _ = pairClass T f.1 g.1 * objectIdempotent T (objectCode W) := by
          rw [← pairClass_eq_tensor_diagonal]
    _ = pairClass T
          (f.1 * objectIdempotent T (objectCode W))
          (g.1 * objectIdempotent T (objectCode W)) := by
        rw [pairClass_mul_common]
    _ = pairClass T f.1 g.1 := by rw [f.2.2, g.2.2]

/-- Quotient class of the coordinate-swap program. -/
def swapClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T :=
  pairClass T (secondProjectionClass T) (firstProjectionClass T)

/-- Quotient class of the reassociation program
`((x,y),z) ↦ (x,(y,z))`. -/
def associatorClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T :=
  pairClass T
    (firstProjectionClass T * firstProjectionClass T)
    (pairClass T
      (secondProjectionClass T * firstProjectionClass T)
      (secondProjectionClass T))

@[simp] theorem swap_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y : CodedProgramCategory T) :
    (swap X Y).1 = swapClass T *
      objectIdempotent T (.product (objectCode X) (objectCode Y)) := by
  change (partialPairing (p1 X Y) (p0 X Y)).1 = _
  rw [partialPairing_val, p1_val, p0_val]
  exact pairClass_mul_common T (secondProjectionClass T)
    (firstProjectionClass T)
    (objectIdempotent T (.product (objectCode X) (objectCode Y)))

theorem assoc_first_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    (p0 (nearProd X Y) Z ≫ p0 X Y).1 =
      (firstProjectionClass T * firstProjectionClass T) *
        objectIdempotent T
          (.product (.product (objectCode X) (objectCode Y)) (objectCode Z)) := by
  have hf := (p0 (nearProd X Y) Z).2.1
  simp only [objectCode_nearProd, p0_val] at hf
  rw [comp_val, p0_val, p0_val]
  calc
    (firstProjectionClass T *
          objectIdempotent T (.product (objectCode X) (objectCode Y))) *
        (firstProjectionClass T *
          objectIdempotent T
            (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))) =
      firstProjectionClass T *
        (objectIdempotent T (.product (objectCode X) (objectCode Y)) *
          (firstProjectionClass T *
            objectIdempotent T
              (.product (.product (objectCode X) (objectCode Y))
                (objectCode Z)))) := by rw [mul_assoc]
    _ = firstProjectionClass T *
        (firstProjectionClass T *
          objectIdempotent T
            (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))) := by
          rw [hf]
    _ = (firstProjectionClass T * firstProjectionClass T) *
        objectIdempotent T
          (.product (.product (objectCode X) (objectCode Y)) (objectCode Z)) := by
          rw [mul_assoc]

theorem assoc_middle_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    (p0 (nearProd X Y) Z ≫ p1 X Y).1 =
      (secondProjectionClass T * firstProjectionClass T) *
        objectIdempotent T
          (.product (.product (objectCode X) (objectCode Y)) (objectCode Z)) := by
  have hf := (p0 (nearProd X Y) Z).2.1
  simp only [objectCode_nearProd, p0_val] at hf
  rw [comp_val, p0_val, p1_val]
  calc
    (secondProjectionClass T *
          objectIdempotent T (.product (objectCode X) (objectCode Y))) *
        (firstProjectionClass T *
          objectIdempotent T
            (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))) =
      secondProjectionClass T *
        (objectIdempotent T (.product (objectCode X) (objectCode Y)) *
          (firstProjectionClass T *
            objectIdempotent T
              (.product (.product (objectCode X) (objectCode Y))
                (objectCode Z)))) := by rw [mul_assoc]
    _ = secondProjectionClass T *
        (firstProjectionClass T *
          objectIdempotent T
            (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))) := by
          rw [hf]
    _ = (secondProjectionClass T * firstProjectionClass T) *
        objectIdempotent T
          (.product (.product (objectCode X) (objectCode Y)) (objectCode Z)) := by
          rw [mul_assoc]

@[simp] theorem assoc_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y Z : CodedProgramCategory T) :
    (assoc X Y Z).1 = associatorClass T *
      objectIdempotent T
        (.product (.product (objectCode X) (objectCode Y)) (objectCode Z)) := by
  change (partialPairing
    (p0 (nearProd X Y) Z ≫ p0 X Y)
    (partialPairing (p0 (nearProd X Y) Z ≫ p1 X Y)
      (p1 (nearProd X Y) Z))).1 = _
  rw [partialPairing_val, assoc_first_val, partialPairing_val,
    assoc_middle_val, p1_val]
  let e := objectIdempotent T
    (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))
  change pairClass T
      ((firstProjectionClass T * firstProjectionClass T) * e)
      (pairClass T
        ((secondProjectionClass T * firstProjectionClass T) * e)
        (secondProjectionClass T * e)) = associatorClass T * e
  rw [pairClass_mul_common]
  rw [pairClass_mul_common]
  rfl

/-- Numerical index of the coordinate swap. -/
def swapIndex : ℕ :=
  pairIndex secondProjectionIndex firstProjectionIndex

/-- Numerical index of reassociation `((x,y),z) ↦ (x,(y,z))`. -/
def associatorIndex : ℕ :=
  pairIndex
    (compIndex firstProjectionIndex firstProjectionIndex)
    (pairIndex
      (compIndex secondProjectionIndex firstProjectionIndex)
      secondProjectionIndex)

@[simp] theorem swapClass_eq_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    swapClass T = classOf T swapIndex :=
  rfl

@[simp] theorem associatorClass_eq_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    associatorClass T = classOf T associatorIndex :=
  rfl

@[simp] theorem eventualGraph_swapIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph swapIndex).val.Evalb ![x, y] ↔
      y = pair (pi₂ x) (pi₁ x) := by
  rw [swapIndex, eventualGraph_pairIndex_eval]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [(eventualGraph_secondProjectionIndex_eval _ _).mp ha,
      (eventualGraph_firstProjectionIndex_eval _ _).mp hb]
  · intro hy
    exact ⟨pi₂ x, pi₁ x,
      (eventualGraph_secondProjectionIndex_eval _ _).mpr rfl,
      (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl, hy⟩

@[simp] theorem eventualGraph_associatorIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph associatorIndex).val.Evalb ![x, y] ↔
      y = pair (pi₁ (pi₁ x)) (pair (pi₂ (pi₁ x)) (pi₂ x)) := by
  rw [associatorIndex, eventualGraph_pairIndex_eval]
  constructor
  · rintro ⟨a, bc, ha, hbc, rfl⟩
    obtain ⟨u, hu, ha'⟩ :=
      (eventualGraph_comp_eval _ _ x a).mp ha
    have hu' : u = pi₁ x :=
      (eventualGraph_firstProjectionIndex_eval x u).mp hu
    have ha'' : a = pi₁ u :=
      (eventualGraph_firstProjectionIndex_eval u a).mp ha'
    obtain ⟨b, c, hb, hc, hbc'⟩ :=
      (eventualGraph_pairIndex_eval _ _ x bc).mp hbc
    obtain ⟨v, hv, hb'⟩ :=
      (eventualGraph_comp_eval _ _ x b).mp hb
    have hv' : v = pi₁ x :=
      (eventualGraph_firstProjectionIndex_eval x v).mp hv
    have hb'' : b = pi₂ v :=
      (eventualGraph_secondProjectionIndex_eval v b).mp hb'
    have hc' : c = pi₂ x :=
      (eventualGraph_secondProjectionIndex_eval x c).mp hc
    rw [hbc', ha'', hu', hb'', hv', hc']
  · intro hy
    refine ⟨pi₁ (pi₁ x), pair (pi₂ (pi₁ x)) (pi₂ x), ?_, ?_, hy⟩
    · apply (eventualGraph_comp_eval _ _ x _).mpr
      exact ⟨pi₁ x,
        (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl,
        (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl⟩
    · apply (eventualGraph_pairIndex_eval _ _ x _).mpr
      refine ⟨pi₂ (pi₁ x), pi₂ x, ?_, ?_, rfl⟩
      · apply (eventualGraph_comp_eval _ _ x _).mpr
        exact ⟨pi₁ x,
          (eventualGraph_firstProjectionIndex_eval _ _).mpr rfl,
          (eventualGraph_secondProjectionIndex_eval _ _).mpr rfl⟩
      · exact (eventualGraph_secondProjectionIndex_eval _ _).mpr rfl

/-- Naturality of the concrete coordinate swap. -/
theorem eqIndex_swap_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    EqIndex T (compIndex swapIndex (tensorIndex q r))
      (compIndex (tensorIndex r q) swapIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨a, b, hq, hr, hp'⟩ :=
      (eventualGraph_tensorIndex_eval q r x p).mp hp
    have hy' : y = pair b a := by
      rw [hp'] at hy
      simpa only [pi₁_pair, pi₂_pair] using
        (eventualGraph_swapIndex_eval _ _).mp hy
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair (pi₂ x) (pi₁ x),
      (eventualGraph_swapIndex_eval _ _).mpr rfl, ?_⟩
    apply (eventualGraph_tensorIndex_eval r q _ _).mpr
    exact ⟨b, a, by simpa only [pi₁_pair] using hr,
      by simpa only [pi₂_pair] using hq, hy'⟩
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    have hp' : p = pair (pi₂ x) (pi₁ x) :=
      (eventualGraph_swapIndex_eval x p).mp hp
    obtain ⟨b, a, hr, hq, hy'⟩ :=
      (eventualGraph_tensorIndex_eval r q p y).mp hy
    rw [hp'] at hr hq
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair a b, ?_, (eventualGraph_swapIndex_eval _ _).mpr ?_⟩
    · apply (eventualGraph_tensorIndex_eval q r x _).mpr
      exact ⟨a, b, by simpa only [pi₂_pair] using hq,
        by simpa only [pi₁_pair] using hr, rfl⟩
    · simpa only [pi₁_pair, pi₂_pair] using hy'

/-- Naturality of the concrete reassociation program. -/
theorem eqIndex_associator_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r s : ℕ) :
    EqIndex T
      (compIndex associatorIndex (tensorIndex (tensorIndex q r) s))
      (compIndex (tensorIndex q (tensorIndex r s)) associatorIndex) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨ab, c, hab, hc, hp'⟩ :=
      (eventualGraph_tensorIndex_eval (tensorIndex q r) s x p).mp hp
    obtain ⟨a, b, hq, hr, hab'⟩ :=
      (eventualGraph_tensorIndex_eval q r (pi₁ x) ab).mp hab
    have hy' : y = pair a (pair b c) := by
      rw [hp', hab'] at hy
      simpa only [pi₁_pair, pi₂_pair] using
        (eventualGraph_associatorIndex_eval _ _).mp hy
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair (pi₁ (pi₁ x))
      (pair (pi₂ (pi₁ x)) (pi₂ x)),
      (eventualGraph_associatorIndex_eval _ _).mpr rfl, ?_⟩
    apply (eventualGraph_tensorIndex_eval q (tensorIndex r s) _ _).mpr
    refine ⟨a, pair b c, by simpa only [pi₁_pair] using hq, ?_, hy'⟩
    apply (eventualGraph_tensorIndex_eval r s _ _).mpr
    exact ⟨b, c, by simpa only [pi₁_pair, pi₂_pair] using hr,
      by simpa only [pi₁_pair, pi₂_pair] using hc, rfl⟩
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    have hp' : p = pair (pi₁ (pi₁ x))
        (pair (pi₂ (pi₁ x)) (pi₂ x)) :=
      (eventualGraph_associatorIndex_eval x p).mp hp
    obtain ⟨a, bc, hq, hbc, hy'⟩ :=
      (eventualGraph_tensorIndex_eval q (tensorIndex r s) p y).mp hy
    obtain ⟨b, c, hr, hc, hbc'⟩ :=
      (eventualGraph_tensorIndex_eval r s (pi₂ p) bc).mp hbc
    rw [hp'] at hq hr hc
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair (pair a b) c, ?_,
      (eventualGraph_associatorIndex_eval _ _).mpr ?_⟩
    · apply (eventualGraph_tensorIndex_eval (tensorIndex q r) s x _).mpr
      refine ⟨pair a b, c, ?_,
        by simpa only [pi₁_pair, pi₂_pair] using hc, rfl⟩
      apply (eventualGraph_tensorIndex_eval q r _ _).mpr
      exact ⟨a, b, by simpa only [pi₁_pair, pi₂_pair] using hq,
        by simpa only [pi₁_pair, pi₂_pair] using hr, rfl⟩
    · rw [hbc'] at hy'
      simpa only [pi₁_pair, pi₂_pair] using hy'

theorem swapClass_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b : ProgramQuotient T) :
    swapClass T * tensorClass T a b = tensorClass T b a * swapClass T := by
  refine Quotient.inductionOn a ?_
  intro q
  refine Quotient.inductionOn b ?_
  intro r
  change classOf T (compIndex swapIndex (tensorIndex q r)) =
    classOf T (compIndex (tensorIndex r q) swapIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_swap_natural T q r)

theorem associatorClass_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b c : ProgramQuotient T) :
    associatorClass T * tensorClass T (tensorClass T a b) c =
      tensorClass T a (tensorClass T b c) * associatorClass T := by
  refine Quotient.inductionOn₃ a b c ?_
  intro q r s
  change classOf T
      (compIndex associatorIndex (tensorIndex (tensorIndex q r) s)) =
    classOf T
      (compIndex (tensorIndex q (tensorIndex r s)) associatorIndex)
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_associator_natural T q r s)

/-- Naturality of the derived coordinate swap on typed arrows. -/
theorem typed_swap_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X X' Y Y' : CodedProgramCategory T}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    nearProd_map f g ≫ swap X' Y' =
      swap X Y ≫ nearProd_map g f := by
  let m := tensorClass T f.1 g.1
  let n := tensorClass T g.1 f.1
  let e := objectIdempotent T
    (.product (objectCode X) (objectCode Y))
  let d := objectIdempotent T
    (.product (objectCode X') (objectCode Y'))
  have ht : d * m = m := (typedNearProdMap T f g).2.1
  have hs : m * e = m := (typedNearProdMap T f g).2.2
  have hn : swapClass T * m = n * swapClass T := by
    exact swapClass_natural T f.1 g.1
  have hsource : (n * swapClass T) * e = n * swapClass T := by
    rw [← hn, mul_assoc, hs]
  apply CodedHom.ext
  rw [comp_val, comp_val, swap_val, swap_val]
  change (swapClass T * d) * m = n * (swapClass T * e)
  calc
    (swapClass T * d) * m = swapClass T * (d * m) := by
      rw [mul_assoc]
    _ = swapClass T * m := by rw [ht]
    _ = n * swapClass T := hn
    _ = (n * swapClass T) * e := hsource.symm
    _ = n * (swapClass T * e) := by rw [mul_assoc]

/-- Naturality of the derived reassociation map on typed arrows. -/
theorem typed_assoc_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X X' Y Y' Z Z' : CodedProgramCategory T}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    nearProd_map (nearProd_map f g) h ≫ assoc X' Y' Z' =
      assoc X Y Z ≫ nearProd_map f (nearProd_map g h) := by
  let m := tensorClass T (tensorClass T f.1 g.1) h.1
  let n := tensorClass T f.1 (tensorClass T g.1 h.1)
  let e := objectIdempotent T
    (.product (.product (objectCode X) (objectCode Y)) (objectCode Z))
  let d := objectIdempotent T
    (.product (.product (objectCode X') (objectCode Y')) (objectCode Z'))
  have ht : d * m = m :=
    (typedNearProdMap T (typedNearProdMap T f g) h).2.1
  have hs : m * e = m :=
    (typedNearProdMap T (typedNearProdMap T f g) h).2.2
  have hn : associatorClass T * m = n * associatorClass T := by
    exact associatorClass_natural T f.1 g.1 h.1
  have hsource : (n * associatorClass T) * e =
      n * associatorClass T := by
    rw [← hn, mul_assoc, hs]
  apply CodedHom.ext
  rw [comp_val, comp_val, assoc_val, assoc_val]
  change (associatorClass T * d) * m = n * (associatorClass T * e)
  calc
    (associatorClass T * d) * m =
        associatorClass T * (d * m) := by rw [mul_assoc]
    _ = associatorClass T * m := by rw [ht]
    _ = n * associatorClass T := hn
    _ = (n * associatorClass T) * e := hsource.symm
    _ = n * (associatorClass T * e) := by rw [mul_assoc]

/-- The typed program category, with the concrete effective near product, is a
`P`-category. -/
instance codedProgramCategoryPCategory
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PCategory (CodedProgramCategory T) where
  nearProd_id := typed_nearProd_id T
  nearProd_comp := typed_nearProd_comp T
  diag_p0 := typed_diag_p0 T
  diag_p1 := typed_diag_p1 T
  diag_p0_p1 := typed_diag_p0_p1 T
  p0_p0 := typed_p0_p0 T
  p0_p1 := typed_p0_p1 T
  p1_p0 := typed_p1_p0 T
  p1_p1 := typed_p1_p1 T
  diag_nat := typed_diag_nat T
  p0_nat := typed_p0_nat T
  p1_nat := typed_p1_nat T
  assoc_nat := typed_assoc_nat T
  swap_nat := typed_swap_nat T

/-! ## The computation-domain restriction -/

/-- For a normalized program, the domain partial identity is obtained by
pairing the selected source identity with the program and then projecting the
first coordinate. -/
theorem eqIndex_domain_normalize_pair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T (domainIndex (normalizeIndex Q R q))
      (compIndex firstProjectionIndex
        (pairIndex (deltaIndex Q) (normalizeIndex Q R q))) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨hy, z, hz⟩ :=
      (eventualGraph_domainIndex_eval (normalizeIndex Q R q) x y).mp h
    have hQ :=
      (eventualGraph_normalizeIndex_eval Q R q x z).mp hz |>.1
    apply (eventualGraph_comp_pair_first_eval
      (deltaIndex Q) (normalizeIndex Q R q) x y).mpr
    exact ⟨x, z,
      (eventualGraph_deltaIndex_eval Q x x).mpr ⟨hQ, rfl⟩,
      hz, hy⟩
  · intro h
    obtain ⟨a, z, ha, hz, hya⟩ :=
      (eventualGraph_comp_pair_first_eval
        (deltaIndex Q) (normalizeIndex Q R q) x y).mp h
    have hax : a = x :=
      (eventualGraph_deltaIndex_eval Q x a).mp ha |>.2
    apply (eventualGraph_domainIndex_eval
      (normalizeIndex Q R q) x y).mpr
    exact ⟨hya.trans hax, z, hz⟩

/-- Quotient form of the normalized computation-domain equation. -/
theorem domainClass_normalize
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    domainClass T (classOf T (normalizeIndex Q R q)) =
      firstProjectionClass T *
        pairClass T (objectIdempotent T Q)
          (classOf T (normalizeIndex Q R q)) := by
  change classOf T (domainIndex (normalizeIndex Q R q)) =
    classOf T (compIndex firstProjectionIndex
      (pairIndex (deltaIndex Q) (normalizeIndex Q R q)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_domain_normalize_pair T Q R q)

/-- The quotient class of the computation-domain program is the underlying
class of the restriction induced by the concrete near product. -/
theorem domainClass_eq_rst_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (f : object T Q ⟶ object T R) :
    domainClass T f.1 = (rst f).1 := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T Q R f
  rw [← hq]
  have hp :=
    (partialPairing (𝟙 (object T Q)) (arrowOfIndex T Q R q)).2.1
  rw [partialPairing_val, id_val, arrowOfIndex_val] at hp
  change objectIdempotent T (.product Q R) *
      pairClass T (objectIdempotent T Q)
        (classOf T (normalizeIndex Q R q)) =
    pairClass T (objectIdempotent T Q)
      (classOf T (normalizeIndex Q R q)) at hp
  rw [show rst (arrowOfIndex T Q R q) =
      partialPairing (𝟙 (object T Q)) (arrowOfIndex T Q R q) ≫
        p0 (object T Q) (object T R) from
      PCategory.rst_eq_partialPairing (arrowOfIndex T Q R q)]
  rw [comp_val, partialPairing_val, p0_val, id_val, arrowOfIndex_val,
    domainClass_normalize]
  rw [mul_assoc]
  simp only [objectCode_object]
  rw [hp]

/-- The concrete computation-domain arrow of a typed program. -/
def domainArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) : Q ⟶ Q :=
  ⟨domainClass T f.1, by
    have h := domainClass_eq_rst_val T (objectCode Q) (objectCode R) f
    constructor
    · rw [h]
      exact (rst f).2.1
    · rw [h]
      exact (rst f).2.2⟩

/-- The concrete computation-domain arrow is exactly the restriction
operation induced by the P-category. -/
theorem domainArrow_eq_rst
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    domainArrow T f = rst f :=
  CodedHom.ext (domainClass_eq_rst_val T (objectCode Q) (objectCode R) f)

/-- A normalized numerical representative for the computation-domain arrow.
Target normalization is part of the index whose domain is taken. -/
@[simp] theorem domainArrow_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    domainArrow T (arrowOfIndex T Q R q) =
      arrowOfIndex T Q Q (domainIndex (normalizeIndex Q R q)) := by
  symm
  apply arrowOfIndex_eq_of_class
  change classOf T (domainIndex (normalizeIndex Q R q)) =
    domainClass T (arrowOfIndex T Q R q).1
  rw [arrowOfIndex_val, domainClass_classOf]

/-- The same compatibility at the RestrictionCategory spelling supplied by
PCategory.inducedRestriction; no second restriction instance is installed.
-/
theorem domainArrow_eq_restriction
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    domainArrow T f = RestrictionCategory.rst f := by
  rw [domainArrow_eq_rst, PCategory.restrictionCategory_rst]

/-! ## Numerical restriction representatives and internal totality -/

/-- The numerical restriction representative associated with a raw typed
representative.  Normalization precedes taking the computation domain. -/
def restrictionIndex (Q R : STObjectCode) (q : ℕ) : ℕ :=
  domainIndex (normalizeIndex Q R q)

/-- For fixed source and target objects, the restriction-index operation is
primitive recursive in the raw program index. -/
theorem primrec_restrictionIndex (Q R : STObjectCode) :
    Primrec (restrictionIndex Q R) :=
  primrec_domainIndex.comp (primrec_normalizeIndex Q R)

/-- Exact graph law for a normalized restriction representative in every
model of PA. -/
@[simp] theorem eventualGraph_restrictionIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (x y : M) :
    (eventualGraph (restrictionIndex Q R q)).val.Evalb ![x, y] ↔
      y = x ∧ ∃ z : M,
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, z] := by
  exact eventualGraph_domainIndex_eval (normalizeIndex Q R q) x y

/-- PA proves the exact graph law for each normalized restriction
representative. -/
theorem restrictionIndex_uniform (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (restrictionIndex Q R q))
      (domainGraph (normalizeIndex Q R q)) :=
  domainIndex_uniform (normalizeIndex Q R q)

/-- Representative equation for the P-category restriction. -/
@[simp] theorem rst_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    rst (arrowOfIndex T Q R q) =
      arrowOfIndex T Q Q (restrictionIndex Q R q) := by
  rw [← domainArrow_eq_rst, domainArrow_arrowOfIndex]
  rfl

/-- Representative equation for the induced restriction-category
operation. -/
@[simp] theorem restrictionCategory_rst_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    RestrictionCategory.rst (arrowOfIndex T Q R q) =
      arrowOfIndex T Q Q (restrictionIndex Q R q) := by
  rw [PCategory.restrictionCategory_rst, rst_arrowOfIndex]

/-- The internal assertion that the normalized representative terminates on
every member of its declared source object. -/
def typedTotalitySentence
    (Q R : STObjectCode) (q : ℕ) : ArithmeticSentence :=
  “∀ x, !(memberFormula Q).val x →
    ∃ y, !(eventualGraph (normalizeIndex Q R q)).val x y”

@[simp] theorem typedTotalitySentence_eval
    {M : Type*} [ORingStructure M]
    (Q R : STObjectCode) (q : ℕ) :
    (typedTotalitySentence Q R q).Evalb (M := M) ![] ↔
      ∀ x : M, (memberFormula Q).val.Evalb ![x] →
        ∃ y : M,
          (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] := by
  simp [typedTotalitySentence]

/-- A normalized computation-domain program equals the selected source
identity exactly when the ambient theory proves internal totality. -/
theorem eqIndex_restriction_iff_proves_typedTotality
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T (restrictionIndex Q R q) (deltaIndex Q) ↔
      T ⊢ typedTotalitySentence Q R q := by
  constructor
  · intro heq
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    have heqM := consequence_iff.mp (Theory.Proof.sound heq) M hM
    rw [models_iff, uniformSentence_eval] at heqM
    rw [models_iff, typedTotalitySentence_eval]
    intro x hQ
    have hdelta :
        (eventualGraph (deltaIndex Q)).val.Evalb ![x, x] :=
      (eventualGraph_deltaIndex_eval Q x x).mpr ⟨hQ, rfl⟩
    have hdomain :
        (eventualGraph (restrictionIndex Q R q)).val.Evalb ![x, x] :=
      (heqM x x).mpr hdelta
    exact (eventualGraph_restrictionIndex_eval Q R q x x).mp hdomain |>.2
  · intro htotal
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    have htotalM := consequence_iff.mp (Theory.Proof.sound htotal) M hM
    rw [models_iff, typedTotalitySentence_eval] at htotalM
    rw [models_iff, uniformSentence_eval]
    intro x y
    constructor
    · intro hdomain
      obtain ⟨hyx, z, hz⟩ :=
        (eventualGraph_restrictionIndex_eval Q R q x y).mp hdomain
      have hQ :=
        (eventualGraph_normalizeIndex_eval Q R q x z).mp hz |>.1
      exact (eventualGraph_deltaIndex_eval Q x y).mpr ⟨hQ, hyx⟩
    · intro hdelta
      obtain ⟨hQ, hyx⟩ :=
        (eventualGraph_deltaIndex_eval Q x y).mp hdelta
      obtain ⟨z, hz⟩ := htotalM x hQ
      exact (eventualGraph_restrictionIndex_eval Q R q x y).mpr
        ⟨hyx, z, hz⟩

/-- A typed arrow is restriction-total exactly when the theory proves that
its normalized representative terminates on every internally represented
source member. -/
theorem arrowOfIndex_isTotal_iff_proves_typedTotality
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    RestrictionCategory.isTotal (arrowOfIndex T Q R q) ↔
      T ⊢ typedTotalitySentence Q R q := by
  let f := arrowOfIndex T Q R q
  constructor
  · intro htotal
    have hdomain : domainArrow T f = 𝟙 (object T Q) :=
      (domainArrow_eq_restriction T f).trans htotal
    have hv := congrArg Subtype.val hdomain
    change domainClass T f.1 = objectIdempotent T Q at hv
    dsimp [f] at hv
    rw [arrowOfIndex_val, domainClass_classOf] at hv
    have heq : EqIndex T (restrictionIndex Q R q) (deltaIndex Q) := by
      apply (classOf_eq_classOf_iff T _ _).mp
      simpa only [restrictionIndex, objectIdempotent] using hv
    exact (eqIndex_restriction_iff_proves_typedTotality T Q R q).mp heq
  · intro htotal
    have heq : EqIndex T (restrictionIndex Q R q) (deltaIndex Q) :=
      (eqIndex_restriction_iff_proves_typedTotality T Q R q).mpr htotal
    have hclasses :
        classOf T (restrictionIndex Q R q) =
          classOf T (deltaIndex Q) :=
      (classOf_eq_classOf_iff T _ _).mpr heq
    have hdomain : domainArrow T f = 𝟙 (object T Q) := by
      apply CodedHom.ext
      change domainClass T f.1 = objectIdempotent T Q
      dsimp [f]
      rw [arrowOfIndex_val, domainClass_classOf]
      simpa only [restrictionIndex, objectIdempotent] using hclasses
    exact (domainArrow_eq_restriction T f).symm.trans hdomain

/-! ## Consequences from the generic P-category API -/

/-- The concrete first projection is restriction-total. -/
theorem typed_p0_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    RestrictionCategory.isTotal (p0 Q R) := by
  change RestrictionCategory.rst (p0 Q R) = 𝟙 (nearProd Q R)
  rw [PCategory.restrictionCategory_rst]
  exact PCategory.p0_isTotal Q R

/-- The concrete second projection is restriction-total. -/
theorem typed_p1_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    RestrictionCategory.isTotal (p1 Q R) := by
  change RestrictionCategory.rst (p1 Q R) = 𝟙 (nearProd Q R)
  rw [PCategory.restrictionCategory_rst]
  exact PCategory.p1_isTotal Q R

/-- The concrete diagonal is restriction-total. -/
theorem typed_diag_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    RestrictionCategory.isTotal (diag Q) := by
  change RestrictionCategory.rst (diag Q) = 𝟙 Q
  rw [PCategory.restrictionCategory_rst]
  exact PCategory.diag_isTotal Q

/-- Projection from a partial pairing requires both components to be defined:
the first projection retains the first component on the domain of the second.
-/
theorem typed_partialPairing_p0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R S : CodedProgramCategory T}
    (f : Q ⟶ R) (g : Q ⟶ S) :
    partialPairing f g ≫ p0 R S =
      RestrictionCategory.rst g ≫ f := by
  rw [PCategory.restrictionCategory_rst]
  exact PCategory.p0_partialPairing f g

/-- The second projection of a partial pairing retains the second component
on the domain of the first. -/
theorem typed_partialPairing_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R S : CodedProgramCategory T}
    (f : Q ⟶ R) (g : Q ⟶ S) :
    partialPairing f g ≫ p1 R S =
      RestrictionCategory.rst f ≫ g := by
  rw [PCategory.restrictionCategory_rst]
  exact PCategory.p1_partialPairing f g

/-- For total arrows, the generic P-category theorem supplies the ordinary
binary-product universal property. -/
theorem typed_existsUnique_partialPairing
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R S : CodedProgramCategory T}
    {f : Q ⟶ R} {g : Q ⟶ S}
    (hf : RestrictionCategory.isTotal f)
    (hg : RestrictionCategory.isTotal g) :
    ∃! h : Q ⟶ nearProd R S,
      h ≫ p0 R S = f ∧ h ≫ p1 R S = g := by
  apply PCategory.existsUnique_partialPairing
  · exact hf
  · exact hg

/-- A nested coded product gives a nontrivial application of the same
projection-totality theorem; the statement is not confined to omega. -/
theorem nestedProduct_firstProjection_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    RestrictionCategory.isTotal
      (p0 (object T (.product .omega .omega)) (object T .omega)) :=
  typed_p0_isTotal T _ _

end

end FailureOfComposition.TypedNearProduct
