/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProductProofs.RETheory

/-!
# Product proof maps at typed representatives

For raw representatives `a : Z ⟶ Q` and `b : Z ⟶ R`, the endpoints in this
file are chosen explicitly:

* `q = normalizeIndex Z Q a` and `r = normalizeIndex Z R b`;
* `pairIndex q r` for the partial pairing;
* `project0PairIndex q r` and `project1PairIndex q r` for its composites with
  the two typed projections.

These representatives are PA-supported.  The numerical proof maps therefore
apply without any separate transport between quotient-equivalent indices.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman CategoryTheory
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProductProofs

open ProofSearch ConcreteEvaluator CodedObjectMembership
open NumericalProofBridge TypedNearProduct TypedProgramCategory
open UniformIndexQuotient
open PCategoryStruct

noncomputable section

/-! ## Explicit typed endpoints -/

def typedLeftRepresentative (Z Q : STObjectCode) (a : ℕ) : ℕ :=
  normalizeIndex Z Q a

def typedRightRepresentative (Z R : STObjectCode) (b : ℕ) : ℕ :=
  normalizeIndex Z R b

def typedPairRepresentative
    (Z Q R : STObjectCode) (a b : ℕ) : ℕ :=
  pairIndex (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b)

def typedProject0Representative
    (Z Q R : STObjectCode) (a b : ℕ) : ℕ :=
  project0PairIndex (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b)

def typedProject1Representative
    (Z Q R : STObjectCode) (a b : ℕ) : ℕ :=
  project1PairIndex (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b)

theorem primrec₂_typedPairRepresentative (Z Q R : STObjectCode) :
    Primrec₂ (typedPairRepresentative Z Q R) :=
  primrec₂_pairIndex.comp
    ((primrec_normalizeIndex Z Q).comp Primrec.fst)
    ((primrec_normalizeIndex Z R).comp Primrec.snd)

theorem primrec₂_typedProject0Representative (Z Q R : STObjectCode) :
    Primrec₂ (typedProject0Representative Z Q R) :=
  primrec₂_project0PairIndex.comp
    ((primrec_normalizeIndex Z Q).comp Primrec.fst)
    ((primrec_normalizeIndex Z R).comp Primrec.snd)

theorem primrec₂_typedProject1Representative (Z Q R : STObjectCode) :
    Primrec₂ (typedProject1Representative Z Q R) :=
  primrec₂_project1PairIndex.comp
    ((primrec_normalizeIndex Z Q).comp Primrec.fst)
    ((primrec_normalizeIndex Z R).comp Primrec.snd)

/-! ## Support of the chosen representatives -/

theorem pa_proves_typedPairRepresentative_support
    (Z Q R : STObjectCode) (a b : ℕ) :
    𝗣𝗔 ⊢ supportSentence Z (.product Q R)
      (typedPairRepresentative Z Q R a b) := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  have hq := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_normalized_support Z Q a)) M hM
  have hr := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_normalized_support Z R b)) M hM
  rw [models_iff, supportSentence_eval] at hq hr ⊢
  intro x y hpair
  rw [typedPairRepresentative, typedLeftRepresentative,
    typedRightRepresentative, eventualGraph_pairIndex_eval] at hpair
  obtain ⟨u, v, hqu, hrv, rfl⟩ := hpair
  obtain ⟨hZ, hQ⟩ := hq x u hqu
  obtain ⟨-, hR⟩ := hr x v hrv
  exact ⟨hZ, (memberFormula_product_eval Q R (pair u v)).mpr
    ⟨u, v, rfl, hQ, hR⟩⟩

theorem pa_proves_typedProject0Representative_support
    (Z Q R : STObjectCode) (a b : ℕ) :
    𝗣𝗔 ⊢ supportSentence Z Q
      (typedProject0Representative Z Q R a b) := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  have hq := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_normalized_support Z Q a)) M hM
  rw [models_iff, supportSentence_eval] at hq ⊢
  intro x y hproj
  rw [typedProject0Representative, typedLeftRepresentative,
    typedRightRepresentative, project0PairIndex,
    eventualGraph_comp_pair_first_eval] at hproj
  obtain ⟨u, v, hqu, -, hyu⟩ := hproj
  obtain ⟨hZ, hQ⟩ := hq x u hqu
  subst y
  exact ⟨hZ, hQ⟩

theorem pa_proves_typedProject1Representative_support
    (Z Q R : STObjectCode) (a b : ℕ) :
    𝗣𝗔 ⊢ supportSentence Z R
      (typedProject1Representative Z Q R a b) := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  have hr := consequence_iff.mp
    (Theory.Proof.sound (pa_proves_normalized_support Z R b)) M hM
  rw [models_iff, supportSentence_eval] at hr ⊢
  intro x y hproj
  rw [typedProject1Representative, typedLeftRepresentative,
    typedRightRepresentative, project1PairIndex,
    eventualGraph_comp_pair_second_eval] at hproj
  obtain ⟨u, v, -, hrv, hyv⟩ := hproj
  obtain ⟨hZ, hR⟩ := hr x v hrv
  subst y
  exact ⟨hZ, hR⟩

theorem typedPairRepresentative_support_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    T ⊢ supportSentence Z (.product Q R)
      (typedPairRepresentative Z Q R a b) :=
  WeakerThan.pbl (pa_proves_typedPairRepresentative_support Z Q R a b)

theorem typedProject0Representative_support_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    T ⊢ supportSentence Z Q
      (typedProject0Representative Z Q R a b) :=
  WeakerThan.pbl (pa_proves_typedProject0Representative_support Z Q R a b)

theorem typedProject1Representative_support_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    T ⊢ supportSentence Z R
      (typedProject1Representative Z Q R a b) :=
  WeakerThan.pbl (pa_proves_typedProject1Representative_support Z Q R a b)

/-! ## Representation of the categorical pairing and projections -/

theorem typedPairRepresentative_arrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    arrowOfIndex T Z (.product Q R)
        (typedPairRepresentative Z Q R a b) =
      partialPairing (arrowOfIndex T Z Q a)
        (arrowOfIndex T Z R b) := by
  apply arrowOfIndex_eq_of_class
  rw [partialPairing_val, arrowOfIndex_val, arrowOfIndex_val,
    typedPairRepresentative, typedLeftRepresentative,
    typedRightRepresentative, pairClass_classOf]

theorem typedProject0Representative_arrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    arrowOfIndex T Z Q (typedProject0Representative Z Q R a b) =
      partialPairing (arrowOfIndex T Z Q a)
          (arrowOfIndex T Z R b) ≫
        p0 (object T Q) (object T R) := by
  let f := arrowOfIndex T Z Q a
  let g := arrowOfIndex T Z R b
  apply arrowOfIndex_eq_of_class
  have ht := (partialPairing f g).2.1
  simp only [objectCode_nearProd, objectCode_object] at ht
  rw [comp_val, p0_val, mul_assoc]
  simp only [objectCode_object]
  rw [ht]
  rw [partialPairing_val, arrowOfIndex_val, arrowOfIndex_val,
    typedProject0Representative, project0PairIndex,
    typedLeftRepresentative, typedRightRepresentative,
    pairClass_classOf]
  rfl

theorem typedProject1Representative_arrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z Q R : STObjectCode) (a b : ℕ) :
    arrowOfIndex T Z R (typedProject1Representative Z Q R a b) =
      partialPairing (arrowOfIndex T Z Q a)
          (arrowOfIndex T Z R b) ≫
        p1 (object T Q) (object T R) := by
  let f := arrowOfIndex T Z Q a
  let g := arrowOfIndex T Z R b
  apply arrowOfIndex_eq_of_class
  have ht := (partialPairing f g).2.1
  simp only [objectCode_nearProd, objectCode_object] at ht
  rw [comp_val, p1_val, mul_assoc]
  simp only [objectCode_object]
  rw [ht]
  rw [partialPairing_val, arrowOfIndex_val, arrowOfIndex_val,
    typedProject1Representative, project1PairIndex,
    typedLeftRepresentative, typedRightRepresentative,
    pairClass_classOf]
  rfl

/-! ## Typed numerical proof maps -/

def typedProject0ToPair
    (Z Q R : STObjectCode) (p a b n : ℕ) : ℕ :=
  project0ToPair p (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b) n

def typedProject1ToPair
    (Z Q R : STObjectCode) (p a b n : ℕ) : ℕ :=
  project1ToPair p (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b) n

def typedPairToLeft
    (Z Q R : STObjectCode) (p a b n : ℕ) : ℕ :=
  pairToLeft p (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b) n

def typedPairToRight
    (Z Q R : STObjectCode) (p a b n : ℕ) : ℕ :=
  pairToRight p (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b) n

def typedComponentsToPair
    (Z Q R : STObjectCode) (p h a b n : ℕ) : ℕ :=
  componentsToPair p h (typedLeftRepresentative Z Q a)
    (typedRightRepresentative Z R b) n

def typedProject0ToPairPacked (Z Q R : STObjectCode)
    (z : UnaryProductMapArgs) : ℕ :=
  typedProject0ToPair Z Q R z.1.1.1 z.1.1.2 z.1.2 z.2

def typedProject1ToPairPacked (Z Q R : STObjectCode)
    (z : UnaryProductMapArgs) : ℕ :=
  typedProject1ToPair Z Q R z.1.1.1 z.1.1.2 z.1.2 z.2

def typedPairToLeftPacked (Z Q R : STObjectCode)
    (z : UnaryProductMapArgs) : ℕ :=
  typedPairToLeft Z Q R z.1.1.1 z.1.1.2 z.1.2 z.2

def typedPairToRightPacked (Z Q R : STObjectCode)
    (z : UnaryProductMapArgs) : ℕ :=
  typedPairToRight Z Q R z.1.1.1 z.1.1.2 z.1.2 z.2

def typedComponentsToPairPacked (Z Q R : STObjectCode)
    (z : BinaryProductMapArgs) : ℕ :=
  typedComponentsToPair Z Q R z.1.1.1.1 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

private theorem primrec_typedUnaryArguments (Z Q R : STObjectCode) :
    Primrec (fun z : UnaryProductMapArgs =>
      (((z.1.1.1, typedLeftRepresentative Z Q z.1.1.2),
        typedRightRepresentative Z R z.1.2), z.2)) := by
  exact (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
    ((primrec_normalizeIndex Z Q).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).pair
    ((primrec_normalizeIndex Z R).comp
      (Primrec.snd.comp Primrec.fst))).pair Primrec.snd

private theorem primrec_typedBinaryArguments (Z Q R : STObjectCode) :
    Primrec (fun z : BinaryProductMapArgs =>
      ((((z.1.1.1.1, z.1.1.1.2),
        typedLeftRepresentative Z Q z.1.1.2),
        typedRightRepresentative Z R z.1.2), z.2)) := by
  exact ((((Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
    ((primrec_normalizeIndex Z Q).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).pair
    ((primrec_normalizeIndex Z R).comp
      (Primrec.snd.comp Primrec.fst))).pair Primrec.snd

theorem primrec_typedProject0ToPair (Z Q R : STObjectCode) :
    Primrec (typedProject0ToPairPacked Z Q R) :=
  (primrec_project0ToPair.comp (primrec_typedUnaryArguments Z Q R)).of_eq
    (fun _ => rfl)

theorem primrec_typedProject1ToPair (Z Q R : STObjectCode) :
    Primrec (typedProject1ToPairPacked Z Q R) :=
  (primrec_project1ToPair.comp (primrec_typedUnaryArguments Z Q R)).of_eq
    (fun _ => rfl)

theorem primrec_typedPairToLeft (Z Q R : STObjectCode) :
    Primrec (typedPairToLeftPacked Z Q R) :=
  (primrec_pairToLeft.comp (primrec_typedUnaryArguments Z Q R)).of_eq
    (fun _ => rfl)

theorem primrec_typedPairToRight (Z Q R : STObjectCode) :
    Primrec (typedPairToRightPacked Z Q R) :=
  (primrec_pairToRight.comp (primrec_typedUnaryArguments Z Q R)).of_eq
    (fun _ => rfl)

theorem primrec_typedComponentsToPair (Z Q R : STObjectCode) :
    Primrec (typedComponentsToPairPacked Z Q R) :=
  (primrec_componentsToPair.comp (primrec_typedBinaryArguments Z Q R)).of_eq
    (fun _ => rfl)

/-! ## Correctness at the typed endpoints -/

theorem reTheory_typedProject0ToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) {p a b n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (typedProject0Representative Z Q R a b) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (typedProject0ToPair Z Q R p a b n)
      (definednessTag (typedPairRepresentative Z Q R a b) n) :=
  reTheoryProof_T_project0ToPair T hRE hp

theorem reTheory_typedProject1ToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) {p a b n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (typedProject1Representative Z Q R a b) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (typedProject1ToPair Z Q R p a b n)
      (definednessTag (typedPairRepresentative Z Q R a b) n) :=
  reTheoryProof_T_project1ToPair T hRE hp

theorem reTheory_typedPairToLeft
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) {p a b n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (typedPairRepresentative Z Q R a b) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (typedPairToLeft Z Q R p a b n)
      (definednessTag (typedLeftRepresentative Z Q a) n) :=
  reTheoryProof_T_pairToLeft T hRE hp

theorem reTheory_typedPairToRight
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) {p a b n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (typedPairRepresentative Z Q R a b) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (typedPairToRight Z Q R p a b n)
      (definednessTag (typedRightRepresentative Z R b) n) :=
  reTheoryProof_T_pairToRight T hRE hp

theorem reTheory_typedComponentsToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) {p h a b n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (typedLeftRepresentative Z Q a) n))
    (hh : Proof_T (reTheoryProductTheoryPresentation T hRE) h
      (definednessTag (typedRightRepresentative Z R b) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (typedComponentsToPair Z Q R p h a b n)
      (definednessTag (typedPairRepresentative Z Q R a b) n) :=
  reTheoryProof_T_componentsToPair T hRE hp hh

theorem reTheory_typedPair_definedness_iff
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) (a b n : ℕ) :
    T ⊢ (definednessFormula (typedPairRepresentative Z Q R a b)).val/[n] ↔
      ∃ p : ℕ, Proof_T (reTheoryProductTheoryPresentation T hRE) p
        (definednessTag (typedPairRepresentative Z Q R a b) n) :=
  reTheory_provable_definedness_iff_exists_product_proof_T T hRE _ _

theorem reTheory_typedProject0_definedness_iff
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) (a b n : ℕ) :
    T ⊢ (definednessFormula
        (typedProject0Representative Z Q R a b)).val/[n] ↔
      ∃ p : ℕ, Proof_T (reTheoryProductTheoryPresentation T hRE) p
        (definednessTag (typedProject0Representative Z Q R a b) n) :=
  reTheory_provable_definedness_iff_exists_product_proof_T T hRE _ _

theorem reTheory_typedProject1_definedness_iff
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z Q R : STObjectCode) (a b n : ℕ) :
    T ⊢ (definednessFormula
        (typedProject1Representative Z Q R a b)).val/[n] ↔
      ∃ p : ℕ, Proof_T (reTheoryProductTheoryPresentation T hRE) p
        (definednessTag (typedProject1Representative Z Q R a b) n) :=
  reTheory_provable_definedness_iff_exists_product_proof_T T hRE _ _

/-! ## Identity-program evidence at input zero -/

def omegaIdentityRepresentative : ℕ :=
  normalizeIndex .omega .omega Kleene.identityIndex

theorem pa_proves_omegaIdentity_definedness_zero :
    𝗣𝗔 ⊢
      (definednessFormula omegaIdentityRepresentative).val/[(0 : ℕ)] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, definednessFormula_instance_eval,
    definednessFormula_eval]
  refine ⟨0, ?_⟩
  rw [omegaIdentityRepresentative, eventualGraph_normalizeIndex_eval]
  exact ⟨memberFormula_omega_eval _,
    (eventualGraph_identityIndex_eval _ _).mpr rfl,
    memberFormula_omega_eval _⟩

theorem reTheory_omegaIdentity_product_evidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ p : ℕ,
      Proof_T (reTheoryProductTheoryPresentation T hRE) p
        (definednessTag omegaIdentityRepresentative 0) ∧
      Proof_T (reTheoryProductTheoryPresentation T hRE)
        (componentsToPair p p omegaIdentityRepresentative
          omegaIdentityRepresentative 0)
        (definednessTag
          (pairIndex omegaIdentityRepresentative omegaIdentityRepresentative)
          0) ∧
      Proof_T (reTheoryProductTheoryPresentation T hRE)
        (pairToLeft
          (componentsToPair p p omegaIdentityRepresentative
            omegaIdentityRepresentative 0)
          omegaIdentityRepresentative omegaIdentityRepresentative 0)
        (definednessTag omegaIdentityRepresentative 0) ∧
      Proof_T (reTheoryProductTheoryPresentation T hRE)
        (pairToRight
          (componentsToPair p p omegaIdentityRepresentative
            omegaIdentityRepresentative 0)
          omegaIdentityRepresentative omegaIdentityRepresentative 0)
        (definednessTag omegaIdentityRepresentative 0) := by
  have hT : T ⊢
      (definednessFormula omegaIdentityRepresentative).val/[(0 : ℕ)] :=
    WeakerThan.pbl pa_proves_omegaIdentity_definedness_zero
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_definedness_iff_exists_product_proof_T
      T hRE omegaIdentityRepresentative 0).mp hT
  have hpair := reTheoryProof_T_componentsToPair T hRE hp hp
  exact ⟨p, hp, hpair,
    reTheoryProof_T_pairToLeft T hRE hpair,
    reTheoryProof_T_pairToRight T hRE hpair⟩

theorem reTheory_omegaIdentity_project0Evidence_to_pair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag
        (project0PairIndex omegaIdentityRepresentative
          omegaIdentityRepresentative) 0)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (project0ToPair p omegaIdentityRepresentative
        omegaIdentityRepresentative 0)
      (definednessTag
        (pairIndex omegaIdentityRepresentative omegaIdentityRepresentative)
        0) :=
  reTheoryProof_T_project0ToPair T hRE hp

theorem reTheory_omegaIdentity_project1Evidence_to_pair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag
        (project1PairIndex omegaIdentityRepresentative
          omegaIdentityRepresentative) 0)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (project1ToPair p omegaIdentityRepresentative
        omegaIdentityRepresentative 0)
      (definednessTag
        (pairIndex omegaIdentityRepresentative omegaIdentityRepresentative)
        0) :=
  reTheoryProof_T_project1ToPair T hRE hp

end

end FailureOfComposition.NumericalProductProofs
