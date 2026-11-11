/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.RETheory
public import FailureOfComposition.NumericalProductProofs.Typed
public import FailureOfComposition.TypedChoice

/-!
# The composed B1(7) rules in the typed program category

Fix a coded object `Z` and arrows `o r : object T Z ⟶ omegaObject T`.
This file chooses one raw representative for each arrow and immediately
normalizes it.  The resulting external indices `q` and `r`, their pairing
`P`, and the second-projection composite `J` are then used unchanged in the
semantic and numerical statements below.

The first conclusion is only definedness: it does not choose a standard
output of `o`.  The second conclusion consumes separately supplied proofs of
the two component values.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman CategoryTheory
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionComposition

open CodedObjectMembership ConcreteEvaluator FiniteExtensionChecker
open NumericalExtensionProofs
open NumericalProductProofs ProofSearch TypedNearProduct
open TypedProgramCategory UniformIndexQuotient
open PCategoryStruct

noncomputable section

/-! ## One normalized pair of representatives -/

/-- An externally selected raw representative of an arrow into `omega`. -/
def chosenOmegaRawIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) : ℕ :=
  Classical.choose (exists_arrowOfIndex T Z .omega f)

theorem arrowOfIndex_chosenOmegaRawIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) :
    arrowOfIndex T Z .omega (chosenOmegaRawIndex T Z f) = f :=
  Classical.choose_spec (exists_arrowOfIndex T Z .omega f)

/-- The supported representative used for the remainder of the construction.
The choice is external; no effective selection from quotient arrows is
claimed. -/
def chosenOmegaRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) : ℕ :=
  normalizeIndex Z .omega (chosenOmegaRawIndex T Z f)

theorem classOf_chosenOmegaRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) :
    classOf T (chosenOmegaRepresentative T Z f) = f.val := by
  have h := congrArg Subtype.val (arrowOfIndex_chosenOmegaRawIndex T Z f)
  rw [arrowOfIndex_val] at h
  exact h

theorem pa_proves_chosenOmegaRepresentative_support
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) :
    𝗣𝗔 ⊢ supportSentence Z .omega
      (chosenOmegaRepresentative T Z f) :=
  pa_proves_normalized_support Z .omega (chosenOmegaRawIndex T Z f)

/-- The actual partial pairing of the two fixed typed arrows. -/
def b17Pair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) :
    object T Z ⟶ object T PairOmega :=
  partialPairing o r

/-- `P`, the selected production representative of the partial pairing. -/
def pairRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) : ℕ :=
  pairIndex (chosenOmegaRepresentative T Z o)
    (chosenOmegaRepresentative T Z r)

/-- `J`, the selected representative of the pairing followed by the second
projection. -/
def project1Representative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) : ℕ :=
  project1PairIndex (chosenOmegaRepresentative T Z o)
    (chosenOmegaRepresentative T Z r)

theorem classOf_pairRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) :
    classOf T (pairRepresentative T Z o r) = (b17Pair T Z o r).val := by
  calc
    classOf T (pairRepresentative T Z o r) =
        pairClass T (classOf T (chosenOmegaRepresentative T Z o))
          (classOf T (chosenOmegaRepresentative T Z r)) := rfl
    _ = pairClass T o.val r.val := by
      rw [classOf_chosenOmegaRepresentative,
        classOf_chosenOmegaRepresentative]
    _ = (b17Pair T Z o r).val :=
      (partialPairing_val T o r).symm

theorem classOf_project1Representative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) :
    classOf T (project1Representative T Z o r) =
      (b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T)).val := by
  let a := chosenOmegaRawIndex T Z o
  let b := chosenOmegaRawIndex T Z r
  let j := typedProject1Representative Z .omega .omega a b
  have harrow :=
    typedProject1Representative_arrow T Z .omega .omega a b
  rw [show arrowOfIndex T Z .omega a = o from
      arrowOfIndex_chosenOmegaRawIndex T Z o,
    show arrowOfIndex T Z .omega b = r from
      arrowOfIndex_chosenOmegaRawIndex T Z r] at harrow
  have hval := congrArg Subtype.val harrow
  rw [arrowOfIndex_val] at hval
  have hsupport : T ⊢ supportSentence Z .omega j :=
    typedProject1Representative_support_in T Z .omega .omega a b
  have heq : EqIndex T (normalizeIndex Z .omega j) j :=
    (proves_support_iff_eqIndex_normalize T Z .omega j).mp hsupport
  have hclass : classOf T (normalizeIndex Z .omega j) = classOf T j :=
    (classOf_eq_classOf_iff T _ _).mpr heq
  change classOf T j = (partialPairing o r ≫
    p1 (omegaObject T) (omegaObject T)).val
  exact hclass.symm.trans hval

theorem classOf_domain_pairRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) :
    classOf T (domainIndex (pairRepresentative T Z o r)) =
      (domainArrow T (b17Pair T Z o r)).val := by
  change classOf T (domainIndex (pairRepresentative T Z o r)) =
    domainClass T (b17Pair T Z o r).val
  rw [← classOf_pairRepresentative, domainClass_classOf]

theorem classOf_domain_chosenOmegaRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (f : object T Z ⟶ omegaObject T) :
    classOf T (domainIndex (chosenOmegaRepresentative T Z f)) =
      (domainArrow T f).val := by
  change classOf T (domainIndex (chosenOmegaRepresentative T Z f)) =
    domainClass T f.val
  rw [← classOf_chosenOmegaRepresentative, domainClass_classOf]

/-! ## Categorical equations as mixed representative equalities -/

theorem mixedEquality_of_projectionEquation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r) :
    T ⊢ uniformSentence
      (firstSuccessGraph (project1Representative T Z o r))
      (eventualGraph (chosenOmegaRepresentative T Z r)) := by
  have hval := congrArg Subtype.val heq
  have hclass :
      classOf T (project1Representative T Z o r) =
        classOf T (chosenOmegaRepresentative T Z r) :=
    (classOf_project1Representative T Z o r).trans
      (hval.trans (classOf_chosenOmegaRepresentative T Z r).symm)
  have hindex : EqIndex T (project1Representative T Z o r)
      (chosenOmegaRepresentative T Z r) :=
    (classOf_eq_classOf_iff T _ _).mp hclass
  exact uniform_trans
    (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph _)) hindex

theorem mixedEquality_of_extensionEquation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T)
    (heq : b17Pair T Z o r ≫ (extensionDomain T).hom =
      b17Pair T Z o r) :
    T ⊢ uniformSentence
      (firstSuccessGraph
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairRepresentative T Z o r)))
      (eventualGraph (pairRepresentative T Z o r)) := by
  have hval := congrArg Subtype.val heq
  have hclass : classOf T
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairRepresentative T Z o r)) =
      classOf T (pairRepresentative T Z o r) := by
    calc
      classOf T (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairRepresentative T Z o r)) =
          classOf T extensionCheckerIndex *
            classOf T (pairRepresentative T Z o r) :=
        (mul_classOf T _ _).symm
      _ = (extensionDomain T).hom.val * (b17Pair T Z o r).val := by
        rw [extensionDomain_hom, extensionCheckerArrow_val,
          classOf_pairRepresentative]
      _ = (b17Pair T Z o r ≫ (extensionDomain T).hom).val := rfl
      _ = (b17Pair T Z o r).val := hval
      _ = classOf T (pairRepresentative T Z o r) :=
        (classOf_pairRepresentative T Z o r).symm
  have hindex : EqIndex T
      (UniformIndexQuotient.compIndex extensionCheckerIndex
        (pairRepresentative T Z o r))
      (pairRepresentative T Z o r) :=
    (classOf_eq_classOf_iff T _ _).mp hclass
  exact uniform_trans
    (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph _)) hindex

/-! ## The two typed B1(7) consequences -/

theorem projectionEquation_domain_pair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t i : ℕ)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r)
    (hr : ProvableAt T r.val t i) :
    ProvableAt T (domainArrow T (b17Pair T Z o r)).val t t := by
  let q := chosenOmegaRepresentative T Z o
  let s := chosenOmegaRepresentative T Z r
  let p := pairRepresentative T Z o r
  let j := project1Representative T Z o r
  have hr' : T ⊢ (eventualGraph s).val/[t, i] := by
    rw [← provableAt_classOf]
    rw [classOf_chosenOmegaRepresentative]
    exact hr
  have hmixed := mixedEquality_of_projectionEquation T Z o r heq
  have hscheme : T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (projectionDefinednessAxiomString j s t i) :=
    WeakerThan.pbl
      (provable_PA_meaning_projectionDefinedness j s t i)
  simp only [projectionDefinednessAxiomString,
    formulaMeaning_impString, formulaMeaning_equalityString,
    formulaMeaning_rightInstanceString, definednessString,
    firstSuccessFamily, eventualFamily] at hscheme
  have hJ := Entailment.mdp (Entailment.mdp hscheme hmixed) hr'
  have hproject : T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (project1ToPairAxiomString q s t) :=
    WeakerThan.pbl
      (NumericalProductProofs.provable_PA_meaning_project1ToPair q s t)
  simp only [project1ToPairAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily] at hproject
  have hP := Entailment.mdp hproject hJ
  have hpv : ProvableAt T (classOf T (domainIndex p)) t t := by
    rw [provableAt_classOf]
    exact hP
  rw [classOf_domain_pairRepresentative] at hpv
  exact hpv

theorem projectionEquation_domain_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t i : ℕ)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r)
    (hr : ProvableAt T r.val t i) :
    ProvableAt T (domainArrow T o).val t t := by
  let q := chosenOmegaRepresentative T Z o
  let s := chosenOmegaRepresentative T Z r
  let p := pairRepresentative T Z o r
  have hpair := projectionEquation_domain_pair T Z o r t i heq hr
  have hP : T ⊢ (eventualGraph (domainIndex p)).val/[t, t] := by
    rw [← provableAt_classOf]
    rw [classOf_domain_pairRepresentative]
    exact hpair
  have hleft : T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (pairToLeftAxiomString q s t) :=
    WeakerThan.pbl
      (NumericalProductProofs.provable_PA_meaning_pairToLeft q s t)
  simp only [pairToLeftAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily] at hleft
  have hq := Entailment.mdp hleft hP
  have hpv : ProvableAt T (classOf T (domainIndex q)) t t := by
    rw [provableAt_classOf]
    exact hq
  rw [classOf_domain_chosenOmegaRepresentative] at hpv
  exact hpv

theorem projectionEquation_definedness_pair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t i : ℕ)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r)
    (hr : ProvableAt T r.val t i) :
    T ⊢ (definednessFormula (pairRepresentative T Z o r)).val/[t] := by
  have h := projectionEquation_domain_pair T Z o r t i heq hr
  rw [← classOf_domain_pairRepresentative,
    provableAt_classOf] at h
  exact Entailment.mdp
    (WeakerThan.pbl (pa_proves_domain_to_definednessInstance
      (pairRepresentative T Z o r) t)) h

theorem projectionEquation_definedness_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t i : ℕ)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r)
    (hr : ProvableAt T r.val t i) :
    T ⊢ (definednessFormula (chosenOmegaRepresentative T Z o)).val/[t] := by
  have h := projectionEquation_domain_left T Z o r t i heq hr
  rw [← classOf_domain_chosenOmegaRepresentative,
    provableAt_classOf] at h
  exact Entailment.mdp
    (WeakerThan.pbl (pa_proves_domain_to_definednessInstance
      (chosenOmegaRepresentative T Z o) t)) h

theorem extensionEquation_proves_extension
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t c i : ℕ)
    (heq : b17Pair T Z o r ≫ (extensionDomain T).hom =
      b17Pair T Z o r)
    (ho : ProvableAt T o.val t c)
    (hr : ProvableAt T r.val t i) :
    T ⊢ extensionFormula.val/[c, i] := by
  let q := chosenOmegaRepresentative T Z o
  let s := chosenOmegaRepresentative T Z r
  have ho' : T ⊢ (eventualGraph q).val/[t, c] := by
    rw [← provableAt_classOf]
    rw [classOf_chosenOmegaRepresentative]
    exact ho
  have hr' : T ⊢ (eventualGraph s).val/[t, i] := by
    rw [← provableAt_classOf]
    rw [classOf_chosenOmegaRepresentative]
    exact hr
  have hmixed := mixedEquality_of_extensionEquation T Z o r heq
  have hscheme : T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (componentValuesToCheckerAxiomString q s t c i) :=
    WeakerThan.pbl
      (provable_PA_meaning_componentValuesToChecker q s t c i)
  simp only [componentValuesToCheckerAxiomString,
    formulaMeaning_impString, formulaMeaning_equalityString,
    formulaMeaning_rightInstanceString, checkerInstanceString,
    firstSuccessFamily, eventualFamily] at hscheme
  have hchecker := Entailment.mdp
    (Entailment.mdp (Entailment.mdp hscheme hmixed) ho') hr'
  exact (proves_checker_iff_extension T c i).mp hchecker

theorem extensionEquation_preceq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode)
    (o r : object T Z ⟶ omegaObject T) (t c i : ℕ)
    (heq : b17Pair T Z o r ≫ (extensionDomain T).hom =
      b17Pair T Z o r)
    (ho : ProvableAt T o.val t c)
    (hr : ProvableAt T r.val t i) :
    Preceq T c i :=
  (proves_extensionFormula_iff_preceq T c i).mp
    (extensionEquation_proves_extension T Z o r t c i heq ho hr)

/-! ## Supplied proof codes and existence of numerical evidence -/

theorem reTheory_projectionEquationToPair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    {u p t i : ℕ}
    (hu : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
      (equalityCode (project1Representative T Z o r)
        (chosenOmegaRepresentative T Z r)))
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (rightInstanceCode (chosenOmegaRepresentative T Z r) t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (projectionEqualityToPair u p (chosenOmegaRepresentative T Z o)
        (chosenOmegaRepresentative T Z r) t i)
      (definednessTag (pairRepresentative T Z o r) t) :=
  reTheoryProof_T_projectionEqualityToPair T hRE hu hp

theorem reTheory_projectionEquationToLeft
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    {u p t i : ℕ}
    (hu : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
      (equalityCode (project1Representative T Z o r)
        (chosenOmegaRepresentative T Z r)))
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (rightInstanceCode (chosenOmegaRepresentative T Z r) t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (projectionEqualityToLeft u p (chosenOmegaRepresentative T Z o)
        (chosenOmegaRepresentative T Z r) t i)
      (definednessTag (chosenOmegaRepresentative T Z o) t) :=
  reTheoryProof_T_projectionEqualityToLeft T hRE hu hp

theorem reTheory_componentValuesToChecker_typed
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    {v a b t c i : ℕ}
    (hv : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
      (equalityCode
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairRepresentative T Z o r))
        (pairRepresentative T Z o r)))
    (ha : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
      (rightInstanceCode (chosenOmegaRepresentative T Z o) t c))
    (hb : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
      (rightInstanceCode (chosenOmegaRepresentative T Z r) t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (componentValuesToChecker v a b
        (chosenOmegaRepresentative T Z o)
        (chosenOmegaRepresentative T Z r) t c i)
      (checkerInstanceCode c i) :=
  reTheoryProof_T_componentValuesToChecker T hRE hv ha hb

theorem reTheory_componentValuesToExt_typed
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    {v a b t c i : ℕ}
    (hv : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
      (equalityCode
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairRepresentative T Z o r))
        (pairRepresentative T Z o r)))
    (ha : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
      (rightInstanceCode (chosenOmegaRepresentative T Z o) t c))
    (hb : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
      (rightInstanceCode (chosenOmegaRepresentative T Z r) t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (componentValuesToExt v a b
        (chosenOmegaRepresentative T Z o)
        (chosenOmegaRepresentative T Z r) t c i)
      (extensionInstanceCode c i) :=
  reTheoryProof_T_componentValuesToExt T hRE hv ha hb

theorem exists_projectionEquationEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    (t i : ℕ)
    (heq : b17Pair T Z o r ≫ p1 (omegaObject T) (omegaObject T) = r)
    (hr : ProvableAt T r.val t i) :
    ∃ u p : ℕ,
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
        (equalityCode (project1Representative T Z o r)
          (chosenOmegaRepresentative T Z r)) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (rightInstanceCode (chosenOmegaRepresentative T Z r) t i) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (projectionEqualityToPair u p (chosenOmegaRepresentative T Z o)
          (chosenOmegaRepresentative T Z r) t i)
        (definednessTag (pairRepresentative T Z o r) t) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (projectionEqualityToLeft u p (chosenOmegaRepresentative T Z o)
          (chosenOmegaRepresentative T Z r) t i)
        (definednessTag (chosenOmegaRepresentative T Z o) t) := by
  obtain ⟨u, hu⟩ :=
    (reTheory_provable_uniform_iff_exists_extensionCompositionProof_T
      T hRE _ _).mp (mixedEquality_of_projectionEquation T Z o r heq)
  have hr' : T ⊢ (eventualGraph
      (chosenOmegaRepresentative T Z r)).val/[t, i] := by
    rw [← provableAt_classOf, classOf_chosenOmegaRepresentative]
    exact hr
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_right_iff_exists_extensionCompositionProof_T
      T hRE _ t i).mp hr'
  exact ⟨u, p, hu, hp,
    reTheory_projectionEquationToPair T hRE Z o r hu hp,
    reTheory_projectionEquationToLeft T hRE Z o r hu hp⟩

theorem exists_extensionEquationEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o r : object T Z ⟶ omegaObject T)
    (t c i : ℕ)
    (heq : b17Pair T Z o r ≫ (extensionDomain T).hom =
      b17Pair T Z o r)
    (ho : ProvableAt T o.val t c)
    (hr : ProvableAt T r.val t i) :
    ∃ v a b : ℕ,
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
        (equalityCode
          (UniformIndexQuotient.compIndex extensionCheckerIndex
            (pairRepresentative T Z o r))
          (pairRepresentative T Z o r)) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
        (rightInstanceCode (chosenOmegaRepresentative T Z o) t c) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
        (rightInstanceCode (chosenOmegaRepresentative T Z r) t i) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (componentValuesToChecker v a b
          (chosenOmegaRepresentative T Z o)
          (chosenOmegaRepresentative T Z r) t c i)
        (checkerInstanceCode c i) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (componentValuesToExt v a b
          (chosenOmegaRepresentative T Z o)
          (chosenOmegaRepresentative T Z r) t c i)
        (extensionInstanceCode c i) := by
  obtain ⟨v, hv⟩ :=
    (reTheory_provable_uniform_iff_exists_extensionCompositionProof_T
      T hRE _ _).mp (mixedEquality_of_extensionEquation T Z o r heq)
  have ho' : T ⊢ (eventualGraph
      (chosenOmegaRepresentative T Z o)).val/[t, c] := by
    rw [← provableAt_classOf, classOf_chosenOmegaRepresentative]
    exact ho
  have hr' : T ⊢ (eventualGraph
      (chosenOmegaRepresentative T Z r)).val/[t, i] := by
    rw [← provableAt_classOf, classOf_chosenOmegaRepresentative]
    exact hr
  obtain ⟨a, ha⟩ :=
    (reTheory_provable_right_iff_exists_extensionCompositionProof_T
      T hRE _ t c).mp ho'
  obtain ⟨b, hb⟩ :=
    (reTheory_provable_right_iff_exists_extensionCompositionProof_T
      T hRE _ t i).mp hr'
  exact ⟨v, a, b, hv, ha, hb,
    reTheory_componentValuesToChecker_typed T hRE Z o r hv ha hb,
    reTheory_componentValuesToExt_typed T hRE Z o r hv ha hb⟩

end

end FailureOfComposition.NumericalExtensionComposition
