/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionTheta.RETheory
import FailureOfComposition.NumericalExtensionComposition.Categorical

/-!
# The typed B1(8) theta arrow

Fix a coded object `Z` and `o : object T Z ⟶ omegaObject T`.  The theta arrow
first applies `o` and the identity to the two input coordinates, then applies
the finite-extension partial identity, and finally takes the actual typed
second projection.  A supported representative of `o` is chosen externally
once; no effective choice from quotient classes is asserted.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman CategoryTheory
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionTheta

open CodedObjectMembership ConcreteEvaluator FiniteExtensionChecker
open NumericalExtensionComposition NumericalExtensionProofs
open NumericalProofBridge ProofSearch TypedNearProduct
open TypedProgramCategory UniformIndexQuotient
open PCategoryStruct

noncomputable section

/-! ## Arrow and representative -/

/-- The typed theta arrow for `o`.  In categorical order it is
`(o boxtimes 1)`, followed by the extension domain and second projection. -/
def thetaArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T) :
    nearProd (object T Z) (omegaObject T) ⟶ omegaObject T :=
  (nearProd_map o (𝟙 (omegaObject T)) ≫
    (extensionDomain T).hom) ≫
      p1 (omegaObject T) (omegaObject T)

/-- The selected explicit representative of the typed theta arrow. -/
def thetaRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T) : ℕ :=
  thetaIndex (chosenOmegaRepresentative T Z o)

@[simp] theorem thetaArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T) :
    (thetaArrow T Z o).val =
      (p1 (omegaObject T) (omegaObject T)).val *
        ((extensionDomain T).hom.val *
          (nearProd_map o (𝟙 (omegaObject T))).val) :=
  rfl

/-- The explicit numerical theta program represents the actual typed
composite.  This is equality of quotient classes, not equality of raw
program indices. -/
theorem classOf_thetaRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T) :
    classOf T (thetaRepresentative T Z o) = (thetaArrow T Z o).val := by
  have hp1 : (p1 (omegaObject T) (omegaObject T)).val =
      classOf T secondProjectionIndex := by
    calc
      (p1 (omegaObject T) (omegaObject T)).val =
          secondProjectionClass T * objectIdempotent T PairOmega := by
        simpa only [omegaObject, objectCode_object] using
          (p1_val T (omegaObject T) (omegaObject T))
      _ = classOf T secondProjectionIndex := by
        rw [objectIdempotent_pairOmega, mul_one]
        rfl
  have hk : (extensionDomain T).hom.val =
      classOf T extensionCheckerIndex := by
    rw [extensionDomain_hom, extensionCheckerArrow_val]
  have hprod : (nearProd_map o (𝟙 (omegaObject T))).val =
      tensorClass T o.val 1 := by
    calc
      (nearProd_map o (𝟙 (omegaObject T))).val =
          tensorClass T o.val
            (𝟙 (omegaObject T) : omegaObject T ⟶ omegaObject T).1 := rfl
      _ = tensorClass T o.val 1 := by
        rw [id_val]
        change tensorClass T o.val (objectIdempotent T .omega) = _
        rw [objectIdempotent_omega]
  rw [thetaRepresentative, thetaIndex, thetaArrow_val]
  rw [← mul_classOf, ← mul_classOf, ← tensorClass_classOf]
  rw [hp1, hk, hprod, classOf_chosenOmegaRepresentative]
  rw [one_eq_classOf]

/-! ## Semantic categorical consequence -/

/-- The two supplied computation derivations give the typed theta
computation.  No equation from B1(7), totality, consistency, soundness, or
Delta-one hypothesis is used. -/
theorem theta_provableAt
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T)
    (t c i : ℕ)
    (ho : ProvableAt T o.val t c)
    (hchecker : ProvableAt T (extensionDomain T).hom.val
      (Nat.pair c i) (Nat.pair c i)) :
    ProvableAt T (thetaArrow T Z o).val (Nat.pair t i) i := by
  let q := chosenOmegaRepresentative T Z o
  have hq : T ⊢ (eventualGraph q).val/[t, c] := by
    rw [← provableAt_classOf]
    rw [classOf_chosenOmegaRepresentative]
    exact ho
  have hk : T ⊢ (eventualGraph extensionCheckerIndex).val/[
      Nat.pair c i, Nat.pair c i] := by
    rw [← provableAt_classOf]
    rw [← extensionCheckerArrow_val]
    simpa only [extensionDomain_hom] using hchecker
  have hscheme : T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (componentAndCheckerToThetaAxiomString q t c i) :=
    WeakerThan.pbl
      (provable_PA_meaning_componentAndCheckerToTheta q t c i)
  simp only [componentAndCheckerToThetaAxiomString,
    formulaMeaning_impString, checkerInstanceString, thetaInstanceString,
    formulaMeaning_rightInstanceString, eventualFamily] at hscheme
  have htheta := Entailment.mdp (Entailment.mdp hscheme hq) hk
  have hpv : ProvableAt T (classOf T (thetaRepresentative T Z o))
      (Nat.pair t i) i := by
    rw [provableAt_classOf]
    exact htheta
  rw [classOf_thetaRepresentative] at hpv
  exact hpv

/-- Equivalent form with a `T`-derivation of the canonical closed
`Ext(c,i)` instance. -/
theorem theta_provableAt_of_extension
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T)
    (t c i : ℕ)
    (ho : ProvableAt T o.val t c)
    (hext : T ⊢ extensionFormula.val/[c, i]) :
    ProvableAt T (thetaArrow T Z o).val (Nat.pair t i) i :=
  theta_provableAt T Z o t c i ho
    ((extensionDomain_provableAt_iff T c i).mpr hext)

/-! ## Exact supplied-code consequences -/

theorem reTheory_componentAndCheckerToTheta_typed
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) [𝗣𝗔 ⪯ T]
    (o : object T Z ⟶ omegaObject T)
    {p s t c i : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
      (rightInstanceCode (chosenOmegaRepresentative T Z o) t c))
    (hs : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
      (checkerInstanceCode c i)) :
    Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
      (componentAndCheckerToTheta p s
        (chosenOmegaRepresentative T Z o) t c i)
      (thetaInstanceCode (chosenOmegaRepresentative T Z o) t i) :=
  reTheoryProof_T_componentAndCheckerToTheta T hRE hp hs

theorem reTheory_componentAndExtToTheta_typed
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) [𝗣𝗔 ⪯ T]
    (o : object T Z ⟶ omegaObject T)
    {p s t c i : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
      (rightInstanceCode (chosenOmegaRepresentative T Z o) t c))
    (hs : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
      (extensionInstanceCode c i)) :
    Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
      (componentAndExtToTheta p s
        (chosenOmegaRepresentative T Z o) t c i)
      (thetaInstanceCode (chosenOmegaRepresentative T Z o) t i) :=
  reTheoryProof_T_componentAndExtToTheta T hRE hp hs

/-- Semantic premises provide existential numerical evidence at the exact
selected representative endpoints.  This is an existence theorem, not a
primitive-recursive extraction from opaque derivability. -/
theorem exists_thetaEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (o : object T Z ⟶ omegaObject T)
    (t c i : ℕ)
    (ho : ProvableAt T o.val t c)
    (hchecker : ProvableAt T (extensionDomain T).hom.val
      (Nat.pair c i) (Nat.pair c i)) :
    ∃ p s : ℕ,
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (rightInstanceCode (chosenOmegaRepresentative T Z o) t c) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
        (checkerInstanceCode c i) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
        (componentAndCheckerToTheta p s
          (chosenOmegaRepresentative T Z o) t c i)
        (thetaInstanceCode (chosenOmegaRepresentative T Z o) t i) := by
  let q := chosenOmegaRepresentative T Z o
  have hq : T ⊢ (eventualGraph q).val/[t, c] := by
    rw [← provableAt_classOf]
    rw [classOf_chosenOmegaRepresentative]
    exact ho
  have hk : T ⊢ (eventualGraph extensionCheckerIndex).val/[
      Nat.pair c i, Nat.pair c i] := by
    rw [← provableAt_classOf]
    rw [← extensionCheckerArrow_val]
    simpa only [extensionDomain_hom] using hchecker
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_right_iff_exists_extensionThetaProof_T
      T hRE q t c).mp hq
  obtain ⟨s, hs⟩ :=
    (reTheory_provable_checker_iff_exists_extensionThetaProof_T
      T hRE c i).mp hk
  exact ⟨p, s, hp, hs,
    reTheoryProof_T_componentAndCheckerToTheta T hRE hp hs⟩

end

end FailureOfComposition.NumericalExtensionTheta
