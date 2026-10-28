/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionComposition.Categorical

/-!
# Constant-zero and identity application of the B1(7) maps

The left component below is the total constant-zero program, not the
nowhere-defined categorical zero.  The right component is the production
identity.  Their partial pairing has output `(0,t)`.  The proof that the
finite-extension checker fixes this pairing is uniform in the internal input
of every PA model: it uses vacuity of `Ext(0,i)` internally, rather than a
family of closed standard instances.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman CategoryTheory
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalExtensionComposition

open CodedObjectMembership ConcreteEvaluator FiniteExtensionChecker
open NumericalExtensionProofs NumericalProductProofs ProofSearch
open TypedNearProduct TypedProgramCategory UniformIndexQuotient
open TypedChoice
open PCategoryStruct

noncomputable section

def applicationZeroArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ omegaObject T :=
  omegaConstantZeroArrow T

def applicationIdentityArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ omegaObject T :=
  arrowOfIndex T .omega .omega Kleene.identityIndex

def applicationPairArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ object T PairOmega :=
  partialPairing (applicationZeroArrow T) (applicationIdentityArrow T)

def applicationZeroRepresentative : ℕ :=
  normalizeIndex .omega .omega (encode Nat.Partrec.Code.zero)

def applicationIdentityRepresentative : ℕ :=
  normalizeIndex .omega .omega Kleene.identityIndex

def applicationPairRepresentative : ℕ :=
  pairIndex applicationZeroRepresentative applicationIdentityRepresentative

theorem applicationIdentityArrow_eq_id
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    applicationIdentityArrow T = 𝟙 (omegaObject T) := by
  apply arrowOfIndex_eq_of_class
  calc
    classOf T Kleene.identityIndex = 1 := (one_eq_classOf T).symm
    _ = (𝟙 (omegaObject T) :
        omegaObject T ⟶ omegaObject T).1 := by
      rw [id_val]
      change 1 = objectIdempotent T .omega
      rw [objectIdempotent_omega]

theorem classOf_applicationPairRepresentative
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    classOf T applicationPairRepresentative = (applicationPairArrow T).val := by
  calc
    classOf T applicationPairRepresentative =
        pairClass T (classOf T applicationZeroRepresentative)
          (classOf T applicationIdentityRepresentative) := rfl
    _ = pairClass T (applicationZeroArrow T).val
        (applicationIdentityArrow T).val := by
      rw [applicationZeroRepresentative, applicationIdentityRepresentative,
        applicationZeroArrow, TypedChoice.omegaConstantZeroArrow,
        arrowOfIndex_val, applicationIdentityArrow, arrowOfIndex_val]
    _ = (applicationPairArrow T).val :=
      (partialPairing_val T (applicationZeroArrow T)
        (applicationIdentityArrow T)).symm

/-! ## Uniform equations -/

theorem pa_proves_applicationZero_totality :
    𝗣𝗔 ⊢ typedTotalitySentence .omega .omega
      (encode Nat.Partrec.Code.zero) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, typedTotalitySentence_eval]
  intro x _
  exact ⟨0, (eventualGraph_normalize_constantZero_eval x 0).mpr rfl⟩

theorem applicationZeroArrow_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    RestrictionCategory.isTotal (applicationZeroArrow T) := by
  change RestrictionCategory.isTotal
    (arrowOfIndex T .omega .omega (encode Nat.Partrec.Code.zero))
  apply (arrowOfIndex_isTotal_iff_proves_typedTotality T .omega .omega
    (encode Nat.Partrec.Code.zero)).mpr
  exact WeakerThan.pbl pa_proves_applicationZero_totality

theorem application_projectionEquation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    applicationPairArrow T ≫ p1 (omegaObject T) (omegaObject T) =
      applicationIdentityArrow T := by
  have hprojection := typed_partialPairing_p1 T
    (applicationZeroArrow T) (applicationIdentityArrow T)
  calc
    applicationPairArrow T ≫ p1 (omegaObject T) (omegaObject T) =
        RestrictionCategory.rst (applicationZeroArrow T) ≫
          applicationIdentityArrow T := hprojection
    _ = applicationIdentityArrow T := by
      rw [applicationZeroArrow_isTotal T, Category.id_comp]

/-- The checker fixes the application pairing uniformly.  The quantified
checker input is internal to the model. -/
theorem pa_applicationPair_checker_eq :
    EqIndex 𝗣𝗔
      (UniformIndexQuotient.compIndex extensionCheckerIndex
        applicationPairRepresentative)
      applicationPairRepresentative := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hp, hk⟩
    have hyz := (eventualGraph_extensionCheckerIndex_eval z y).mp hk |>.1
    simpa [hyz] using hp
  · intro hp
    refine ⟨y, hp, ?_⟩
    rw [applicationPairRepresentative, eventualGraph_pairIndex_eval] at hp
    obtain ⟨a, b, ha, -, rfl⟩ := hp
    have ha0 : a = 0 :=
      (eventualGraph_normalize_constantZero_eval x a).mp ha
    subst a
    rw [eventualGraph_extensionCheckerIndex_pair_eval]
    refine ⟨rfl, ?_⟩
    rw [extensionFormula_eval_bounded]
    simp

theorem application_extensionEquation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    applicationPairArrow T ≫ (extensionDomain T).hom =
      applicationPairArrow T := by
  apply CodedHom.ext
  have heq : EqIndex T
      (UniformIndexQuotient.compIndex extensionCheckerIndex
        applicationPairRepresentative)
      applicationPairRepresentative :=
    WeakerThan.pbl pa_applicationPair_checker_eq
  have hclasses : classOf T
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          applicationPairRepresentative) =
      classOf T applicationPairRepresentative :=
    (classOf_eq_classOf_iff T _ _).mpr heq
  calc
    (applicationPairArrow T ≫ (extensionDomain T).hom).val =
        classOf T extensionCheckerIndex *
          classOf T applicationPairRepresentative := by
      rw [comp_val, extensionDomain_hom, extensionCheckerArrow_val,
        ← classOf_applicationPairRepresentative]
    _ = classOf T
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          applicationPairRepresentative) := mul_classOf T _ _
    _ = classOf T applicationPairRepresentative := hclasses
    _ = (applicationPairArrow T).val :=
      classOf_applicationPairRepresentative T

/-! ## Input-zero consequences and numerical evidence -/

theorem applicationZero_provableAt_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProvableAt T (applicationZeroArrow T).val 0 0 := by
  rw [applicationZeroArrow, omegaConstantZeroArrow, arrowOfIndex_val,
    provableAt_classOf]
  have hpa : 𝗣𝗔 ⊢
      (eventualGraph applicationZeroRepresentative).val/[
        (0 : ℕ), (0 : ℕ)] := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff, graph_instance_eval, applicationZeroRepresentative,
      eventualGraph_normalize_constantZero_eval]
    simp only [ORingStructure.zero_eq_zero]
  exact WeakerThan.pbl hpa

theorem applicationIdentity_provableAt_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProvableAt T (applicationIdentityArrow T).val 0 0 := by
  rw [applicationIdentityArrow_eq_id]
  have hval : (𝟙 (omegaObject T) :
      omegaObject T ⟶ omegaObject T).1 =
      (1 : ProgramQuotient T) := by
    rw [id_val]
    change objectIdempotent T .omega = 1
    exact objectIdempotent_omega T
  rw [hval]
  exact provableAt_one T 0

theorem application_domain_pair_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProvableAt T (domainArrow T (applicationPairArrow T)).val 0 0 :=
  projectionEquation_domain_pair T .omega (applicationZeroArrow T)
    (applicationIdentityArrow T) 0 0 (application_projectionEquation T)
    (applicationIdentity_provableAt_zero T)

theorem application_domain_zeroComponent_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProvableAt T (domainArrow T (applicationZeroArrow T)).val 0 0 :=
  projectionEquation_domain_left T .omega (applicationZeroArrow T)
    (applicationIdentityArrow T) 0 0 (application_projectionEquation T)
    (applicationIdentity_provableAt_zero T)

theorem application_proves_empty_extension
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    T ⊢ extensionFormula.val/[(0 : ℕ), (0 : ℕ)] :=
  extensionEquation_proves_extension T .omega (applicationZeroArrow T)
    (applicationIdentityArrow T) 0 0 0 (application_extensionEquation T)
    (applicationZero_provableAt_zero T)
    (applicationIdentity_provableAt_zero T)

theorem application_empty_preceq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Preceq T 0 0 :=
  extensionEquation_preceq T .omega (applicationZeroArrow T)
    (applicationIdentityArrow T) 0 0 0 (application_extensionEquation T)
    (applicationZero_provableAt_zero T)
    (applicationIdentity_provableAt_zero T)

/-- At input zero, both actual input computations have numerical proof
evidence, and the four composed maps produce proofs at `D(P,0)`, `D(q,0)`,
`C(0,0)`, and `X(0,0)` in the common presentation. -/
theorem reTheory_application_composedEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    (∃ u p : ℕ,
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
        (equalityCode
          (project1Representative T .omega (applicationZeroArrow T)
            (applicationIdentityArrow T))
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T))) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (rightInstanceCode
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T)) 0 0) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (projectionEqualityToPair u p
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T))
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T)) 0 0)
        (definednessTag
          (pairRepresentative T .omega (applicationZeroArrow T)
            (applicationIdentityArrow T)) 0) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (projectionEqualityToLeft u p
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T))
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T)) 0 0)
        (definednessTag
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T)) 0))
    ∧
    (∃ v a b : ℕ,
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
        (equalityCode
          (UniformIndexQuotient.compIndex extensionCheckerIndex
            (pairRepresentative T .omega (applicationZeroArrow T)
              (applicationIdentityArrow T)))
          (pairRepresentative T .omega (applicationZeroArrow T)
            (applicationIdentityArrow T))) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
        (rightInstanceCode
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T))
          0 0) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
        (rightInstanceCode
          (chosenOmegaRepresentative T .omega (applicationIdentityArrow T))
          0 0) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (componentValuesToChecker v a b
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T))
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T)) 0 0 0)
        (checkerInstanceCode 0 0) ∧
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
        (componentValuesToExt v a b
          (chosenOmegaRepresentative T .omega (applicationZeroArrow T))
          (chosenOmegaRepresentative T .omega
            (applicationIdentityArrow T)) 0 0 0)
        (extensionInstanceCode 0 0)) := by
  constructor
  · exact exists_projectionEquationEvidence T hRE .omega
      (applicationZeroArrow T) (applicationIdentityArrow T) 0 0
      (application_projectionEquation T)
      (applicationIdentity_provableAt_zero T)
  · exact exists_extensionEquationEvidence T hRE .omega
      (applicationZeroArrow T) (applicationIdentityArrow T) 0 0 0
      (application_extensionEquation T)
      (applicationZero_provableAt_zero T)
      (applicationIdentity_provableAt_zero T)

end

end FailureOfComposition.NumericalExtensionComposition
