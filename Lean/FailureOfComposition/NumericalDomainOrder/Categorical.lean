/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalDomainOrder.RETheory
import FailureOfComposition.TypedChoice

/-!
# Categorical transfer along a domain inequality

This module applies the numerical domain-order rule to the actual
`DomSemilattice (omegaObject T)`.  It selects one normalized representative
for each omega endomorphism, proves that canonical index composition represents
diagrammatic categorical composition, and translates `rho ≤ S` into the mixed
first-success/eventual equality required by the numerical rule.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalDomainOrder

open ConcreteEvaluator NumericalProofBridge ProofSearch TypedProgramCategory
open UniformIndexQuotient

noncomputable section

/-! ## Selected normalized representatives -/

/-- An externally selected raw index for an omega endomorphism.  No effective
dependence on the quotient arrow is claimed. -/
noncomputable def chosenOmegaIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f : omegaObject T ⟶ omegaObject T) : ℕ :=
  Classical.choose (exists_arrowOfIndex T .omega .omega f)

theorem arrowOfIndex_chosenOmegaIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f : omegaObject T ⟶ omegaObject T) :
    arrowOfIndex T .omega .omega (chosenOmegaIndex T f) = f :=
  Classical.choose_spec (exists_arrowOfIndex T .omega .omega f)

/-- The supported normalized production representative selected for `f`. -/
noncomputable def normalizedOmegaIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f : omegaObject T ⟶ omegaObject T) : ℕ :=
  normalizeIndex .omega .omega (chosenOmegaIndex T f)

theorem classOf_normalizedOmegaIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f : omegaObject T ⟶ omegaObject T) :
    classOf T (normalizedOmegaIndex T f) = f.val := by
  have h := congrArg Subtype.val (arrowOfIndex_chosenOmegaIndex T f)
  rw [arrowOfIndex_val] at h
  exact h

/-- The selected representative has its declared omega-to-omega support in
PA. -/
theorem pa_proves_normalizedOmegaIndex_support
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f : omegaObject T ⟶ omegaObject T) :
    𝗣𝗔 ⊢ supportSentence .omega .omega (normalizedOmegaIndex T f) := by
  exact pa_proves_normalized_support .omega .omega (chosenOmegaIndex T f)

/-- Canonical composition of the two selected representatives represents
diagrammatic composition of the corresponding omega endomorphisms. -/
theorem classOf_normalizedOmegaIndex_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f g : omegaObject T ⟶ omegaObject T) :
    classOf T
        (compIndex (normalizedOmegaIndex T g) (normalizedOmegaIndex T f)) =
      (f ≫ g).val := by
  calc
    classOf T
          (compIndex (normalizedOmegaIndex T g) (normalizedOmegaIndex T f)) =
        classOf T (normalizedOmegaIndex T g) *
          classOf T (normalizedOmegaIndex T f) :=
      (mul_classOf T _ _).symm
    _ = g.val * f.val := by
      rw [classOf_normalizedOmegaIndex, classOf_normalizedOmegaIndex]
    _ = (f ≫ g).val := rfl

/-! ## Provability transfer before numerical presentation -/

/-- A representative-level composition equality and a provable diagonal
computation for the inner program imply the corresponding computation for the
outer program.  This theorem needs only provability inclusion from PA. -/
theorem provableAt_of_comp_class_eq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {r s i : ℕ}
    (hcomp : classOf T (compIndex s r) = classOf T r)
    (hr : ProvableAt T (classOf T r) i i) :
    ProvableAt T (classOf T s) i i := by
  have hgr : EqIndex T (compIndex s r) r :=
    (classOf_eq_classOf_iff T _ _).mp hcomp
  have hmixed :
      T ⊢ uniformSentence (firstSuccessGraph (compIndex s r))
        (eventualGraph r) :=
    uniform_trans
      (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph
        (compIndex s r))) hgr
  have hschema : T ⊢
      FailureOfComposition.NumericalSpecialization.formulaMeaning
        FailureOfComposition.NumericalSpecialization.firstSuccessFamily
        FailureOfComposition.NumericalSpecialization.eventualFamily
        (domainOrderAxiomString s r i) :=
    WeakerThan.pbl (provable_PA_meaning_domainOrder s r i)
  simp only [domainOrderAxiomString, formulaMeaning_impString,
    formulaMeaning_equalityString, formulaMeaning_rightInstanceString,
    FailureOfComposition.NumericalSpecialization.firstSuccessFamily,
    FailureOfComposition.NumericalSpecialization.eventualFamily] at hschema
  rw [provableAt_classOf] at hr ⊢
  exact Entailment.mdp (Entailment.mdp hschema hmixed) hr

/-- The order equality supplies equality of the chosen composite class and
the chosen representative of `rho`. -/
theorem classOf_comp_eq_of_domainOrder
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (rho S : CategoryTheory.DomSemilattice (omegaObject T))
    (horder : rho ≤ S) :
    classOf T
        (compIndex (normalizedOmegaIndex T S.hom)
          (normalizedOmegaIndex T rho.hom)) =
      classOf T (normalizedOmegaIndex T rho.hom) := by
  have hhom : rho.hom ≫ S.hom = rho.hom :=
    (CategoryTheory.DomSemilattice.le_def).mp horder
  have hval := congrArg Subtype.val hhom
  calc
    classOf T
          (compIndex (normalizedOmegaIndex T S.hom)
            (normalizedOmegaIndex T rho.hom)) =
        (rho.hom ≫ S.hom).val :=
      classOf_normalizedOmegaIndex_comp T rho.hom S.hom
    _ = rho.hom.val := hval
    _ = classOf T (normalizedOmegaIndex T rho.hom) :=
      (classOf_normalizedOmegaIndex T rho.hom).symm

/-- The actual categorical B7 consequence at the number object.  Recursive
enumerability is absent because this statement concerns derivability, not a
selected numerical proof presentation. -/
theorem provableAt_of_domainOrder
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (rho S : CategoryTheory.DomSemilattice (omegaObject T)) (i : ℕ)
    (horder : rho ≤ S)
    (hr : ProvableAt T rho.hom.val i i) :
    ProvableAt T S.hom.val i i := by
  let r := normalizedOmegaIndex T rho.hom
  let s := normalizedOmegaIndex T S.hom
  have hr' : ProvableAt T (classOf T r) i i := by
    rw [classOf_normalizedOmegaIndex]
    exact hr
  have hs' : ProvableAt T (classOf T s) i i :=
    provableAt_of_comp_class_eq T
      (classOf_comp_eq_of_domainOrder T rho S horder) hr'
  rw [classOf_normalizedOmegaIndex] at hs'
  exact hs'

/-! ## Numerical evidence at the selected representatives -/

/-- The abstract order equation yields the mixed equality theorem at exactly
the chosen composite and inner indices. -/
theorem mixedEquality_of_domainOrder
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (rho S : CategoryTheory.DomSemilattice (omegaObject T))
    (horder : rho ≤ S) :
    T ⊢ uniformSentence
      (firstSuccessGraph
        (compIndex (normalizedOmegaIndex T S.hom)
          (normalizedOmegaIndex T rho.hom)))
      (eventualGraph (normalizedOmegaIndex T rho.hom)) := by
  have hgr : EqIndex T
      (compIndex (normalizedOmegaIndex T S.hom)
        (normalizedOmegaIndex T rho.hom))
      (normalizedOmegaIndex T rho.hom) :=
    (classOf_eq_classOf_iff T _ _).mp
      (classOf_comp_eq_of_domainOrder T rho S horder)
  exact uniform_trans
    (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph _)) hgr

/-- A supplied equality proof and a supplied proof that the chosen inner
representative fixes `i` are transformed at the exact requested endpoints. -/
theorem reTheory_normalizedDomainOrderTransfer
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (rho S : CategoryTheory.DomSemilattice (omegaObject T)) (i : ℕ)
    {e p : ℕ}
    (he : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) e
      (equalityCode
        (compIndex (normalizedOmegaIndex T S.hom)
          (normalizedOmegaIndex T rho.hom))
        (normalizedOmegaIndex T rho.hom)))
    (hp : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
      (rightInstanceCode (normalizedOmegaIndex T rho.hom) i i)) :
    Proof_T (reTheoryDomainOrderTheoryPresentation T hRE)
      (domainOrderTransfer e p (normalizedOmegaIndex T S.hom)
        (normalizedOmegaIndex T rho.hom) i)
      (rightInstanceCode (normalizedOmegaIndex T S.hom) i i) :=
  reTheoryProof_T_domainOrderTransfer T hRE he hp

theorem exists_domainOrderEqualityProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (rho S : CategoryTheory.DomSemilattice (omegaObject T))
    (horder : rho ≤ S) :
    ∃ e : ℕ, Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) e
      (equalityCode
        (compIndex (normalizedOmegaIndex T S.hom)
          (normalizedOmegaIndex T rho.hom))
        (normalizedOmegaIndex T rho.hom)) :=
  (reTheory_provable_uniform_iff_exists_domainOrderProof_T T hRE _ _).mp
    (mixedEquality_of_domainOrder T rho S horder)

theorem exists_domainOrderRightProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (rho : CategoryTheory.DomSemilattice (omegaObject T)) (i : ℕ)
    (hr : ProvableAt T rho.hom.val i i) :
    ∃ p : ℕ, Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
      (rightInstanceCode (normalizedOmegaIndex T rho.hom) i i) := by
  apply (reTheory_provable_right_iff_exists_domainOrderProof_T
    T hRE (normalizedOmegaIndex T rho.hom) i i).mp
  rw [← provableAt_classOf]
  rw [classOf_normalizedOmegaIndex]
  exact hr

/-- Existence of numerical input evidence at the selected representatives
gives explicit output evidence whose code is the displayed primitive-recursive
transformation. -/
theorem exists_domainOrderTransferEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (rho S : CategoryTheory.DomSemilattice (omegaObject T)) (i : ℕ)
    (horder : rho ≤ S)
    (hr : ProvableAt T rho.hom.val i i) :
    ∃ e p : ℕ,
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) e
        (equalityCode
          (compIndex (normalizedOmegaIndex T S.hom)
            (normalizedOmegaIndex T rho.hom))
          (normalizedOmegaIndex T rho.hom)) ∧
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
        (rightInstanceCode (normalizedOmegaIndex T rho.hom) i i) ∧
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE)
        (domainOrderTransfer e p (normalizedOmegaIndex T S.hom)
          (normalizedOmegaIndex T rho.hom) i)
        (rightInstanceCode (normalizedOmegaIndex T S.hom) i i) := by
  obtain ⟨e, he⟩ := exists_domainOrderEqualityProof T hRE rho S horder
  obtain ⟨p, hp⟩ := exists_domainOrderRightProof T hRE rho i hr
  exact ⟨e, p, he, hp,
    reTheory_normalizedDomainOrderTransfer T hRE rho S i he hp⟩

/-! ## Identity-at-zero regression -/

/-- At the identity program and numeral zero, both premises have actual
numerical witnesses and `domainOrderTransfer` produces the requested right-tag
proof. -/
theorem reTheory_identityZero_domainOrderEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ e p : ℕ,
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) e
        (equalityCode
          (compIndex Kleene.identityIndex Kleene.identityIndex)
          Kleene.identityIndex) ∧
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
        (rightInstanceCode Kleene.identityIndex 0 0) ∧
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE)
        (domainOrderTransfer e p Kleene.identityIndex
          Kleene.identityIndex 0)
        (rightInstanceCode Kleene.identityIndex 0 0) := by
  have hclass :
      classOf T (compIndex Kleene.identityIndex Kleene.identityIndex) =
        classOf T Kleene.identityIndex := by
    calc
      classOf T (compIndex Kleene.identityIndex Kleene.identityIndex) =
          classOf T Kleene.identityIndex *
            classOf T Kleene.identityIndex := (mul_classOf T _ _).symm
      _ = (1 : ProgramQuotient T) * 1 := by
        rw [one_eq_classOf]
      _ = 1 := one_mul 1
      _ = classOf T Kleene.identityIndex := one_eq_classOf T
  have hgr : EqIndex T
      (compIndex Kleene.identityIndex Kleene.identityIndex)
      Kleene.identityIndex :=
    (classOf_eq_classOf_iff T _ _).mp hclass
  have hmixed : T ⊢ uniformSentence
      (firstSuccessGraph
        (compIndex Kleene.identityIndex Kleene.identityIndex))
      (eventualGraph Kleene.identityIndex) :=
    uniform_trans
      (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph _)) hgr
  obtain ⟨e, he⟩ :=
    (reTheory_provable_uniform_iff_exists_domainOrderProof_T
      T hRE _ _).mp hmixed
  have hright : T ⊢
      (eventualGraph Kleene.identityIndex).val/[(0 : ℕ), (0 : ℕ)] := by
    rw [← provableAt_classOf]
    simpa only [← one_eq_classOf T] using provableAt_one T 0
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_right_iff_exists_domainOrderProof_T
      T hRE Kleene.identityIndex 0 0).mp hright
  exact ⟨e, p, he, hp,
    reTheoryProof_T_domainOrderTransfer T hRE he hp⟩

end

end FailureOfComposition.NumericalDomainOrder
