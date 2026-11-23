/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedTheoryObservationsProofs
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompleteness
public import CategoricalEssentialIncompleteness.ArithmeticObservationFunctor

/-! # The functor on signed numeral instances

Section 8.6 sends a consistent c.e. theory to the indices at which it
proves the fixed numeral instance or its negation. Theory inclusions act
on both supports by the identity of the numerical object.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedTheoryObservations
open NamedArithmeticSignature NumericalArithmetic.Incompleteness

theorem positive_enumerable (T : Theory) : REPred (· ∈ positive T) :=
  (theory_enumerable T).comp ArithmeticSentenceInseparability.theta_computable

theorem negative_enumerable (T : Theory) : REPred (· ∈ negative T) :=
  (theory_enumerable T).comp negativeWord_computable

theorem observations_disjoint (T : Theory) : Disjoint (positive T) (negative T) := by
  apply Set.disjoint_left.mpr
  intro n hp hn
  change positiveWord n ∈ T.val at hp
  change negativeWord n ∈ T.val at hn
  rw [positiveWord_eq] at hp
  rw [negativeWord_eq] at hn
  exact T.property.2 (numeralInstance n) (numeralInstance_closed n) ⟨hp, hn⟩

/-- A point of the numerical sentence-proof object with the specified conclusion word. -/
def NumericalProofPoint (Γ : Carrier) (w : ℕ) : Prop :=
  ∃ p : NumericalTuples.Point (NumericalArithmetic.SentenceProofCodes.object Γ),
    ((NumericalArithmetic.ProofComparison.conclusion Γ).toFun p).val = w

theorem theoremSet_iff_numericalProofPoint (Γ : Carrier) (φ : Formula) (hφ : φ.freeVariables = []) :
    formulaCode φ ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔ NumericalProofPoint Γ (formulaCode φ) := by
  let s : NumericalTuples.Point NumericalArithmetic.ProofImage.sentenceObject :=
    ⟨formulaCode φ, (ArithmeticIndexedPAEnumeration.sentence_formulaCode φ).mpr hφ⟩
  have hc := (NumericalArithmetic.ProofComparison.fixed_provability Γ s).symm
  refine (theoremSet_iff_eval Γ (formulaCode φ)).trans (hc.trans ?_)
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

theorem signed_numerical_proofPoints (T : Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) (n : ℕ) :
    (n ∈ positive T ↔ NumericalProofPoint Γ (formulaCode (numeralInstance n))) ∧
      (n ∈ negative T ↔ NumericalProofPoint Γ (formulaCode (.neg (numeralInstance n)))) := by
  change (positiveWord n ∈ T.val ↔ _) ∧ (negativeWord n ∈ T.val ↔ _)
  rw [hΓ, positiveWord_eq, negativeWord_eq]
  exact ⟨theoremSet_iff_numericalProofPoint Γ _ (numeralInstance_closed n),
    theoremSet_iff_numericalProofPoint Γ _ (numeralInstance_closed n)⟩

/-- The domains of the two numerical inverse images in the restriction splitting. -/
theorem pullback_supports (T : Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) :
    ClassicalPrograms.splitSupport (Idem.pull theta (theoremIdem Γ)) = positive T ∧
    ClassicalPrograms.splitSupport (Idem.pull theta (Idem.pull nu (theoremIdem Γ))) = negative T := by
  have ht : ClassicalPrograms.splitSupport (theoremIdem Γ) = T.val :=
    (theorem_support Γ).trans hΓ.symm
  have pull_theta (d : Idem S_rec) :
      ClassicalPrograms.splitSupport (Idem.pull theta d) = positiveWord ⁻¹' ClassicalPrograms.splitSupport d := by
    rw [ClassicalPrograms.splitSupport_pull]
    ext n
    change (∃ w : ℕ, w ∈ ClassicalPrograms.J.map theta.hom n ∧ w ∈ ClassicalPrograms.splitSupport d) ↔
      positiveWord n ∈ ClassicalPrograms.splitSupport d
    constructor
    · rintro ⟨w, hw, hd⟩
      have he : w = positiveWord n := (theta_graph n w).mp hw
      exact he ▸ hd
    · intro hd
      exact ⟨positiveWord n, (theta_graph n _).mpr rfl, hd⟩
  constructor
  · rw [pull_theta, ht]
    rfl
  · rw [pull_theta, ClassicalPrograms.splitSupport_pull, ht]
    ext n
    change (∃ w, w ∈ ClassicalPrograms.J.map nu.hom (positiveWord n) ∧ w ∈ T.val) ↔
      negativeWord n ∈ T.val
    constructor
    · rintro ⟨w, hw, ht⟩
      have he : w = negativeWord n := ((nu_graph _ _).mp hw).2
      exact he ▸ ht
    · intro hn
      exact ⟨negativeWord n, (nu_graph _ _).mpr ⟨theta_sentence_supported n, rfl⟩, hn⟩

theorem signed_bounds (T : Theory) :
    {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} ⊆ positive T ∧
      {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} ⊆ negative T := by
  obtain ⟨Γ, hPA, hΓ⟩ := T.property.1
  have bounds := NamedArithmeticDiagonalBounds.semantic_bounds ℕ Γ hPA
  constructor
  · intro n hn
    change positiveWord n ∈ T.val
    rw [hΓ]
    exact (theoremSet_iff_eval Γ (positiveWord n)).mpr (bounds.1 n hn)
  · intro n hn
    change negativeWord n ∈ T.val
    rw [hΓ]
    exact (theoremSet_iff_eval Γ (negativeWord n)).mpr (bounds.2 n hn)

def observedPair (T : Theory) : RecursivePairs.Object where
  carrier := ClassicalPrograms.U
  positive := ClassicalPrograms.supportIdem (positive T) (positive_enumerable T)
  negative := ClassicalPrograms.supportIdem (negative T) (negative_enumerable T)
  disjoint := RecursivePairs.supportIdems_disjoint _ _ _ _ (observations_disjoint T)

theorem observedPair_supports (T : Theory) :
    PartialFunctions.support (ClassicalPrograms.inclusionRangeFunctor.mapIdem
      (observedPair T).positive) = positive T ∧
    PartialFunctions.support (ClassicalPrograms.inclusionRangeFunctor.mapIdem
      (observedPair T).negative) = negative T := by
  simp only [observedPair, ClassicalPrograms.supportIdem_image, PartialFunctions.support_setIdem, and_self]

theorem observations_mono {T U : Theory} (h : T ≤ U) :
    positive T ⊆ positive U ∧ negative T ⊆ negative U :=
  ⟨Set.preimage_mono h, Set.preimage_mono h⟩

def observationFunctor : Theory ⥤ RecursivePairs.Object where
  obj := observedPair
  map {T U} f :=
    { map := 𝟙 ClassicalPrograms.U
      total := rst_id _
      positive := by
        change ClassicalPrograms.supportIdem (positive T) (positive_enumerable T) ≤
          Idem.pull (𝟙 ClassicalPrograms.U) (ClassicalPrograms.supportIdem (positive U) (positive_enumerable U))
        rw [Idem.pull_id]
        exact ClassicalPrograms.supportIdem_le _ _ (observations_mono (leOfHom f)).1
      negative := by
        change ClassicalPrograms.supportIdem (negative T) (negative_enumerable T) ≤
          Idem.pull (𝟙 ClassicalPrograms.U) (ClassicalPrograms.supportIdem (negative U) (negative_enumerable U))
        rw [Idem.pull_id]
        exact ClassicalPrograms.supportIdem_le _ _ (observations_mono (leOfHom f)).2 }
  map_id _ := RecursivePairs.Hom.ext rfl
  map_comp _ _ := RecursivePairs.Hom.ext (Category.id_comp (𝟙 ClassicalPrograms.U)).symm

theorem inclusion_map {T U : Theory} (f : T ⟶ U) :
    (observationFunctor.map f).map = 𝟙 ClassicalPrograms.U := rfl

def diagonalPair : RecursivePairs.Object :=
  ⟨ClassicalPrograms.U, aRec, bRec, diagonal_inseparable.disjoint⟩

/-- The even and odd diagonal domains map into the two signed supports by the identity. -/
def diagonalToObservation (T : Theory) : diagonalPair ⟶ observedPair T where
  map := 𝟙 ClassicalPrograms.U
  total := rst_id _
  positive := by
    change aRec ≤ Idem.pull (𝟙 ClassicalPrograms.U) (ClassicalPrograms.supportIdem (positive T) (positive_enumerable T))
    rw [Idem.pull_id, ArithmeticApplication.le_supportIdem_iff, aRec_standard,
      PartialFunctions.support_setIdem]
    exact (signed_bounds T).1
  negative := by
    change bRec ≤ Idem.pull (𝟙 ClassicalPrograms.U) (ClassicalPrograms.supportIdem (negative T) (negative_enumerable T))
    rw [Idem.pull_id, ArithmeticApplication.le_supportIdem_iff, bRec_standard,
      PartialFunctions.support_setIdem]
    exact (signed_bounds T).2

/-- A total recursive function preserving both signs pulls a recursive separator back to its source. -/
theorem separator_preimage {A B P N C : Set ℕ} (f : ℕ → ℕ) (hf : Computable f)
    (hp : ∀ n ∈ A, f n ∈ P) (hn : ∀ n ∈ B, f n ∈ N)
    (hC : ComputablePred (· ∈ C)) (hP : P ⊆ C) (hN : Disjoint C N) :
    ComputablePred (· ∈ f ⁻¹' C) ∧ A ⊆ f ⁻¹' C ∧ Disjoint (f ⁻¹' C) B :=
  ⟨ArithmeticSentenceInseparability.computable_preimage C hC f hf,
    fun _ ha => hP (hp _ ha),
    Set.disjoint_left.mpr (fun n hc hb => Set.disjoint_left.mp hN hc (hn n hb))⟩

theorem recursively_inseparable (T : Theory) : Numerical.RecursivelyInseparable (positive T) (negative T) := by
  refine ⟨observations_disjoint T, ?_⟩
  rintro ⟨C, hC, hP, hN⟩
  exact ArithmeticSentenceInseparability.diagonal_no_recursive_separator
    ⟨id ⁻¹' C, separator_preimage id Computable.id
      (fun _ hn => (signed_bounds T).1 hn) (fun _ hn => (signed_bounds T).2 hn) hC hP hN⟩

end CategoricalEssentialIncompleteness.V46.NamedTheoryObservations
