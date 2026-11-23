/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedTheoryObservations

/-! # The two signed supports, proof points and theory inclusions of §8.6 -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.NamedTheoryObservations.Checks
open NamedArithmeticSignature NumericalArithmetic.Incompleteness

example (A : Set ℕ) (hA : REPred (· ∈ A)) :
    ∀ n : ℕ, (axiomPredicate A).val.Evalb ![n] ↔ n ∈ A := axiomPredicate_eval A hA

example (T : Set ℕ) (hT : REPred (· ∈ T))
    (hs : ∀ w ∈ T, ∃ φ : Formula, φ.freeVariables = [] ∧ formulaCode φ = w)
    (hPA : ∀ φ, ArithmeticNamedAxiomComparison.PAAxiom φ → formulaCode φ ∈ T)
    (hd : ∀ φ : Formula, φ.freeVariables = [] → FiniteDerivation (axiomPredicate T) φ → formulaCode φ ∈ T)
    (hc : ∀ φ : Formula, φ.freeVariables = [] → ¬ (formulaCode φ ∈ T ∧ formulaCode (.neg φ) ∈ T)) :
    ∃ U : NamedTheoryObservations.Theory, U.val = T :=
  ⟨ofEnumerableTheory T hT hs hPA hd hc, rfl⟩

example (T : NamedTheoryObservations.Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) (n : ℕ) :
    (n ∈ positive T ↔ SyntacticFiniteNamedDerivations.Derives 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ ℕ (SyntacticNamedHilbert.formulaPoint
        functionSymbols relationSymbols bound (NamedArithmeticDiagonalBounds.instanceFormula
          ArithmeticDiagonalCodes.alpha.val n))) ∧
    (n ∈ negative T ↔ SyntacticFiniteNamedDerivations.Derives 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ ℕ (SyntacticNamedHilbert.formulaPoint
        functionSymbols relationSymbols bound (.neg (NamedArithmeticDiagonalBounds.instanceFormula
          ArithmeticDiagonalCodes.alpha.val n)))) := signed_derivability T Γ hΓ n

example (Γ : Carrier) (φ : Formula) (hs : φ.freeVariables = []) :
    formulaCode φ ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔
    ∃ p : Obj 𝗣𝗔 ℕ (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ).a.left,
      ((F 𝗣𝗔 ℕ).map (SyntacticGeneratedAxioms.conclusion 𝗣𝗔 variableSymbols
        functionSymbols relationSymbols bound Γ) p).val = formulaCode φ :=
  theoremSet_iff_proofPoint Γ φ hs

example (T : NamedTheoryObservations.Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) (n : ℕ) :
    (n ∈ positive T ↔ ∃ p : NumericalTuples.Point (NumericalArithmetic.SentenceProofCodes.object Γ),
      ((NumericalArithmetic.ProofComparison.conclusion Γ).toFun p).val = formulaCode (numeralInstance n)) ∧
    (n ∈ negative T ↔ ∃ p : NumericalTuples.Point (NumericalArithmetic.SentenceProofCodes.object Γ),
      ((NumericalArithmetic.ProofComparison.conclusion Γ).toFun p).val = formulaCode (.neg (numeralInstance n))) :=
  signed_numerical_proofPoints T Γ hΓ n

example (T : NamedTheoryObservations.Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) :
    ClassicalPrograms.splitSupport (Idem.pull theta (theoremIdem Γ)) = positive T ∧
      ClassicalPrograms.splitSupport (Idem.pull theta (Idem.pull nu (theoremIdem Γ))) = negative T :=
  pullback_supports T Γ hΓ

example (T : NamedTheoryObservations.Theory) :
    REPred (· ∈ positive T) ∧ REPred (· ∈ negative T) ∧ Disjoint (positive T) (negative T) :=
  ⟨positive_enumerable T, negative_enumerable T, observations_disjoint T⟩

example {T U : NamedTheoryObservations.Theory} (f : T ⟶ U) :
    (observationFunctor.map f).map = 𝟙 ClassicalPrograms.U := inclusion_map f

example (T : NamedTheoryObservations.Theory) :
    observationFunctor.map (𝟙 T) = 𝟙 (observedPair T) := observationFunctor.map_id T

example {T U V : NamedTheoryObservations.Theory} (f : T ⟶ U) (g : U ⟶ V) :
    observationFunctor.map (f ≫ g) = observationFunctor.map f ≫ observationFunctor.map g :=
  observationFunctor.map_comp f g

example (T : NamedTheoryObservations.Theory) :
    diagonalPair.positive = aRec ∧ diagonalPair.negative = bRec ∧
      (diagonalToObservation T).map = 𝟙 ClassicalPrograms.U := ⟨rfl, rfl, rfl⟩

example (T : NamedTheoryObservations.Theory) :
    Numerical.RecursivelyInseparable (positive T) (negative T) := recursively_inseparable T

end CategoricalEssentialIncompleteness.V46.NamedTheoryObservations.Checks
