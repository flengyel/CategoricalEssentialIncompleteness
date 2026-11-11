/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityDiagonal
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsPrinted
public import CategoricalEssentialIncompleteness.NumericalInseparability

/-! # The categorical recursive-separator argument for actual Gamma words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
open NamedArithmeticSignature
attribute [local irreducible] ArithmeticDiagonalCodes.diagonalIndex

/-- The carrier remains opaque while membership is packaged as a set. -/
theorem mem_literal_set (C : SyntacticPredicates.Carrier) (w : ℕ)
    (h : C.val.Evalb (M := ℕ) ![w]) :
    w ∈ {z : ℕ | C.val.Evalb (M := ℕ) ![z]} := h

/-- These are the actual selected conclusion-image programs on literal
sentence words, including the constructed negation inverse image. -/
def theoremSet (A : SyntacticPredicates.Carrier) : Set ℕ :=
  {word | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]}

def refutationSet (A : SyntacticPredicates.Carrier) : Set ℕ :=
  {word | (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]}

def theta : ℕ → ℕ := NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val

theorem theta_computable : Computable theta :=
  (NamedArithmeticUnarySubstitution.value_primrec ArithmeticDiagonalCodes.alpha.val).to_comp

theorem theta_eq_fixed (n : ℕ) :
    theta n = NamedArithmeticFixedSubstitution.value (M := ℕ) NamedArithmeticDiagonalBounds.namedAlpha n := by
  unfold theta NamedArithmeticUnarySubstitution.value NamedArithmeticDiagonalBounds.namedAlpha
  rfl

theorem theta_eq_fixed_function :
    theta = (NamedArithmeticFixedSubstitution.value (M := ℕ)
      NamedArithmeticDiagonalBounds.namedAlpha : ℕ → ℕ) := by
  funext n
  exact theta_eq_fixed n

/-- A generic literal-word chart is established before specializing the
opaque diagonal formula, preserving the selected conclusion program. -/
theorem positive_literal_eval (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (n : ℕ)
    (h : (NamedArithmeticProofSearch.positive A φ).val.Evalb (M := ℕ) ![n]) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ)
      ![NamedArithmeticFixedSubstitution.value (M := ℕ) φ n] :=
  (NamedArithmeticProofSearch.positive_eval ℕ A φ n).mp h

theorem negative_literal_eval (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (n : ℕ) (h : (NamedArithmeticProofSearch.negative A φ).val.Evalb (M := ℕ) ![n]) :
    (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ)
      ![NamedArithmeticFixedSubstitution.value (M := ℕ) φ n] :=
  (NamedArithmeticProofSearch.negative_literal_refutation ℕ A φ hφ n).mp h

theorem positive_member (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (n : ℕ)
    (h : (NamedArithmeticProofSearch.positive A φ).val.Evalb (M := ℕ) ![n]) :
    NamedArithmeticFixedSubstitution.value (M := ℕ) φ n ∈ theoremSet A :=
  mem_literal_set (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A) _ (positive_literal_eval A φ n h)

theorem negative_member (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (n : ℕ) (h : (NamedArithmeticProofSearch.negative A φ).val.Evalb (M := ℕ) ![n]) :
    NamedArithmeticFixedSubstitution.value (M := ℕ) φ n ∈ refutationSet A :=
  mem_literal_set (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A) _ (negative_literal_eval A φ hφ n h)

theorem computable_preimage (R : Set ℕ) (hR : ComputablePred (· ∈ R))
    (f : ℕ → ℕ) (hf : Computable f) : ComputablePred (fun n => f n ∈ R) := by
  obtain ⟨r,hr,he⟩ := ComputablePred.computable_iff.mp hR
  refine ComputablePred.computable_iff.mpr ⟨r ∘ f,hr.comp hf,?_⟩
  funext n
  exact congrFun he (f n)

/-- The full separator proof is formula-generic. This keeps the source
formula and its concrete numerical substitution value distinct until the
actual diagonal formula is supplied with its proved bounds. -/
theorem no_recursive_separator_of_bounds (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (hAlpha : ∀ n : ℕ, ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.positive A φ).val.Evalb (M := ℕ) ![n])
    (hBeta : ∀ n : ℕ, ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.negative A φ).val.Evalb (M := ℕ) ![n]) :
    ¬ ∃ R : Set ℕ, ComputablePred (· ∈ R) ∧ theoremSet A ⊆ R ∧
      Disjoint R (refutationSet A) := by
  rintro ⟨R,hR,hTheorems,hRefutations⟩
  let f : ℕ → ℕ := NamedArithmeticFixedSubstitution.value (M := ℕ) φ
  let C := f ⁻¹' R
  have hf : Computable f := (NamedArithmeticFixedSubstitution.value_primrec φ).to_comp
  have hC : ComputablePred (· ∈ C) := computable_preimage R hR f hf
  apply diagonal_no_recursive_separator
  refine ⟨C,hC,?_,?_⟩
  · intro n hn
    exact hTheorems (positive_member A φ n (hAlpha n hn))
  · apply Set.disjoint_left.mpr
    intro n hnC hnBeta
    exact Set.disjoint_left.mp hRefutations hnC (negative_member A φ hφ n (hBeta n hnBeta))

/-- The actual literal Gamma theorem and refutation sets have no
recursive separator. Both concrete bounds are proved from native Γ≥PA;
the actual Θ is identified by theta_eq_fixed. -/
theorem no_recursive_separator (A : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    ¬ ∃ R : Set ℕ, ComputablePred (· ∈ R) ∧ theoremSet A ⊆ R ∧
      Disjoint R (refutationSet A) :=
  no_recursive_separator_of_bounds A NamedArithmeticDiagonalBounds.namedAlpha
    NamedArithmeticDiagonalBounds.namedAlpha_freeVariables
    (NamedArithmeticDiagonalBounds.standard_positive_of_axioms_admissible A
      (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hPA))
    (NamedArithmeticDiagonalBounds.standard_negative_of_axioms_admissible A
      (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hPA))

end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
