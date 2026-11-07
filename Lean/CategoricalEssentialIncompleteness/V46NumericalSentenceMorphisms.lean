/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues
import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphs
import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalLiteralTotal

/-! # Numerical negation and the literal numeral-substitution morphism -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalSentenceMorphisms
open NamedArithmeticSignature

def omega : NumericalTuples.Object := ⟨1, Set.univ, REPred.const True⟩

def omegaPoint (n : ℕ) : NumericalTuples.Point omega := ⟨n, Set.mem_univ _⟩

/-- The variable object has dimension one and literally the natural-number carrier. -/
def omegaIso : omega ≅ NumericalCoordinates.predicateObject variableSymbols where
  hom :=
    { toFun := fun x => ⟨x.val, variables_eval (M := ℕ) x.val⟩
      represented := ⟨Part.some, Partrec.some, fun _ => rfl⟩ }
  inv :=
    { toFun := fun x => ⟨x.val, Set.mem_univ _⟩
      represented := ⟨Part.some, Partrec.some, fun _ => rfl⟩ }
  hom_inv_id := NumericalTuples.Map.ext rfl
  inv_hom_id := NumericalTuples.Map.ext rfl

def sentence : NumericalTuples.Object :=
  NumericalCoordinates.predicateObject NamedArithmeticLiteralTotal.literalPredicate

def negation : sentence ⟶ sentence :=
  NumericalCoordinates.predicateMap (representedArrow 𝗧𝗔
    (NumericalArithmetic.liftGraph (chosenGraph 𝗣𝗔 ArithmeticLiteralModel.negation)))

theorem negation_value (s : NumericalTuples.Point sentence) :
    (negation.toFun s).val = NamedArithmeticProofSearch.negationWord ℕ s.val := by
  rw [negation, NumericalCoordinates.predicateMap_value, NumericalArithmetic.liftGraph_map,
    chosenGraph_class]
  exact ArithmeticLiteralModel.negation_value ℕ s

def theta (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) : omega ⟶ sentence :=
  omegaIso.hom ≫ NumericalCoordinates.predicateMap (representedArrow 𝗧𝗔
    (NumericalArithmetic.liftGraph (NamedArithmeticLiteralTotal.literalMorphism φ hφ)))

theorem theta_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ((theta φ hφ).toFun (omegaPoint n)).val = NamedArithmeticFixedSubstitution.value φ n := by
  rw [theta, NumericalTuples.composition_apply, NumericalCoordinates.predicateMap_value,
    NumericalArithmetic.liftGraph_map]
  exact (NamedArithmeticFixedSubstitution.morphism_graph_eval φ hφ n _).mp
    ((PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ
      (NamedArithmeticLiteralTotal.literalMorphism φ hφ) (omegaIso.hom.toFun (omegaPoint n)) _).mp rfl)

/-- The numeral is the manuscript's zero/add-one term, with its actual word. -/
theorem standard_literal_result (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      ((theta φ hφ).toFun (omegaPoint n)).val = formulaCode out ∧ out.freeVariables = [] := by
  obtain ⟨out, hs, hw, hc⟩ := NamedArithmeticFixedSubstitution.standard_literal_result φ hφ n
  exact ⟨out, hs, (theta_value φ hφ n).trans hw, hc⟩

theorem theta_standard_interpretation (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ((theta φ hφ).toFun (omegaPoint n)).val =
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        (NamedArithmeticLiteralTotal.theta φ hφ)
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val :=
  (theta_value φ hφ n).trans (NamedArithmeticLiteralTotal.canonical_value_at φ hφ ℕ n).symm

end CategoricalEssentialIncompleteness.V46.NumericalSentenceMorphisms
