/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedGammaModelSource
public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparison

/-! # A semantic model of the printed consistent named Gamma

The enumeration is the given literal named enumeration. PA extension means
derivability of its actual named arithmetic axioms. Completeness is used only
after both the finite proof comparison and each original formula roundtrip
have been proved.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.NamedGammaModel
open NamedArithmeticSignature SyntacticPredicates

variable (A : Carrier)
local notation "S" => ArithmeticNamedProofConnectives.system A

/-- The concrete given Gamma, extending actual named PA, has a consistent
source presentation by the proved individual PA and Gamma axiom comparisons. -/
theorem source_consistent_of_extendsPA
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent S) : Entailment.Consistent (sourceTheory A) :=
  source_consistent A (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hPA) hc

/-- Genuine first-order completeness supplies a semantic K satisfying
all literal Gamma sentences. K is distinct from the arithmetic code model;
no standard-model truth or arithmetic proof of consistency is assumed. -/
theorem exists_model_all_assignments
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent S) :
    ∃ (K : Type) (s : ORingStructure K), letI := s;
      ∀ ρ : ℕ → K, NamedGammaSoundness.Models functionSymbols relationSymbols bound A
        ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ := by
  rcases exists_source_model A (source_consistent_of_extendsPA A hPA hc) with ⟨K,s,hK⟩
  let := s
  have := hK
  exact ⟨K,s,fun ρ => source_model_models A ρ⟩

/-- The actual Gamma soundness interface receives a model constructed
from external consistency and the printed native PA extension. -/
theorem exists_model
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent S) :
    ∃ (K : Type) (s : ORingStructure K), letI := s;
      NamedGammaSoundness.Models functionSymbols relationSymbols bound A
        ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations
        (fun _ => (0 : K)) := by
  rcases exists_model_all_assignments A hPA hc with ⟨K,s,hK⟩
  let := s
  exact ⟨K,s,hK (fun _ => 0)⟩

end CategoricalEssentialIncompleteness.V46.NamedGammaModel
