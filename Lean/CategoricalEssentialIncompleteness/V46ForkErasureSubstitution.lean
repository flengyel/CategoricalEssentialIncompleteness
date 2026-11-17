/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ErasureLogicalSchemes
public import CategoricalEssentialIncompleteness.V46ForkFirstOrderErasure

/-! # Substitution invariance and the seven erased fork schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkFirstOrderErasure
open ForkDerivation.Diagram

/-- Erasure retains the exact failure/success branch of substitution. -/
theorem substitution_option :
    firstOrder.formulaSubstitutionOption ≫ OptionSyntax.map erase =
      OptionSyntax.mask (prod.fst ≫ erase) firstOrder.formulaSubstitutionOption :=
  NullaryPropositionalErasure.substitution_option_value _ _ _ _ _

@[reassoc] theorem substitution : firstOrder.formulaSubstitution ≫ erase =
    firstOrder.admissibleInclusion ≫ prod.fst ≫ erase :=
  NullaryPropositionalErasure.substitution_value _ _ _ _ _

theorem substitution_natural {j k : WalkingSpan} (f : j ⟶ k) :
    firstOrder.admissibleSubstitution.map f ≫ (firstOrder.formulaSubstitution ≫ erase).app k =
      (firstOrder.formulaSubstitution ≫ erase).app j ≫ sentences.map f :=
  (firstOrder.formulaSubstitution ≫ erase).naturality f

theorem hilbert_one : firstOrder.hilbertOne ≫ erase =
    prod.map erase erase ≫ ErasureLogicalSchemes.one implication :=
  ErasureLogicalSchemes.hilbert_one _ _ _ _ _

theorem hilbert_two : firstOrder.hilbertTwo ≫ erase =
    prod.map (prod.map erase erase) erase ≫ ErasureLogicalSchemes.two implication :=
  ErasureLogicalSchemes.hilbert_two _ _ _ _ _

theorem hilbert_three : firstOrder.hilbertThree ≫ erase =
    prod.map erase erase ≫ ErasureLogicalSchemes.three negation implication :=
  ErasureLogicalSchemes.hilbert_three _ _ _ _ _

theorem hilbert_instantiation : firstOrder.hilbertInstantiation ≫ erase =
    prod.lift (firstOrder.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ erase)
      (firstOrder.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ erase) ≫ implication :=
  ErasureLogicalSchemes.hilbert_instantiation _ _ _ _ _

theorem hilbert_distribution : firstOrder.hilbertDistribution ≫ erase =
    prod.lift (firstOrder.distributionInclusion ≫ prod.snd ≫ prod.map erase erase ≫ implication)
      (firstOrder.distributionInclusion ≫ prod.snd ≫ prod.map erase erase ≫ implication) ≫
        implication := ErasureLogicalSchemes.hilbert_distribution _ _ _ _ _

theorem hilbert_reflexivity : firstOrder.hilbertReflexivity ≫ erase =
    terminal.from _ ≫ truth := ErasureLogicalSchemes.hilbert_reflexivity _ _ _ _ _

theorem hilbert_equality : firstOrder.hilbertEquality ≫ erase =
    prod.lift (terminal.from _ ≫ truth)
      (prod.lift (firstOrder.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ erase)
        (firstOrder.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ erase) ≫ implication) ≫
          implication := ErasureLogicalSchemes.hilbert_equality _ _ _ _ _

end CategoricalEssentialIncompleteness.V46.ForkFirstOrderErasure
