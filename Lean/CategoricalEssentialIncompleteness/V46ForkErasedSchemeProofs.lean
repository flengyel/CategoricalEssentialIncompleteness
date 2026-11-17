/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkPropositionalProofs
public import CategoricalEssentialIncompleteness.V46ForkErasureSubstitution

/-! # Uniform finite propositional derivations of all seven erased fork schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkErasedSchemeProofs
open ForkDerivation.Diagram ForkFirstOrderErasure PropositionalProofCombinators

def one (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertOne ≫ erase) :=
  ((ForkPropositionalProofs.schemes a b).one.precomp (prod.map erase erase)).restate
    hilbert_one.symm

def two (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertTwo ≫ erase) :=
  ((ForkPropositionalProofs.schemes a b).two.precomp
    (prod.map (prod.map erase erase) erase)).restate hilbert_two.symm

def three (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertThree ≫ erase) :=
  ((ForkPropositionalProofs.schemes a b).three.precomp (prod.map erase erase)).restate
    hilbert_three.symm

def instantiation (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertInstantiation ≫ erase) :=
  (ForkPropositionalProofs.identity a b
    (firstOrder.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ erase)).restate
      hilbert_instantiation.symm

def distribution (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertDistribution ≫ erase) :=
  (ForkPropositionalProofs.identity a b
    (firstOrder.distributionInclusion ≫ prod.snd ≫ prod.map erase erase ≫ implication)).restate
      hilbert_distribution.symm

def reflexivity (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertReflexivity ≫ erase) :=
  ((ForkPropositionalProofs.truth a b).precomp (terminal.from _)).restate hilbert_reflexivity.symm

def equality (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.hilbertEquality ≫ erase) :=
  (ForkPropositionalProofs.weaken a b
    (ForkPropositionalProofs.identity a b
      (firstOrder.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ erase))
    (terminal.from _ ≫ truth)).restate hilbert_equality.symm

/-- One natural morphism assigns a finite propositional derivation to
every instance in the actual seven-summand logical parameter object. -/
def logicalProof (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) (firstOrder.logicalAxioms ≫ erase) where
  hom := coprod.desc (coprod.desc (coprod.desc (coprod.desc
    (coprod.desc (coprod.desc (one a b).hom (two a b).hom) (three a b).hom)
      (instantiation a b).hom) (distribution a b).hom) (reflexivity a b).hom) (equality a b).hom
  conclusion := by
    simp only [coprod.desc_comp, (one a b).conclusion, (two a b).conclusion,
      (three a b).conclusion, (instantiation a b).conclusion, (distribution a b).conclusion,
      (reflexivity a b).conclusion, (equality a b).conclusion, CategoricalSyntax.logicalAxioms]

/-- The conclusion is the original scalar-code conclusion transported
by the established realization equivalence. -/
@[reassoc] theorem logicalProof_conclusion (a b : Idem EffectiveFork.V) :
    (logicalProof a b).hom ≫ realization.map (ForkDerivation.conclusion a b) =
      firstOrder.logicalAxioms ≫ erase := (logicalProof a b).conclusion

theorem printed_statement (a b : Idem EffectiveFork.V) :
    ∃ p : firstOrder.logicalParameters ⟶ realization.obj (ForkDerivation.proofObject a b),
      p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.logicalAxioms ≫ erase :=
  ⟨(logicalProof a b).hom, logicalProof_conclusion a b⟩

theorem naturality (a b : Idem EffectiveFork.V) {j k : WalkingSpan} (f : j ⟶ k) :
    firstOrder.logicalParameters.map f ≫ (logicalProof a b).hom.app k =
      (logicalProof a b).hom.app j ≫ (realization.obj (ForkDerivation.proofObject a b)).map f :=
  (logicalProof a b).hom.naturality f

/-- Every erased logical instance factors through the actual propositional theorem image. -/
theorem image_factor (a b : Idem EffectiveFork.V) :
    ∃ p : firstOrder.logicalParameters ⟶
        (imageSubobject (realization.map (ForkDerivation.conclusion a b)) : Object),
      p ≫ (imageSubobject (realization.map (ForkDerivation.conclusion a b))).arrow =
        firstOrder.logicalAxioms ≫ erase := by
  refine ⟨(logicalProof a b).hom ≫ factorThruImageSubobject _, ?_⟩
  rw [Category.assoc, imageSubobject_arrow_comp, logicalProof_conclusion]

end CategoricalEssentialIncompleteness.V46.ForkErasedSchemeProofs
