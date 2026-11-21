/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkErasedSchemeProofs

/-! # Independent checks of uniform finite derivations of the erased schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.UniformPropositionalStatementChecks
open PropositionalProofCombinators

section Generic
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {F Ax W : C} {axioms : Ax ⟶ F} {imp : F ⨯ F ⟶ F} {neg : F ⟶ F}
variable (A : Endofunctor.Algebra (ForkInference.rules axioms imp).inference)

example (f g : W ⟶ F) (p : Proof A f) (q : Proof A (prod.lift f g ≫ imp)) :
    (Proof.mp p q).hom ≫ A.a.hom = g := (Proof.mp p q).conclusion

example (H : Schemes A neg) (f : W ⟶ F) :
    (H.identity f).hom ≫ A.a.hom = prod.lift f f ≫ imp := (H.identity f).conclusion

/-- The identity proof is exactly the derivation with two MP applications. -/
example (H : Schemes A neg) (f : W ⟶ F) :
    H.identity f = Proof.mp (H.oneProof f f)
      (Proof.mp (H.oneProof f (implies imp f f)) (H.twoProof f (implies imp f f) f)) := rfl

example (H : Schemes A neg) (f g : W ⟶ F) (p : Proof A f) :
    (H.weaken p g).hom ≫ A.a.hom = prod.lift g f ≫ imp := (H.weaken p g).conclusion
end Generic

section Fork
open ForkDerivation.Diagram ForkFirstOrderErasure
variable (a b : Idem EffectiveFork.V)

example : (inferenceAlgebra a b).a.left = realization.obj (ForkDerivation.proofObject a b) :=
  inference_carrier a b
example : (inferenceAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) :=
  inference_conclusion a b

example : coefficientShapeConclusion a b 0 = ErasureLogicalSchemes.one implication :=
  ForkPropositionalProofs.coefficient_one a b
example : coefficientShapeConclusion a b 1 = ErasureLogicalSchemes.two implication :=
  ForkPropositionalProofs.coefficient_two a b
example : coefficientShapeConclusion a b 2 =
    ErasureLogicalSchemes.three negation implication :=
  ForkPropositionalProofs.coefficient_three a b

/-- W is an arbitrary diagram, with no constant-family restriction. -/
example {W : Object} (f : W ⟶ sentences) :
    (ForkPropositionalProofs.identity a b f).hom ≫
        realization.map (ForkDerivation.conclusion a b) = prod.lift f f ≫ implication :=
  (ForkPropositionalProofs.identity a b f).conclusion

example : (ForkPropositionalProofs.truth a b).hom ≫
    realization.map (ForkDerivation.conclusion a b) = truth :=
  (ForkPropositionalProofs.truth a b).conclusion

example : ∃ p : firstOrder.algebra.a.2 ⨯ firstOrder.algebra.a.2 ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.hilbertOne ≫ erase :=
  ⟨(ForkErasedSchemeProofs.one a b).hom, (ForkErasedSchemeProofs.one a b).conclusion⟩
example : ∃ p : (firstOrder.algebra.a.2 ⨯ firstOrder.algebra.a.2) ⨯ firstOrder.algebra.a.2 ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.hilbertTwo ≫ erase :=
  ⟨(ForkErasedSchemeProofs.two a b).hom, (ForkErasedSchemeProofs.two a b).conclusion⟩
example : ∃ p : firstOrder.algebra.a.2 ⨯ firstOrder.algebra.a.2 ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.hilbertThree ≫ erase :=
  ⟨(ForkErasedSchemeProofs.three a b).hom, (ForkErasedSchemeProofs.three a b).conclusion⟩
example : ∃ p : firstOrder.instantiationParameters ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) =
      firstOrder.hilbertInstantiation ≫ erase :=
  ⟨(ForkErasedSchemeProofs.instantiation a b).hom,
    (ForkErasedSchemeProofs.instantiation a b).conclusion⟩
example : ∃ p : firstOrder.distributionParameters ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) =
      firstOrder.hilbertDistribution ≫ erase :=
  ⟨(ForkErasedSchemeProofs.distribution a b).hom, (ForkErasedSchemeProofs.distribution a b).conclusion⟩
example : ∃ p : firstOrder.algebra.a.1 ⟶ realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.hilbertReflexivity ≫ erase :=
  ⟨(ForkErasedSchemeProofs.reflexivity a b).hom, (ForkErasedSchemeProofs.reflexivity a b).conclusion⟩
example : ∃ p : firstOrder.equalitySchemeParameters ⟶
      realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.hilbertEquality ≫ erase :=
  ⟨(ForkErasedSchemeProofs.equality a b).hom, (ForkErasedSchemeProofs.equality a b).conclusion⟩

/-- The full scope has no derivability, initiality or compatibility hypothesis. -/
example : ∃ p : firstOrder.logicalParameters ⟶ realization.obj (ForkDerivation.proofObject a b),
    p ≫ realization.map (ForkDerivation.conclusion a b) = firstOrder.logicalAxioms ≫ erase :=
  ForkErasedSchemeProofs.printed_statement a b

example {j k : WalkingSpan} (f : j ⟶ k) :
    firstOrder.logicalParameters.map f ≫ (ForkErasedSchemeProofs.logicalProof a b).hom.app k =
      (ForkErasedSchemeProofs.logicalProof a b).hom.app j ≫
        (realization.obj (ForkDerivation.proofObject a b)).map f :=
  ForkErasedSchemeProofs.naturality a b f

example : ∃ p : firstOrder.logicalParameters ⟶
      (imageSubobject (realization.map (ForkDerivation.conclusion a b)) : Object),
    p ≫ (imageSubobject (realization.map (ForkDerivation.conclusion a b))).arrow =
      firstOrder.logicalAxioms ≫ erase := ForkErasedSchemeProofs.image_factor a b
end Fork
end CategoricalEssentialIncompleteness.V46.UniformPropositionalStatementChecks

namespace CategoricalEssentialIncompleteness.V46
#print axioms PropositionalProofCombinators.Proof.precomp
#print axioms PropositionalProofCombinators.Proof.restate
#print axioms PropositionalProofCombinators.Proof.axiomInstance
#print axioms PropositionalProofCombinators.Proof.mp
#print axioms PropositionalProofCombinators.Schemes.oneProof
#print axioms PropositionalProofCombinators.Schemes.twoProof
#print axioms PropositionalProofCombinators.Schemes.identity
#print axioms PropositionalProofCombinators.Schemes.weaken
#print axioms PropositionalSchemeTransport.map_pair_imp
#print axioms PropositionalSchemeTransport.one
#print axioms PropositionalSchemeTransport.two
#print axioms PropositionalSchemeTransport.three
#print axioms ForkPropositionalProofs.coefficient_one
#print axioms ForkPropositionalProofs.coefficient_two
#print axioms ForkPropositionalProofs.coefficient_three
#print axioms ForkPropositionalProofs.axiomProof
#print axioms ForkPropositionalProofs.schemes
#print axioms ForkPropositionalProofs.identity
#print axioms ForkPropositionalProofs.weaken
#print axioms ForkPropositionalProofs.truth
#print axioms ForkErasedSchemeProofs.one
#print axioms ForkErasedSchemeProofs.two
#print axioms ForkErasedSchemeProofs.three
#print axioms ForkErasedSchemeProofs.instantiation
#print axioms ForkErasedSchemeProofs.distribution
#print axioms ForkErasedSchemeProofs.reflexivity
#print axioms ForkErasedSchemeProofs.equality
#print axioms ForkErasedSchemeProofs.logicalProof
#print axioms ForkErasedSchemeProofs.logicalProof_conclusion
#print axioms ForkErasedSchemeProofs.printed_statement
#print axioms ForkErasedSchemeProofs.naturality
#print axioms ForkErasedSchemeProofs.image_factor
end CategoricalEssentialIncompleteness.V46
