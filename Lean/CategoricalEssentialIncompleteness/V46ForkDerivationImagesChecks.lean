/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationImages


/-! # Statement checks in `V46ForkDerivationImagesChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkDerivationImages.Checks

open EffectiveFork (V)
local notation "S" => ForkDerivation.sentenceObject

example (a b : Idem V) : (conclusion a b).hom = ForkSyntax.conclusion a b :=
  conclusion_hom a b

example (a b : Idem V) : theoremRange a b = ForkSyntax.t0 a b :=
  theoremRange_eq_t0 a b

example (a b : Idem V) :
    theoremSubobject a b = Subobject.mk (theoremInclusion a b) :=
  theoremSubobject_eq_domain a b

example (a b : Idem V) :
    ClosedUnder (ForkDerivation.rules a b).inference (image.ι (conclusion a b)) ∧
      ∀ {U : EffectiveFork.Total} (m : U ⟶ S) [Mono m],
        ClosedUnder (ForkDerivation.rules a b).inference m →
          ∃ w : image (conclusion a b) ⟶ U, w ≫ m = image.ι (conclusion a b) :=
  least_theorem_image a b

example (a b : Idem V) :
    IsLeast {P : Subobject S |
      ClosedUnder (ForkDerivation.rules a b).inference P.arrow}
      (theoremSubobject a b) :=
  theoremSubobject_isLeast a b

example (a b : Idem V) :
    ClosedUnder (ForkDerivation.rules a b).inference (theoremInclusion a b) ∧
      ∀ {U : EffectiveFork.Total} (m : U ⟶ S) [Mono m],
        ClosedUnder (ForkDerivation.rules a b).inference m →
          ∃ w : theoremObject a b ⟶ U, w ≫ m = theoremInclusion a b :=
  theoremInclusion_least a b

example (a b : Idem V) :
    (theoremRange a b).hom =
      EffectiveFork.domainRetraction (theoremRange a b) ≫ (theoremInclusion a b).hom :=
  range_regular_image a b

example (a b : Idem V) (hd : a ⊓ b = ⊥) :
    IsLeast {P : Subobject S |
      ClosedUnder (ForkDerivation.rules a b).inference P.arrow}
      (theoremSubobject a b) ∧
    IsLeast {e | ForkSyntax.IsTheory a b e} (theoremRange a b) ∧
      a ≤ Idem.pull ForkSyntax.theta (theoremRange a b) ∧
      b ≤ Idem.pull ForkSyntax.theta (Idem.pull ForkSyntax.nu (theoremRange a b)) ∧
      theoremRange a b ⊓ Idem.pull ForkSyntax.nu (theoremRange a b) = ⊥ :=
  proof_presentation a b hd

example : categoricalTheory = ForkSyntax.categoricalTheory := categoricalTheory_eq

example (i : Bool) (T : Set ℕ) (hT : REPred (· ∈ T))
    (hext : EnumerableCarriers.support (ForkSyntax.endpointTheory i categoricalTheory) ⊆ T)
    (hc : ∀ n : ℕ, n ∈ T → ForkSyntax.negCode n ∉ T) :
    ∃ n : ℕ, n ∉ T ∧ ForkSyntax.negCode n ∉ T :=
  endpoint_ce_extension_incomplete i T hT hext hc

example (i : Bool) (A : Set ℕ) (hA : REPred (· ∈ A))
    (hext : EnumerableCarriers.support (ForkSyntax.endpointTheory i categoricalTheory) ⊆
      ForkAxiomClosure.theoremCodes A)
    (hc : ∀ p : ForkSyntax.Formula,
      ¬(ForkAxiomClosure.Derives A p ∧ ForkAxiomClosure.Derives A (.neg p))) :
    ∃ p : ForkSyntax.Formula,
      ¬ForkAxiomClosure.Derives A p ∧ ¬ForkAxiomClosure.Derives A (.neg p) :=
  endpoint_axiom_extension_incomplete i A hA hext hc

namespace LiteralDiagram

local notation "D" => (WalkingSpan ⥤ NumericalTuples.Object)
local notation "LS" => ForkDerivation.Diagram.sentences
local notation "F" => ForkDerivation.Diagram.realization

example (a b : Idem V) :
    ForkDerivationImages.LiteralDiagram.conclusion a b =
      (F).map (ForkDerivation.conclusion a b) :=
  ForkDerivationImages.LiteralDiagram.conclusion_realization a b

example (a b : Idem V) :
    image (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom ≅
      (F).obj (EffectiveFork.imageObject (ForkDerivation.conclusion a b)) :=
  ForkDerivationImages.LiteralDiagram.imageIso a b

example (a b : Idem V) :
    (ForkDerivationImages.LiteralDiagram.imageIso a b).hom ≫
        (F).map (EffectiveFork.imageInclusion (ForkDerivation.conclusion a b)) =
      image.ι (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom :=
  ForkDerivationImages.LiteralDiagram.imageIso_hom_inclusion a b

example (a b : Idem V) :
    imageSubobject (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom =
      Subobject.mk ((F).map
        (EffectiveFork.imageInclusion (ForkDerivation.conclusion a b))) :=
  ForkDerivationImages.LiteralDiagram.theoremSubobject_eq_realizedImage a b

example (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.rules a b).inference
        (image.ι (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.rules a b).inference m →
          ∃ w : image (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom ⟶ U,
            w ≫ m = image.ι (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom :=
  ForkDerivationImages.LiteralDiagram.least_theorem_image a b

example (a b : Idem V) :
    IsLeast {P : Subobject LS |
      ClosedUnder (ForkDerivation.Diagram.rules a b).inference P.arrow}
      (imageSubobject (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom) :=
  ForkDerivationImages.LiteralDiagram.theoremSubobject_isLeast a b

example (a b : Idem V) :
    IsLeast {P : Subobject LS |
      ClosedUnder (ForkDerivation.Diagram.shapedH a b) P.arrow}
      (imageSubobject (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom) :=
  ForkDerivationImages.LiteralDiagram.shaped_theoremSubobject_isLeast a b

example (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.shapedH a b)
        ((F).map (EffectiveFork.imageInclusion (ForkDerivation.conclusion a b))) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.shapedH a b) m →
          ∃ w : (F).obj (EffectiveFork.imageObject (ForkDerivation.conclusion a b)) ⟶ U,
            w ≫ m = (F).map
              (EffectiveFork.imageInclusion (ForkDerivation.conclusion a b)) :=
  ForkDerivationImages.LiteralDiagram.shaped_theoremInclusion_least a b

example (a b : Idem V) :
    ForkDerivationImages.LiteralDiagram.theoremObject a b =
      (F).obj (⟨EffectiveFork.domainObject (ForkSyntax.t0 a b)⟩ : EffectiveFork.Total) :=
  ForkDerivationImages.LiteralDiagram.theoremObject_eq_t0_domain a b

end LiteralDiagram

end CategoricalEssentialIncompleteness.V46.ForkDerivationImages.Checks
