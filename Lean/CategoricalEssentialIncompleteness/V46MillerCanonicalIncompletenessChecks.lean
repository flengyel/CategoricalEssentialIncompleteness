/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalIncompleteness


/-! # Statement checks in `V46MillerCanonicalIncompletenessChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalIncompleteness.Checks

variable (a : Point)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d

-- The object and arrow coordinate statements concern the actual E.
example : ((E).functor.obj (S₁).sentenceObject).obj=
    CarrierIdempotents.SplitCarrier (S₁).sentenceObject.obj := mapped_sentence_object a

example {X Y : Total.TotalCategory (P)} (f : X ⟶ Y) :
    ((E).functor.map f).hom.hom.val=Total.val f.hom := mapped_arrow_value a f

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    theoremIdem a Γ hΓ=Ranges.range
      (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom := rfl

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    IsInitial (CanonicalPresentation.chosenProofAlgebra a σ π d Γ hΓ) :=
  CanonicalPresentation.chosenProofInitial a σ π d Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    imageSubobject (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)=
      Subobject.mk ((E).functor.map (image.ι
        (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ))≫
          (CanonicalPresentation.mappedSentenceIso a (V) σ π d).hom) :=
  CanonicalPresentation.chosen_canonical_sentenceTheory_eq a σ π d Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    ∃ r : (S₂).sentenceObject.obj ⟶
        (image (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).obj,
      (image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom≫r=𝟙 _ ∧
      r≫(image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom=rst r ∧
      (Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom).hom=
        r≫(image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom :=
  theorem_regular_image a Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    Ranges.range ((E).functor.map
      (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)).hom=
        Total.toSplitIdem (NamedProofImage.sentenceIdem (P) σ π d Γ hΓ) :=
  mapped_source_range a Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    Idem.pull (sourceSentenceIso a).hom
      (Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom)=
      TheoryDomainApplication.theoremIdem a Γ hΓ := source_theorem_conjugacy a Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (Incompleteness.theoremIdem a Γ hΓ).hom=(sentenceChart a).inv≫
      (Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom).hom≫
        (sentenceChart a).hom := theorem_conjugacy_hom a Γ hΓ

example : nu a=(S₂).sentenceNegation.hom := rfl

example : (S₂).sentenceNegation.hom≫(sentenceChart a).hom=
    (sentenceChart a).hom≫Incompleteness.nu a := negation_square a

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (Incompleteness.refutationIdem a Γ hΓ).hom=(sentenceChart a).inv≫
      (Idem.pull (S₂).sentenceNegation.hom
        (Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom)).hom≫
          (sentenceChart a).hom := refutation_conjugacy_hom a Γ hΓ

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
      ¬(RealClosedBounds.Proof Γ φ ∧ RealClosedBounds.Proof Γ (.neg φ))) ↔
      theoremIdem a Γ hΓ⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)=⊥ :=
  consistent_iff_canonical_disjoint a Γ hΓ

example (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hc : theoremIdem a Γ hΓ⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ)
      (Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ⊔Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)≠⊤ :=
  printed_essential_incompleteness a ha Γ hΓ hext hc

example (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hc : theoremIdem a Γ hΓ⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)=⊥) :
    theoremIdem a Γ hΓ⊔Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ)≠
      (⊤ : Idem (S₂).sentenceObject.obj) := printed_noncoverage a ha Γ hΓ hext hc

example (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hc : Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom⊓
      Idem.pull (S₂).sentenceNegation.hom
        (Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom)=⊥) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof Γ φ ∧ ¬RealClosedBounds.Proof Γ (.neg φ) :=
  printed_native_incomplete a ha Γ hΓ hext hc

example (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    RealClosedBounds.Extends a Γ ↔
      theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a Γ hΓ :=
  extends_iff_theoremIdem_le a Γ hΓ

example (ha : IsMiller a) (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a Γ hΓ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (refutationIdem a Γ hΓ) ∧
      theoremIdem a Γ hΓ⊔refutationIdem a Γ hΓ≠⊤ :=
  printed_categorical_incompleteness a ha Γ hΓ hext hcons

example (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hc : theoremIdem a Γ hΓ⊓Idem.pull (S₂).sentenceNegation.hom
      (theoremIdem a Γ hΓ)=⊥)
    (c e : Idem (S₂).sentenceObject.obj) (hce : Complementary c e)
    (ht : theoremIdem a Γ hΓ ≤ c)
    (hr : Idem.pull (S₂).sentenceNegation.hom (theoremIdem a Γ hΓ) ≤ e) : False :=
  (printed_essential_incompleteness a ha Γ hΓ hext hc).1.no_separator
    ⟨c,e,hce,ht,hr⟩

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalIncompleteness.Checks
