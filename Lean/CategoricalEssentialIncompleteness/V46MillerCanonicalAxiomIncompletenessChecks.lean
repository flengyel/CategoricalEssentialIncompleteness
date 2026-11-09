import CategoricalEssentialIncompleteness.V46MillerCanonicalAxiomIncompleteness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalAxiomIncompleteness.Checks
variable (a : Point) {A : Total.CanonicalTotal a}
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d

-- Every example binds its original mono explicitly. No chosen code set,
-- axiom-object comparison or initial-algebra hypothesis is an input.
example (m : A ⟶ (S₂).sentenceObject) :
    (E).functor.map (sourceAxioms a m)=
      ((E).counitIso.app A).hom≫m≫
        (CanonicalPresentation.mappedSentenceIso a (V) σ π d).inv :=
  sourceAxioms_map a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Mono (sourceAxioms a m) := inferInstance

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Uniform.Enumerable (P) (·∈recoveredCodes a m) := recoveredCodes_enumerable a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    recoveredCodes a m⊆AxiomSubobjects.imageCodes (NamedProofImage.sentenceWord (P) σ π d) :=
  recoveredCodes_sentence a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (E).functor.map (sourceAxioms a m)≫
      (CanonicalPresentation.mappedSentenceIso a (V) σ π d).hom=
        ((E).counitIso.app A).hom≫m := sourceAxioms_square a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Subobject.mk (sourceAxioms a m)=Subobject.mk (NamedProofImage.axioms (P) σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)) := source_subobject_recovery a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    A ≅ CanonicalPresentation.chosenAxiomObject a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m) := axiomIso a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (axiomIso a m).hom≫CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)=m := axiomIso_inclusion a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (axiomIso a m).inv≫m=CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m) := axiomIso_inverse_inclusion a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Subobject.mk m=Subobject.mk (CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)) := axiom_subobject_recovery a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    IsInitial (Derivation.Canonical.derivationAlgebra a ((S₂).logicalRules m)) := proofInitial a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    sentenceConclusion a m=pullback.snd
      (Derivation.Canonical.derivationAlgebra a ((S₂).logicalRules m)).a.hom
      (S₂).sentenceInclusion := rfl

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    theoremIdem a m=Ranges.range (sentenceConclusion a m).hom := rfl

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    imageSubobject (sentenceConclusion a m)=imageSubobject
      (CanonicalPresentation.chosenSentenceConclusion a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)) := sentence_image_recovery a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Ranges.range (sentenceConclusion a m).hom=
      Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)).hom := range_recovery a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Idem.pull (S₂).sentenceNegation.hom (Ranges.range (sentenceConclusion a m).hom)=
      CanonicalIncompleteness.refutationIdem a
        (recoveredCodes a m) (recoveredCodes_enumerable a m) := refutation_recovery a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    CanonicalIncompleteness.chartIdemIso a (Ranges.range (sentenceConclusion a m).hom)=
      Incompleteness.theoremIdem a (recoveredCodes a m) (recoveredCodes_enumerable a m) :=
  literal_range_conjugacy a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
      ¬(RealClosedBounds.Proof (recoveredCodes a m) φ ∧
        RealClosedBounds.Proof (recoveredCodes a m) (.neg φ))) ↔
      Ranges.range (sentenceConclusion a m).hom⊓Idem.pull (S₂).sentenceNegation.hom
        (Ranges.range (sentenceConclusion a m).hom)=⊥ := consistent_iff_disjoint a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : ∀ φ : OrderedFieldSyntax.Formula,
      NamedPostfixEncoding.formulaCode φ∈RealClosedAxioms.theoryAxioms a →
        RealClosedBounds.Proof (recoveredCodes a m) φ)
    (hc : Ranges.range (sentenceConclusion a m).hom⊓Idem.pull (S₂).sentenceNegation.hom
      (Ranges.range (sentenceConclusion a m).hom)=⊥) :
    Inseparable (Ranges.range (sentenceConclusion a m).hom)
      (Idem.pull (S₂).sentenceNegation.hom (Ranges.range (sentenceConclusion a m).hom)) ∧
      Ranges.range (sentenceConclusion a m).hom⊔Idem.pull (S₂).sentenceNegation.hom
        (Ranges.range (sentenceConclusion a m).hom)≠(⊤ : Idem (S₂).sentenceObject.obj) :=
  printed_essential_incompleteness a m ha hext hc

example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hc : Ranges.range (sentenceConclusion a m).hom⊓Idem.pull (S₂).sentenceNegation.hom
      (Ranges.range (sentenceConclusion a m).hom)=⊥) :
    Ranges.range (sentenceConclusion a m).hom⊔Idem.pull (S₂).sentenceNegation.hom
      (Ranges.range (sentenceConclusion a m).hom)≠(⊤ : Idem (S₂).sentenceObject.obj) :=
  printed_noncoverage a m ha hext hc

example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hc : Ranges.range (sentenceConclusion a m).hom⊓Idem.pull (S₂).sentenceNegation.hom
      (Ranges.range (sentenceConclusion a m).hom)=⊥) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) φ ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) (.neg φ) :=
  printed_native_incomplete a m ha hext hc

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    RealClosedBounds.Extends a (recoveredCodes a m) ↔
      CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m :=
  extends_iff_theoremIdem_le a m

example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m)
    (hcons : theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥) :
    Inseparable (theoremIdem a m) (refutationIdem a m) ∧
      theoremIdem a m⊔refutationIdem a m≠⊤ :=
  printed_categorical_incompleteness a m ha hext hcons

example (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (∀ φ : OrderedFieldSyntax.Formula,
      FiniteAxiomProof OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols
        OrderedFieldSyntax.bound (RealClosedAxioms.theoryAxioms a) φ →
      FiniteAxiomProof OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols
        OrderedFieldSyntax.bound (recoveredCodes a m) φ) ↔
      CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m :=
  finite_proof_transport_iff_theoremIdem_le a m

/- The final statement accepts finite derivability and native sentence
consistency; its categorical disjointness premise has been discharged. -/
example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : ∀ φ : OrderedFieldSyntax.Formula,
      OrderedFieldSyntax.formulaCode φ∈RealClosedAxioms.theoryAxioms a →
        ∃ L : List ℕ,(∀ c∈L,c∈recoveredCodes a m) ∧
          SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ)
    (hcons : ∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
      ¬((∃ L : List ℕ,(∀ c∈L,c∈recoveredCodes a m) ∧
          SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) ∧
        (∃ K : List ℕ,(∀ c∈K,c∈recoveredCodes a m) ∧
          SyntacticNamedHilbert.Derives σ π d (finiteCarrier K) (.neg φ)))) :
    Inseparable (theoremIdem a m) (refutationIdem a m) ∧
      theoremIdem a m⊔refutationIdem a m≠⊤ :=
  printed_essential_incompleteness_of_consistent a m ha hext hcons

example (m : A ⟶ (S₂).sentenceObject) [Mono m] (ha : IsMiller a)
    (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : ∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
      ¬(RealClosedBounds.Proof (recoveredCodes a m) φ ∧
        RealClosedBounds.Proof (recoveredCodes a m) (.neg φ))) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) φ ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) (.neg φ) :=
  printed_native_incomplete_of_consistent a m ha hext hcons

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalAxiomIncompleteness.Checks
