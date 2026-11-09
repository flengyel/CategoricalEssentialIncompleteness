import CategoricalEssentialIncompleteness.V46MillerTheoryDomainApplication

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.TheoryDomainApplication.Checks

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    (∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
      ¬(RealClosedBounds.Proof Γ φ ∧ RealClosedBounds.Proof Γ (.neg φ))) ↔
      theoremIdem a Γ hΓ ⊓ Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊥ :=
  consistent_iff_disjoint a Γ hΓ

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) (hcons : Consistent Γ) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (negation a) (theoremIdem a Γ hΓ)≠⊤ :=
  categorical_incompleteness a ha Γ hΓ hext hcons

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) : baseIdem a ≤ theoremIdem a Γ hΓ :=
  theoremIdem_mono a Γ hΓ hext

example (a : Point) : isTotal (theta a) ∧ isTotal (negation a) :=
  ⟨theta_total a,negation_total a⟩

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    RealClosedBounds.Extends a Γ ↔ baseIdem a ≤ theoremIdem a Γ hΓ :=
  extends_iff_theoremIdem_le a Γ hΓ

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : baseIdem a ≤ theoremIdem a Γ hΓ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ⊔Idem.pull (negation a) (theoremIdem a Γ hΓ)≠⊤ :=
  categorical_incompleteness_of_theory_extension a ha Γ hΓ hext hcons



/- The idempotent is the actual chosen sentence-conclusion range. -/
example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    theoremIdem a Γ hΓ=Total.toSplitIdem
      (Ranges.range (NamedProofImage.sentenceConclusion (Uniform.Family.ofPoint a)
        OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound Γ hΓ).hom) :=
  rfl

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) (s : ℕ) :
    s∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      s∈Total.Subobjects.imageCodes
        (NamedProofImage.sentenceConclusion (Uniform.Family.ofPoint a)
          OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound Γ hΓ) :=
  support_range a Γ hΓ s

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (s : Total.underlying.obj
      (NamedProofImage.syntaxData (Uniform.Family.ofPoint a) OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).sentenceObject) :
    s.val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      RealClosedBounds.Proof Γ (decodedSentence a s) :=
  theorem_mem a Γ hΓ s

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    CutInseparability.SourceSplit.lowerIdem a ≤ Idem.pull (theta a) (theoremIdem a Γ hΓ) :=
  lower_bound a Γ hΓ hext

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    CutInseparability.SourceSplit.upperIdem a ≤
      Idem.pull (theta a) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) :=
  upper_bound a Γ hΓ hext

example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    NamedProofImage.sentenceTheory (Uniform.Family.ofPoint a)
        OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound
        (RealClosedAxioms.theoryAxioms a) (RealClosedAxioms.theoryAxioms_enumerable a) ≤
      NamedProofImage.sentenceTheory (Uniform.Family.ofPoint a)
        OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound Γ hΓ :=
  sentenceTheory_mono a Γ hΓ hext

/- Coverage is relative to the actual proper sentence carrier. -/
example (a : Point) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    theoremIdem a Γ hΓ⊔Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊤ ↔
      CarrierIdempotents.support (theoremIdem a Γ hΓ) ∪
        CarrierIdempotents.support (Idem.pull (negation a) (theoremIdem a Γ hΓ))=
          (NamedProofImage.syntaxData (Uniform.Family.ofPoint a) OrderedFieldSyntax.functionSymbols
            OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).sentenceObject.obj.support :=
  CarrierIdempotents.join_eq_top_iff _ _

end CategoricalEssentialIncompleteness.V46.Miller.TheoryDomainApplication.Checks
