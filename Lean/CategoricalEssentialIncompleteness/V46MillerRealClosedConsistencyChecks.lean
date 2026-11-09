import CategoricalEssentialIncompleteness.V46MillerRealClosedConsistency

noncomputable section

namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedConsistency

example (a : Point) : TheoryDomainApplication.Consistent
    (RealClosedAxioms.RCFAxiomWords ∪ OrderedFieldSyntax.cutAxioms a) :=
  theoryAxioms_consistent a

example (a : Point) : ∀ φ : OrderedFieldSyntax.Formula, φ.freeVariables = [] →
    ¬(FiniteAxiomProof OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols
        OrderedFieldSyntax.bound (RealClosedAxioms.theoryAxioms a) φ ∧
      FiniteAxiomProof OrderedFieldSyntax.functionSymbols OrderedFieldSyntax.relationSymbols
        OrderedFieldSyntax.bound (RealClosedAxioms.theoryAxioms a) (.neg φ)) :=
  theoryAxioms_consistent a

example (a : Point) (φ : OrderedFieldSyntax.Formula) (hc : φ.freeVariables = [])
    (L K : List ℕ)
    (hL : ∀ word ∈ L, word ∈ RealClosedAxioms.theoryAxioms a)
    (hK : ∀ word ∈ K, word ∈ RealClosedAxioms.theoryAxioms a)
    (hp : SyntacticNamedHilbert.Derives OrderedFieldSyntax.functionSymbols
      OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound (finiteCarrier L) φ)
    (hn : SyntacticNamedHilbert.Derives OrderedFieldSyntax.functionSymbols
      OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound (finiteCarrier K) (.neg φ)) :
    False := by
  apply theoryAxioms_consistent a φ hc
  exact ⟨⟨L, hL, hp⟩, ⟨K, hK, hn⟩⟩

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedConsistency
