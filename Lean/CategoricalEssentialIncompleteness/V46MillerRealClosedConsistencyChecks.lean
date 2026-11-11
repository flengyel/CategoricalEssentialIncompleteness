/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedConsistency


/-! # Statement checks in `V46MillerRealClosedConsistencyChecks` -/

@[expose] public section
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
