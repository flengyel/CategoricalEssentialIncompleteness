import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.AcceptanceChecks

example (formula : Bool) (a b : RawPolynomial) :
    𝗣𝗔 ⊢ plainCarrierEquivalenceSentence formula a b := carrier_plain_pa formula a b

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (formula : Bool) (a b : RawPolynomial) :
    @CategoryTheory.Iso (PredicateCategory T) inferInstance
      (carrier formula a b) (plainCarrier formula a b) := plainCarrierIso T formula a b

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (formula : Bool) (a b : RawPolynomial) (u : M)
    (hu : (rawCarrier (plainCarrier false a b) (plainCarrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    (toPlainMorphism T formula a b).graph.val.Evalb
      ![constructor formula (if formula then b else a) u, constructor formula (if formula then b else a) u] :=
  toPlain_constructor_graph T formula a b u hu

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.AcceptanceChecks
