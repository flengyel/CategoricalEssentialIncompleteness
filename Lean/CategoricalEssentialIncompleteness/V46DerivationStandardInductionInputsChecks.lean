import CategoricalEssentialIncompleteness.V46DerivationStandardInductionInputs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.DerivationStandardInductionInputsChecks
open SyntacticSyntax SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (labels : ℕ → PredicateCategory T) (X : PredicateCategory T) (n : ℕ)
    (i : Fin (n + 1)) (p : Obj T M (labels i.val ⨯ finitePower X i.val)) (tuple : M)
    (ht : (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.power .term i.val)).val.Evalb
      ![tuple,((F T M).map (PolynomialComparison.powerIso X i.val).hom
        ((F T M).map (prod.snd : labels i.val ⨯ finitePower X i.val ⟶ _) p)).val]) :
    (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.constructors labels n)).val.Evalb
      ![ruleTag M n i
          (Arithmetic.pair ((F T M).map (prod.fst : labels i.val ⨯ finitePower X i.val ⟶ _) p).val tuple),
        ((F T M).map (PolynomialComparison.injection labels X n i) p).val] :=
  injection_representation T M labels X n i p tuple ht
end CategoricalEssentialIncompleteness.V46.DerivationStandardInductionInputsChecks
