import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ParserChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (a b : RawPolynomial) (word n initial : M) :
    runPrefix a b word (n + 1) initial = step a b (nth word n) (runPrefix a b word n initial) :=
  prefix_succ a b word n initial

example (a b : RawPolynomial) (word suffix initial : M) :
    run a b (Words.append word suffix) initial = run a b suffix (run a b word initial) :=
  run_append a b word suffix initial

example (a b : RawPolynomial) (word record initial : M) :
    run a b (concat word record) initial = step a b record (run a b word initial) :=
  run_snoc a b word record initial

example (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] ∧
        run a b word 1 = adjoin ⟪word, if formula then 1 else 0⟫ 0 + 1 :=
  carrier_eval formula a b word

example (formula : Bool) (a b : RawPolynomial) :
    ¬(carrier formula a b).val.Evalb (M := M) ![0] := not_carrier_nil formula a b
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ParserChecks
