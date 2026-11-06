import CategoricalEssentialIncompleteness.V46NamedPlainSubstitutionSemantics

noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSubstitutionSemanticsChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
example (q : Obj 𝗣𝗔 ℕ (X ⨯ P)) (ρ : ℕ → K) :
    evaluate σ π d functions ((G).map (S).termSubstitution q) ρ =
      evaluate σ π d functions ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)
        (Function.update ρ
          ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)).val
          (evaluate σ π d functions ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)) ρ)) :=
  evaluate_termSubstitution σ π d functions q ρ
example (a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).formulaSubstitution a) ρ ↔
      Holds σ π d functions relations
        ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))
        (Function.update ρ
          ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))).val
          (evaluate σ π d functions ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))) ρ)) :=
  holds_formulaSubstitution σ π d functions relations a ρ
example (z : Obj 𝗣𝗔 ℕ (S).instantiationParameters) :
    Valid σ π d functions relations ((G).map (S).hilbertInstantiation z) :=
  valid_hilbertInstantiation σ π d functions relations z
example (z : Obj 𝗣𝗔 ℕ (S).equalitySchemeParameters) :
    Valid σ π d functions relations ((G).map (S).hilbertEquality z) :=
  valid_hilbertEquality σ π d functions relations z
end CategoricalEssentialIncompleteness.V46.NamedPlainSubstitutionSemanticsChecks
