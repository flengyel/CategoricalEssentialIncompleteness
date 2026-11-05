import CategoricalEssentialIncompleteness.V46NamedPlainSemantics

universe w

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemanticsChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → Carrier) (d : ℕ) {K : Type w}
variable (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "G" => F 𝗣𝗔 ℕ
example (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertOne z) :=
  valid_hilbertOne σ π d functions relations z
example (z : Obj 𝗣𝗔 ℕ ((Y ⨯ Y) ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertTwo z) :=
  valid_hilbertTwo σ π d functions relations z
example (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertThree z) :=
  valid_hilbertThree σ π d functions relations z
example (t : Obj 𝗣𝗔 ℕ (S).algebra.a.1) :
    Valid σ π d functions relations ((G).map (S).hilbertReflexivity t) :=
  valid_hilbertReflexivity σ π d functions relations t
example (z : Obj 𝗣𝗔 ℕ (variableCarrier ⨯ Y))
    (h : Valid σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z)) :
    Valid σ π d functions relations ((G).map (S).quantifierConstructor z) :=
  valid_generalization σ π d functions relations z h
example (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y))
    (hφ : Valid σ π d functions relations ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z))
    (himp : Valid σ π d functions relations ((G).map (S).implicationConstructor z)) :
    Valid σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z) :=
  valid_modusPonens σ π d functions relations z hφ himp
example [Nonempty K] (φ : Obj 𝗣𝗔 ℕ Y)
    (hφ : Valid σ π d functions relations φ)
    (hnot : Valid σ π d functions relations ((G).map (S).negationConstructor φ)) : False :=
  valid_negation_disjoint σ π d functions relations φ hφ hnot
end CategoricalEssentialIncompleteness.V46.NamedPlainSemanticsChecks
