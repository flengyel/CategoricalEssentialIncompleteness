/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainAdmissibleValues
import CategoricalEssentialIncompleteness.V46NamedNumericalSemantics
import CategoricalEssentialIncompleteness.V46ModelSubstitutionSoundness

/-! # Semantic substitution on the constructed admissibility pullback -/

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

/-- Term evaluation respects the actual categorical substitution morphism
on every standard accepted term and every named parameter. -/
theorem evaluate_termSubstitution (q : Obj 𝗣𝗔 ℕ (X ⨯ P)) (ρ : ℕ → K) :
    evaluate σ π d functions ((G).map (S).termSubstitution q) ρ =
      evaluate σ π d functions ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)
        (Function.update ρ
          ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)).val
          (evaluate σ π d functions ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q)) ρ)) := by
  exact numerical_evaluate_substitute σ π d functions
    ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X)) ((G).map prod.snd q)).val
    ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X)) ((G).map prod.snd q))
    ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := P)) q) ((G).map (S).termSubstitution q) ρ
    (plain_termSubstitution_value 𝗣𝗔 variableCarrier σ π d ℕ q).symm

/-- The actual categorical substitution satisfies semantic substitution.
Its input is a point of the constructed success pullback, not an extra
free-for or successful-output assumption. The structure K is independent
of the arithmetic code model ℕ. -/
theorem holds_formulaSubstitution (a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).formulaSubstitution a) ρ ↔
      Holds σ π d functions relations
        ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))
        (Function.update ρ
          ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))).val
          (evaluate σ π d functions ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X))
            ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) ((G).map (S).admissibleInclusion a))) ρ)) := by
  let q := (G).map (S).admissibleInclusion a
  exact numerical_holds_substitute σ π d functions relations
    ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X)) ((G).map prod.snd q)).val
    ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := (variableCarrier : PredicateCategory 𝗣𝗔)) («Y» := X)) ((G).map prod.snd q))
    ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := P)) q) ((G).map (S).formulaSubstitution a) ρ
    (plain_formulaSubstitution_result 𝗣𝗔 variableCarrier σ π d ℕ a)

/-- The instantiation scheme uses the actual admissibility restriction
and the semantic substitution theorem just proved. -/
theorem valid_hilbertInstantiation (z : Obj 𝗣𝗔 ℕ (S).instantiationParameters) :
    Valid σ π d functions relations ((G).map (S).hilbertInstantiation z) := by
  exact ModelSubstitutionSoundness.valid_instantiation (G) (S) (fun x => x.val)
    (evaluate σ π d functions) (Holds σ π d functions relations)
    (holds_formulaSubstitution σ π d functions relations)
    (holds_implication σ π d functions relations)
    (holds_quantifier σ π d functions relations) z

/-- Equality substitution uses the two separately admissible inputs,
matched by the actual scheme pullback. -/
theorem valid_hilbertEquality (z : Obj 𝗣𝗔 ℕ (S).equalitySchemeParameters) :
    Valid σ π d functions relations ((G).map (S).hilbertEquality z) := by
  exact ModelSubstitutionSoundness.valid_equality (G) (S) (fun x => x.val)
    (evaluate σ π d functions) (Holds σ π d functions relations)
    (holds_formulaSubstitution σ π d functions relations)
    (holds_implication σ π d functions relations)
    (holds_equality σ π d functions relations) z

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
