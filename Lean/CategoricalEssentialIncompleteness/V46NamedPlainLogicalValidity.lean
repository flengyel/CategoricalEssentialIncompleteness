/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSubstitutionSemantics
public import CategoricalEssentialIncompleteness.V46NamedPlainDistributionSemantics
public import CategoricalEssentialIncompleteness.V46NamedPlainSentenceTruth
public import CategoricalEssentialIncompleteness.V46FirstOrderLogicalInduction
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheory

/-! # Soundness of the constructed standard sentence derivations -/

@[expose] public section

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding
open SyntacticGeneratedTheory SyntacticDerivation.StandardInduction
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "G" => F 𝗣𝗔 ℕ
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

theorem valid_logicalAxioms (l : Obj 𝗣𝗔 ℕ (S).logicalParameters) :
    Valid σ π d functions relations ((G).map (S).logicalAxioms l) :=
  logicalAxioms_predicate 𝗣𝗔 ℕ (S) (Valid σ π d functions relations)
    (valid_hilbertOne σ π d functions relations)
    (valid_hilbertTwo σ π d functions relations)
    (valid_hilbertThree σ π d functions relations)
    (valid_hilbertInstantiation σ π d functions relations)
    (valid_hilbertDistribution σ π d functions relations)
    (valid_hilbertReflexivity σ π d functions relations)
    (valid_hilbertEquality σ π d functions relations) l

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
