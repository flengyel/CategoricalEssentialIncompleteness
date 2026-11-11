/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptionBranches


/-! # Statement checks in `V46ConcreteNamedComparisonOptionBranchesChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OptionBranchesChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example {C D : PredicateCategory T} (h : C ⨯ C ⟶ D) :
    prod.map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) (𝟙 (OptionSyntax.obj C)) ≫
      OptionSyntax.binary h = OptionSyntax.fail := binary_failure_left_map h
example {C D : PredicateCategory T} (h : C ⨯ C ⟶ D) (φ : M → M → M)
    (hf : ∀ z : Obj T M (C ⨯ C), ((F T M).map h z).val =
      φ ((F T M).map (prod.fst : C ⨯ C ⟶ C) z).val ((F T M).map (prod.snd : C ⨯ C ⟶ C) z).val)
    (q : Obj T M (OptionSyntax.obj C ⨯ OptionSyntax.obj C)) :
    optionCode T M D ((F T M).map (OptionSyntax.binary h) q) =
      if π₂ (optionCode T M C ((F T M).map prod.fst q)) = 1 ∧
          π₂ (optionCode T M C ((F T M).map prod.snd q)) = 1
      then Arithmetic.pair
        (φ (π₁ (optionCode T M C ((F T M).map prod.fst q)))
          (π₁ (optionCode T M C ((F T M).map prod.snd q)))) 1 else 0 :=
  optionCode_binary T M h φ hf q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OptionBranchesChecks
