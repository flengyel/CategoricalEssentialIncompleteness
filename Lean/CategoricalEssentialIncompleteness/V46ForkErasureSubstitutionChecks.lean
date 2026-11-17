/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkErasureSubstitution
public import CategoricalEssentialIncompleteness.V46ForkPropositionalEmbedding

/-! # Independent substitution and logical-erasure statement checks

The checks cover the printed substitution invariant and all seven erased
scheme expressions. Their uniform propositional derivations and the
generated-theory comparisons remain separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ErasureSubstitutionStatementChecks

section General
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V X Y : C}
variable (S : CategoricalSyntax V (fun _ => ⊥_ C) (fun _ => X) 0)
variable (d : X ⟶ Y) (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ C ⟶ Y)
local notation "r" => NullaryPropositionalErasure.erase S d neg imp truth

/-- The target is arbitrary propositional operations, rather than a Boolean valuation. -/
example : S.formulaSubstitutionOption ≫ OptionSyntax.map r =
    OptionSyntax.mask (prod.fst ≫ r) S.formulaSubstitutionOption :=
  NullaryPropositionalErasure.substitution_option_value _ _ _ _ _

example : S.formulaSubstitution ≫ r = S.admissibleInclusion ≫ prod.fst ≫ r :=
  NullaryPropositionalErasure.substitution_value _ _ _ _ _

example {W : C} (a : W ⟶ S.algebra.a.2 ⨯ S.substitutionParameters)
    (b : W ⟶ S.algebra.a.2)
    (h : a ≫ S.formulaSubstitutionOption = b ≫ coprod.inr) :
    b ≫ r = a ≫ prod.fst ≫ r := by
  have e := congrArg (fun k => a ≫ k)
    (NullaryPropositionalErasure.substitution_option_value S d neg imp truth)
  rw [← Category.assoc, h, Category.assoc, OptionSyntax.map_ok,
    OptionSyntax.mask_precomp, h, OptionSyntax.mask_ok] at e
  apply (cancel_mono (coprod.inr : Y ⟶ OptionSyntax.obj Y)).mp
  simpa only [Category.assoc] using e

example {W : C} (a : W ⟶ S.algebra.a.2 ⨯ S.substitutionParameters)
    (h : a ≫ S.formulaSubstitutionOption = OptionSyntax.fail) :
    a ≫ S.formulaSubstitutionOption ≫ OptionSyntax.map r = OptionSyntax.fail := by
  rw [← Category.assoc, h, OptionSyntax.fail_map]

example : S.hilbertOne ≫ r = prod.map r r ≫ ErasureLogicalSchemes.one imp :=
  ErasureLogicalSchemes.hilbert_one _ _ _ _ _
example : S.hilbertTwo ≫ r = prod.map (prod.map r r) r ≫ ErasureLogicalSchemes.two imp :=
  ErasureLogicalSchemes.hilbert_two _ _ _ _ _
example : S.hilbertThree ≫ r = prod.map r r ≫ ErasureLogicalSchemes.three neg imp :=
  ErasureLogicalSchemes.hilbert_three _ _ _ _ _

example : S.hilbertInstantiation ≫ r =
    prod.lift (S.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ r)
      (S.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ r) ≫ imp :=
  ErasureLogicalSchemes.hilbert_instantiation _ _ _ _ _
example : S.hilbertDistribution ≫ r =
    prod.lift (S.distributionInclusion ≫ prod.snd ≫ prod.map r r ≫ imp)
      (S.distributionInclusion ≫ prod.snd ≫ prod.map r r ≫ imp) ≫ imp :=
  ErasureLogicalSchemes.hilbert_distribution _ _ _ _ _
example : S.hilbertReflexivity ≫ r = terminal.from _ ≫ truth :=
  ErasureLogicalSchemes.hilbert_reflexivity _ _ _ _ _
example : S.hilbertEquality ≫ r = prod.lift (terminal.from _ ≫ truth)
    (prod.lift (S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ r)
      (S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ r) ≫ imp) ≫ imp :=
  ErasureLogicalSchemes.hilbert_equality _ _ _ _ _
end General

section Fork
open ForkFirstOrderErasure ForkDerivation.Diagram

example : labels = realization.obj ForkDerivation.variableObject := rfl
example : firstOrder = ForkCategoricalSyntax.categoricalSyntax labels := rfl
example : firstOrder.formulaSubstitution ≫ erase =
    firstOrder.admissibleInclusion ≫ prod.fst ≫ erase := substitution
example : firstOrder.formulaSubstitutionOption ≫ OptionSyntax.map erase =
    OptionSyntax.mask (prod.fst ≫ erase) firstOrder.formulaSubstitutionOption :=
  substitution_option

/-- All fork transitions are allowed, including those identifying atom labels. -/
example {j k : WalkingSpan} (f : j ⟶ k) :
    firstOrder.admissibleSubstitution.map f ≫ (firstOrder.formulaSubstitution ≫ erase).app k =
      (firstOrder.formulaSubstitution ≫ erase).app j ≫ sentences.map f :=
  substitution_natural f

example : firstOrder.hilbertOne ≫ erase =
    prod.map erase erase ≫ ErasureLogicalSchemes.one implication := hilbert_one
example : firstOrder.hilbertTwo ≫ erase =
    prod.map (prod.map erase erase) erase ≫ ErasureLogicalSchemes.two implication := hilbert_two
example : firstOrder.hilbertThree ≫ erase =
    prod.map erase erase ≫ ErasureLogicalSchemes.three negation implication := hilbert_three
example : firstOrder.hilbertInstantiation ≫ erase =
    prod.lift (firstOrder.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ erase)
      (firstOrder.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ erase) ≫ implication :=
  hilbert_instantiation
example : firstOrder.hilbertDistribution ≫ erase =
    prod.lift (firstOrder.distributionInclusion ≫ prod.snd ≫ prod.map erase erase ≫ implication)
      (firstOrder.distributionInclusion ≫ prod.snd ≫ prod.map erase erase ≫ implication) ≫
        implication := hilbert_distribution
example : firstOrder.hilbertReflexivity ≫ erase = terminal.from _ ≫ truth := hilbert_reflexivity
example : firstOrder.hilbertEquality ≫ erase = prod.lift (terminal.from _ ≫ truth)
    (prod.lift (firstOrder.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ erase)
      (firstOrder.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ erase) ≫ implication) ≫
        implication := hilbert_equality

example : ForkPropositionalEmbedding.embedding ≫ firstOrder.sentenceInclusion ≫ erase =
    𝟙 sentences := ForkPropositionalEmbedding.retraction
end Fork
end CategoricalEssentialIncompleteness.V46.ErasureSubstitutionStatementChecks

namespace CategoricalEssentialIncompleteness.V46
#print axioms NullaryPropositionalErasure.equality_pair_good
#print axioms NullaryPropositionalErasure.relation_pair_good
#print axioms NullaryPropositionalErasure.negation_pair_good
#print axioms NullaryPropositionalErasure.implication_pair_good
#print axioms NullaryPropositionalErasure.quantifier_pair_good
#print axioms NullaryPropositionalErasure.equality_closed
#print axioms NullaryPropositionalErasure.relation_closed
#print axioms NullaryPropositionalErasure.negation_closed
#print axioms NullaryPropositionalErasure.implication_closed
#print axioms NullaryPropositionalErasure.quantifier_closed
#print axioms NullaryPropositionalErasure.invariant_precomp
#print axioms NullaryPropositionalErasure.constructor_closed
#print axioms NullaryPropositionalErasure.fold_invariant
#print axioms NullaryPropositionalErasure.substitution_option_value
#print axioms NullaryPropositionalErasure.substitution_value
#print axioms ErasureLogicalSchemes.hilbert_one
#print axioms ErasureLogicalSchemes.hilbert_two
#print axioms ErasureLogicalSchemes.hilbert_three
#print axioms ErasureLogicalSchemes.hilbert_instantiation
#print axioms ErasureLogicalSchemes.hilbert_distribution
#print axioms ErasureLogicalSchemes.hilbert_reflexivity
#print axioms ErasureLogicalSchemes.hilbert_equality
#print axioms ForkFirstOrderErasure.substitution_option
#print axioms ForkFirstOrderErasure.substitution
#print axioms ForkFirstOrderErasure.substitution_natural
#print axioms ForkFirstOrderErasure.hilbert_one
#print axioms ForkFirstOrderErasure.hilbert_two
#print axioms ForkFirstOrderErasure.hilbert_three
#print axioms ForkFirstOrderErasure.hilbert_instantiation
#print axioms ForkFirstOrderErasure.hilbert_distribution
#print axioms ForkFirstOrderErasure.hilbert_reflexivity
#print axioms ForkFirstOrderErasure.hilbert_equality
end CategoricalEssentialIncompleteness.V46
