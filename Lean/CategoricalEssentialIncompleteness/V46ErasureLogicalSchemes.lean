/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryErasureSubstitution

/-! # The seven first-order schemes under propositional erasure -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ErasureLogicalSchemes
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V X Y : C}

def one (imp : Y ⨯ Y ⟶ Y) : Y ⨯ Y ⟶ Y :=
  prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ imp) ≫ imp

def two (imp : Y ⨯ Y ⟶ Y) : (Y ⨯ Y) ⨯ Y ⟶ Y :=
  prod.lift
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ imp) ≫ imp)
    (prod.lift (prod.fst ≫ imp)
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ imp) ≫ imp) ≫ imp

def three (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) : Y ⨯ Y ⟶ Y :=
  prod.lift (prod.lift (prod.snd ≫ neg) (prod.fst ≫ neg) ≫ imp) imp ≫ imp

variable (S : CategoricalSyntax V (fun _ => ⊥_ C) (fun _ => X) 0)
variable (d : X ⟶ Y) (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ C ⟶ Y)
local notation "r" => NullaryPropositionalErasure.erase S d neg imp truth

theorem hilbert_one : S.hilbertOne ≫ r = prod.map r r ≫ one imp := by
  simp [CategoricalSyntax.hilbertOne, one, Category.assoc,
    NullaryPropositionalErasure.implication, prod.comp_lift_assoc, prod.lift_map_assoc]

theorem hilbert_two : S.hilbertTwo ≫ r = prod.map (prod.map r r) r ≫ two imp := by
  simp [CategoricalSyntax.hilbertTwo, two, Category.assoc,
    NullaryPropositionalErasure.implication, prod.comp_lift_assoc, prod.lift_map_assoc]

theorem hilbert_three : S.hilbertThree ≫ r = prod.map r r ≫ three neg imp := by
  simp [CategoricalSyntax.hilbertThree, three, Category.assoc,
    NullaryPropositionalErasure.implication, NullaryPropositionalErasure.negation,
    prod.comp_lift_assoc, prod.lift_map_assoc]

@[reassoc] theorem instantiation_original :
    S.instantiationAdmissible ≫ S.admissibleInclusion ≫ prod.fst =
      S.instantiationInclusion ≫ prod.snd ≫ prod.fst := by
  have h := congrArg (fun k => k ≫ prod.fst) S.instantiation_admissible
  simpa [CategoricalSyntax.instantiationInput, Category.assoc] using h.symm

/-- The instantiation scheme erases to H ⇒ H on its success pullback. -/
theorem hilbert_instantiation : S.hilbertInstantiation ≫ r =
    prod.lift (S.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ r)
      (S.instantiationInclusion ≫ prod.snd ≫ prod.fst ≫ r) ≫ imp := by
  simp [CategoricalSyntax.hilbertInstantiation, Category.assoc,
    NullaryPropositionalErasure.implication, NullaryPropositionalErasure.quantifier,
    NullaryPropositionalErasure.substitution_value,
    prod.lift_map_assoc, instantiation_original_assoc]

/-- The distribution scheme erases to (H ⇒ K) ⇒ (H ⇒ K). -/
theorem hilbert_distribution : S.hilbertDistribution ≫ r =
    prod.lift (S.distributionInclusion ≫ prod.snd ≫ prod.map r r ≫ imp)
      (S.distributionInclusion ≫ prod.snd ≫ prod.map r r ≫ imp) ≫ imp := by
  have h : prod.lift (S.distributionInclusion ≫ prod.snd ≫ prod.fst ≫ r)
      (S.distributionInclusion ≫ prod.snd ≫ prod.snd ≫ r) =
        S.distributionInclusion ≫ prod.snd ≫ prod.map r r := by
    apply prod.hom_ext <;> simp [Category.assoc]
  simp [CategoricalSyntax.hilbertDistribution, Category.assoc,
    NullaryPropositionalErasure.implication, NullaryPropositionalErasure.quantifier,
    prod.comp_lift_assoc, prod.lift_map_assoc, h]

theorem hilbert_reflexivity : S.hilbertReflexivity ≫ r = terminal.from _ ≫ truth := by
  simp [CategoricalSyntax.hilbertReflexivity, Category.assoc,
    NullaryPropositionalErasure.equality]

@[reassoc] theorem equality_first_original :
    S.equalityFirstAdmissible ≫ S.admissibleInclusion ≫ prod.fst =
      S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd := by
  have h := congrArg (fun k => k ≫ prod.fst) S.equality_first_admissible
  simpa [CategoricalSyntax.equalityFirstInput, Category.assoc] using h.symm

@[reassoc] theorem equality_second_original :
    S.equalitySecondAdmissible ≫ S.admissibleInclusion ≫ prod.fst =
      S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd := by
  have h := congrArg (fun k => k ≫ prod.fst) S.equality_second_admissible
  simpa [CategoricalSyntax.equalitySecondInput, Category.assoc] using h.symm

/-- Both admissible substitutions erase to the same original H. -/
theorem hilbert_equality : S.hilbertEquality ≫ r =
    prod.lift (terminal.from _ ≫ truth)
      (prod.lift (S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ r)
        (S.equalitySchemeInclusion ≫ prod.fst ≫ prod.snd ≫ r) ≫ imp) ≫ imp := by
  simp [CategoricalSyntax.hilbertEquality, Category.assoc,
    NullaryPropositionalErasure.implication, NullaryPropositionalErasure.equality,
    NullaryPropositionalErasure.substitution_value, prod.lift_map_assoc,
    equality_first_original_assoc, equality_second_original_assoc]

end CategoricalEssentialIncompleteness.V46.ErasureLogicalSchemes
