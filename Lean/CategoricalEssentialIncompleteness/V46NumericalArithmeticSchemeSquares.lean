/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticLogicalOperations
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticEqualityParameters
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionParameters

/-! # Actual arithmetic diagrams for the Hilbert axiom schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SchemeSquares
open Coordinates SubstitutionParameters SubstitutionDomains RuleParameters EqualityParameters NamedArithmeticSignature
local notation "K" => numericalInterpretation
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
abbrev formulaObject := numericalSyntax.algebra.a.2
abbrev originalFormulaObject := originalSyntax.algebra.a.2
local notation "Y" => formulaObject
local notation "Y₀" => originalFormulaObject

private theorem factor_right {A B C D : NumericalTuples.Object}
    {u : A ⟶ D} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (p : u = f ≫ g ≫ h) : u = (f ≫ g) ≫ h :=
  p.trans (Category.assoc f g h).symm

private theorem mapped_chain
    {A B C : PredicateCategory 𝗣𝗔} {U₁ U₂ U₃ : NumericalTuples.Object}
    {h : U₁ ⟶ (K).obj A} {p : U₁ ⟶ U₂} {j : U₂ ⟶ (K).obj B}
    {q : U₂ ⟶ U₃} {k : U₃ ⟶ (K).obj C} {f : A ⟶ B} {g : B ⟶ C}
    (hf : h ≫ (K).map f = p ≫ j) (hg : j ≫ (K).map g = q ≫ k) :
    h ≫ (K).map (f ≫ g) = (p ≫ q) ≫ k := by
  rw [(K).map_comp,← Category.assoc,hf,Category.assoc,hg,← Category.assoc]

/-- This calculation uses the constructed binary constructor square;
it introduces no additional operation-comparison hypothesis. -/
private theorem implication_lift {A : PredicateCategory 𝗣𝗔} {Z : NumericalTuples.Object}
    (h : Z ⟶ (K).obj A) (f g : A ⟶ Y₀) (f' g' : Z ⟶ Y)
    (hf : h ≫ (K).map f = f' ≫ formulaIso.hom)
    (hg : h ≫ (K).map g = g' ≫ formulaIso.hom) :
    h ≫ (K).map (prod.lift f g ≫ (S₀).implicationConstructor) =
      (prod.lift f' g' ≫ (S).implicationConstructor) ≫ formulaIso.hom := by
  rw [(K).map_comp,← Category.assoc,post_mapped_lift,hf,hg,
    ← pairedIso_lift formulaIso formulaIso f' g',Category.assoc,
    ← LogicalOperations.implication_square,← Category.assoc]

private theorem negation_lift {A : PredicateCategory 𝗣𝗔} {Z : NumericalTuples.Object}
    (h : Z ⟶ (K).obj A) (f : A ⟶ Y₀) (f' : Z ⟶ Y)
    (hf : h ≫ (K).map f = f' ≫ formulaIso.hom) :
    h ≫ (K).map (f ≫ (S₀).negationConstructor) =
      (f' ≫ (S).negationConstructor) ≫ formulaIso.hom := by
  rw [(K).map_comp,← Category.assoc,hf,Category.assoc,← LogicalOperations.negation_square,← Category.assoc]

private theorem quantifier_lift {A : PredicateCategory 𝗣𝗔} {Z : NumericalTuples.Object}
    (h : Z ⟶ (K).obj A) (f : A ⟶ variableSymbols) (g : A ⟶ Y₀)
    (f' : Z ⟶ NumericalNamed.variableObject) (g' : Z ⟶ Y)
    (hf : h ≫ (K).map f = f' ≫ variableIso.hom)
    (hg : h ≫ (K).map g = g' ≫ formulaIso.hom) :
    h ≫ (K).map (prod.lift f g ≫ (S₀).quantifierConstructor) =
      (prod.lift f' g' ≫ (S).quantifierConstructor) ≫ formulaIso.hom := by
  rw [(K).map_comp,← Category.assoc,post_mapped_lift,hf,hg,
    ← pairedIso_lift variableIso formulaIso f' g',Category.assoc,
    ← LogicalOperations.quantifier_square,← Category.assoc]

private theorem equality_lift {A : PredicateCategory 𝗣𝗔} {Z : NumericalTuples.Object}
    (h : Z ⟶ (K).obj A) (f g : A ⟶ (S₀).algebra.a.1)
    (f' g' : Z ⟶ (S).algebra.a.1)
    (hf : h ≫ (K).map f = f' ≫ termIso.hom)
    (hg : h ≫ (K).map g = g' ≫ termIso.hom) :
    h ≫ (K).map (prod.lift f g ≫ (S₀).equalityConstructor) =
      (prod.lift f' g' ≫ (S).equalityConstructor) ≫ formulaIso.hom := by
  rw [(K).map_comp,← Category.assoc,post_mapped_lift,hf,hg,
    ← pairedIso_lift termIso termIso f' g',Category.assoc,
    ← LogicalOperations.equality_square,← Category.assoc]

/-- The first propositional scheme retains both formula parameters. -/
theorem hilbertOne : formulaPairIso.hom ≫ (K).map (S₀).hilbertOne =
    (S).hilbertOne ≫ formulaIso.hom := by
  exact implication_lift formulaPairIso.hom _ _ _ _
    (pairedIso_fst formulaIso formulaIso)
    (implication_lift formulaPairIso.hom _ _ _ _
      (pairedIso_snd formulaIso formulaIso) (pairedIso_fst formulaIso formulaIso))

/-- All three formula parameters of the second propositional scheme
remain in their specified product coordinates. -/
theorem hilbertTwo : formulaTripleIso.hom ≫ (K).map (S₀).hilbertTwo =
    (S).hilbertTwo ≫ formulaIso.hom := by
  have hφ := factor_right (pairedIso_fst_fst formulaIso formulaIso formulaIso)
  have hψ := factor_right (pairedIso_fst_snd formulaIso formulaIso formulaIso)
  have hχ := pairedIso_snd formulaPairIso formulaIso
  have hφψ := mapped_chain (pairedIso_fst formulaPairIso formulaIso)
    LogicalOperations.implication_square.symm
  have hφχ := implication_lift formulaTripleIso.hom _ _ _ _ hφ hχ
  have hψχ := implication_lift formulaTripleIso.hom _ _ _ _ hψ hχ
  have hleft := implication_lift formulaTripleIso.hom _ _ _ _ hφ hψχ
  have hright := implication_lift formulaTripleIso.hom _ _ _ _ hφψ hφχ
  exact implication_lift formulaTripleIso.hom _ _ _ _ hleft hright

theorem hilbertThree : formulaPairIso.hom ≫ (K).map (S₀).hilbertThree =
    (S).hilbertThree ≫ formulaIso.hom := by
  have hφ := pairedIso_fst formulaIso formulaIso
  have hψ := pairedIso_snd formulaIso formulaIso
  have hNotPhi := negation_lift formulaPairIso.hom _ _ hφ
  have hNotPsi := negation_lift formulaPairIso.hom _ _ hψ
  exact implication_lift formulaPairIso.hom _ _ _ _
    (implication_lift formulaPairIso.hom _ _ _ _ hNotPsi hNotPhi)
    LogicalOperations.implication_square.symm

/-- The quantifier scheme uses the actual successful-substitution map
on its prescribed pullback domain. -/
theorem hilbertInstantiation : instantiationIso.hom ≫ (K).map (S₀).hilbertInstantiation =
    (S).hilbertInstantiation ≫ formulaIso.hom := by
  have hx := mapped_chain instantiation_inclusion instantiation_name
  have hφ := mapped_chain instantiation_inclusion (factor_right instantiation_formula)
  have hall := quantifier_lift instantiationIso.hom _ _ _ _ hx hφ
  have hsub := mapped_chain instantiation_admissible admissible_result
  exact implication_lift instantiationIso.hom _ _ _ _ hall hsub

/-- Distribution uses the genuine absent-variable fiber; its two formula
entries and named binder are the same parameters under the product chart. -/
theorem hilbertDistribution : DistributionParameters.iso.hom ≫ (K).map (S₀).hilbertDistribution =
    (S).hilbertDistribution ≫ formulaIso.hom := by
  have hx := DistributionParameters.name_coordinate
  have hφ := factor_right DistributionParameters.first_coordinate
  have hψ := factor_right DistributionParameters.second_coordinate
  have himp := mapped_chain (pairedIso_snd variableIso formulaPairIso)
    LogicalOperations.implication_square.symm
  have hleft := quantifier_lift distributionBaseIso.hom _ _ _ _ hx himp
  have hallψ := quantifier_lift distributionBaseIso.hom _ _ _ _ hx hψ
  have hright := implication_lift distributionBaseIso.hom _ _ _ _ hφ hallψ
  have hout := implication_lift distributionBaseIso.hom _ _ _ _ hleft hright
  exact mapped_chain DistributionParameters.inclusion hout

/-- The reflexivity parameter is the same original term word. -/
theorem hilbertReflexivity : termIso.hom ≫ (K).map (S₀).hilbertReflexivity =
    (S).hilbertReflexivity ≫ formulaIso.hom := by
  exact equality_lift termIso.hom (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- Both successful substitutions in the equality scheme are taken on
its actual intersection of success pullbacks. -/
theorem hilbertEquality : equalityIso.hom ≫ (K).map (S₀).hilbertEquality =
    (S).hilbertEquality ≫ formulaIso.hom := by
  have heq := mapped_chain equality_inclusion
    (mapped_chain (pairedIso_snd (pairedIso variableIso formulaIso) (pairedIso termIso termIso))
      LogicalOperations.equality_square.symm)
  have hs₁ := mapped_chain equality_first_admissible admissible_result
  have hs₂ := mapped_chain equality_second_admissible admissible_result
  exact implication_lift equalityIso.hom _ _ _ _ heq
    (implication_lift equalityIso.hom _ _ _ _ hs₁ hs₂)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SchemeSquares
