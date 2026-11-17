/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkErasureClosure
public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # Embedding propositional derivations and restriction of the signed theory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkConservativeRestriction
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure
open ForkPropositionalEmbedding (embedding formulaEmbedding)
local notation "S" => firstOrder
local notation "jF" => formulaEmbedding
variable (a b : Idem EffectiveFork.V)

private theorem embed_one : coefficientShapeConclusion a b 0 ≫ jF =
    prod.map jF jF ≫ (S).hilbertOne := by
  rw [ForkPropositionalProofs.coefficient_one]
  simp [ErasureLogicalSchemes.one, CategoricalSyntax.hilbertOne,
    Category.assoc, ForkPropositionalEmbedding.formula_implication,
    prod.comp_lift_assoc, prod.lift_map_assoc]

private theorem embed_two : coefficientShapeConclusion a b 1 ≫ jF =
    prod.map (prod.map jF jF) jF ≫ (S).hilbertTwo := by
  rw [ForkPropositionalProofs.coefficient_two]
  simp [ErasureLogicalSchemes.two, CategoricalSyntax.hilbertTwo,
    Category.assoc, ForkPropositionalEmbedding.formula_implication,
    prod.comp_lift_assoc, prod.lift_map_assoc]

private theorem embed_three : coefficientShapeConclusion a b 2 ≫ jF =
    prod.map jF jF ≫ (S).hilbertThree := by
  rw [ForkPropositionalProofs.coefficient_three]
  simp [ErasureLogicalSchemes.three, CategoricalSyntax.hilbertThree,
    Category.assoc, ForkPropositionalEmbedding.formula_implication,
    ForkPropositionalEmbedding.formula_negation, prod.comp_lift_assoc, prod.lift_map_assoc]

abbrev nullary := (S).logicalParameters ⨿ (axiomImage a b : Object)

/-- Common inclusion of the first three logical schemes. The successive
left injections pass instantiation, distribution, reflexivity, equality
and the nonlogical axiom summand in the prescribed coproduct. -/
def logicalTriple : (((formulas ⨯ formulas) ⨿ ((formulas ⨯ formulas) ⨯ formulas)) ⨿
    (formulas ⨯ formulas)) ⟶ nullary a b :=
  coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl

def nullaryConclusion := coprod.desc (S).logicalAxioms
  ((axiomImage a b).arrow ≫ (S).sentenceInclusion)

@[reassoc] theorem logicalTriple_conclusion : logicalTriple a b ≫ nullaryConclusion a b =
    coprod.desc (coprod.desc (S).hilbertOne (S).hilbertTwo) (S).hilbertThree := by
  dsimp only [logicalTriple, nullaryConclusion, CategoricalSyntax.logicalAxioms]
  simp only [Category.assoc]
  erw [coprod.inl_desc, coprod.inl_desc, coprod.inl_desc, coprod.inl_desc, coprod.inl_desc]

def label : ∀ i, coefficientShape a b i ⟶ nullary a b :=
  Fin.cases (prod.map jF jF ≫ coprod.inl ≫ coprod.inl ≫ logicalTriple a b)
    (Fin.cases (prod.map (prod.map jF jF) jF ≫ coprod.inr ≫ coprod.inl ≫ logicalTriple a b)
      (Fin.cases (prod.map jF jF ≫ coprod.inr ≫ logicalTriple a b)
        (Fin.cases (coprod.inl ≫ factorThruImageSubobject (signedAxioms a b) ≫ coprod.inr)
          (Fin.cases (coprod.inr ≫ factorThruImageSubobject (signedAxioms a b) ≫ coprod.inr)
            (fun i => Fin.elim0 i)))))

private theorem label_one : label a b 0 ≫ nullaryConclusion a b =
    coefficientShapeConclusion a b 0 ≫ jF := by
  change (prod.map jF jF ≫ coprod.inl ≫ coprod.inl ≫ logicalTriple a b) ≫ _ = _
  rw [embed_one]
  simp only [Category.assoc, logicalTriple_conclusion]
  erw [coprod.inl_desc, coprod.inl_desc]

private theorem label_two : label a b 1 ≫ nullaryConclusion a b =
    coefficientShapeConclusion a b 1 ≫ jF := by
  change (prod.map (prod.map jF jF) jF ≫ coprod.inr ≫ coprod.inl ≫ logicalTriple a b) ≫ _ = _
  rw [embed_two]
  simp only [Category.assoc, logicalTriple_conclusion]
  erw [coprod.inl_desc, coprod.inr_desc]

private theorem label_three : label a b 2 ≫ nullaryConclusion a b =
    coefficientShapeConclusion a b 2 ≫ jF := by
  change (prod.map jF jF ≫ coprod.inr ≫ logicalTriple a b) ≫ _ = _
  rw [embed_three]
  simp only [Category.assoc, logicalTriple_conclusion]
  erw [coprod.inr_desc]

private theorem label_conclusion (i : Fin 5) : label a b i ≫ nullaryConclusion a b =
    coefficientShapeConclusion a b i ≫ jF := by
  fin_cases i
  · exact label_one a b
  · exact label_two a b
  · exact label_three a b
  · change (coprod.inl ≫ factorThruImageSubobject (signedAxioms a b) ≫ coprod.inr) ≫
      nullaryConclusion a b = coefficientShapeConclusion a b 3 ≫ embedding ≫ (S).sentenceInclusion
    rw [← Category.assoc (coefficientShapeConclusion a b 3), positive_embedding]
    simp [nullaryConclusion, axiomImage, signedAxioms]
  · change (coprod.inr ≫ factorThruImageSubobject (signedAxioms a b) ≫ coprod.inr) ≫
      nullaryConclusion a b = coefficientShapeConclusion a b 4 ≫ embedding ≫ (S).sentenceInclusion
    rw [← Category.assoc (coefficientShapeConclusion a b 4), negative_embedding]
    simp [nullaryConclusion, axiomImage, signedAxioms]

def nullaryMap : axioms a b ⟶ nullary a b := (axiomShapeIso a b).hom ≫ Sigma.desc (label a b)

theorem nullaryMap_conclusion : nullaryMap a b ≫ nullaryConclusion a b = lambda a b ≫ jF := by
  apply (cancel_epi (axiomShapeIso a b).inv).mp
  rw [nullaryMap, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    ← Category.assoc, axiomShapeIso_inverse_conclusion]
  apply Sigma.hom_ext
  intro i
  simpa only [shapedLambda, Sigma.ι_comp_desc_assoc] using label_conclusion a b i

/-- The empty unary coefficient maps uniquely into the generalization
coefficient. The binary coefficient maps the two formulas in order. -/
def translation : (rules a b).Translation ((S).logicalRules (axiomImage a b).arrow) where
  formula := jF
  map := Fin.cases (nullaryMap a b)
    (Fin.cases (initial.to _) (Fin.cases (prod.map jF jF) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · exact initial.hom_ext _ _
    · change prod.map jF jF ≫ prod.lift prod.fst (S).implicationConstructor =
        prod.lift prod.fst implication ≫ prod.map jF jF
      apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        prod.map_fst, prod.map_snd, prod.lift_fst_assoc, prod.lift_snd_assoc,
        ForkPropositionalEmbedding.formula_implication]
  conclusion i := by
    fin_cases i
    · exact nullaryMap_conclusion a b
    · exact initial.hom_ext _ _
    · exact prod.map_snd _ _

def embedDerivation := (translation a b).fold (inferenceAlgebra a b) (inferenceInitial a b)
  (proofFamily (axiomImage a b))

@[reassoc] theorem embedDerivation_conclusion : embedDerivation a b ≫
    (proofFamily (axiomImage a b)).a.hom = realization.map (ForkDerivation.conclusion a b) ≫ jF :=
  (translation a b).fold_conclusion (inferenceAlgebra a b) (inferenceInitial a b)
    (proofFamily (axiomImage a b))

theorem prop_le : propTheory a b ≤ (Subobject.pullback jF).obj (formulaTheory a b) := by
  let c := realization.map (ForkDerivation.conclusion a b)
  have h : (formulaTheory a b).Factors (c ≫ jF) := by
    rw [← embedDerivation_conclusion]
    exact imageSubobject_factors_comp_self _ _
  have hh := pullback_factors jF _ c h
  exact imageSubobject_le c (Subobject.factorThru _ c hh)
    (Subobject.factorThru_arrow _ c hh)

/-- Restriction to the propositional language is exactly the original
theory on the realized scalar-coded fork. -/
theorem conservativity : (Subobject.pullback embedding).obj (sentenceTheory a b) =
    propTheory a b := by
  rw [sentence_restriction, ← Subobject.pullback_comp]
  apply le_antisymm _ (prop_le a b)
  have h := (Subobject.pullback jF).monotone (formula_le a b)
  rw [← Subobject.pullback_comp] at h
  have hr : jF ≫ erase = 𝟙 sentences := ForkPropositionalEmbedding.retraction
  rwa [hr, Subobject.pullback_id] at h

theorem restriction_to_domain : (Subobject.pullback embedding).obj (sentenceTheory a b) =
    Subobject.mk (ForkDerivationImages.LiteralDiagram.theoremInclusion a b) :=
  (conservativity a b).trans (ForkDerivationImages.LiteralDiagram.theoremSubobject_eq_realizedImage a b)

end CategoricalEssentialIncompleteness.V46.ForkConservativeRestriction
