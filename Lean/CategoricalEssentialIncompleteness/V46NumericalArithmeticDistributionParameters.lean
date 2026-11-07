/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleParameters
import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionValues

/-! # The actual arithmetic absent-variable scheme label comparison -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionParameters
open Coordinates SubstitutionParameters SubstitutionDomains RuleParameters NamedArithmeticSignature
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
local notation "F" => PredicateInterpretation.functor 𝗣𝗔 ℕ
private abbrev formulaObject := numericalSyntax.algebra.a.2
private abbrev originalFormulaObject := originalSyntax.algebra.a.2
local notation "Y" => formulaObject
local notation "Y₀" => originalFormulaObject
local notation "B" => NumericalNamed.variableObject ⨯ (Y ⨯ Y)
local notation "B₀" => variableSymbols ⨯ (Y₀ ⨯ Y₀)

@[reassoc] theorem name_coordinate : distributionBaseIso.hom ≫
    numericalInterpretation.map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := variableSymbols) («Y» := (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀))) =
      prod.fst ≫ variableIso.hom := pairedIso_fst variableIso formulaPairIso

@[reassoc] theorem first_coordinate : distributionBaseIso.hom ≫
    numericalInterpretation.map ((prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableSymbols) («Y» := (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀))) ≫ prod.fst) =
      prod.snd ≫ prod.fst ≫ formulaIso.hom := by
  exact pairedIso_snd_fst variableIso formulaIso formulaIso

@[reassoc] theorem second_coordinate : distributionBaseIso.hom ≫
    numericalInterpretation.map ((prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableSymbols) («Y» := (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀))) ≫ prod.snd) =
      prod.snd ≫ prod.snd ≫ formulaIso.hom := by
  exact pairedIso_snd_snd variableIso formulaIso formulaIso

private theorem model_name (q : NumericalTuples.Point B) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := variableSymbols) («Y» := (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀))) (distributionBaseIso.hom.toFun q)).val =
      ((prod.fst : B ⟶ NumericalNamed.variableObject).toFun q).val := by
  exact congrArg Subtype.val (pairedIso_fst_point variableIso formulaPairIso q)

private theorem model_formula (q : NumericalTuples.Point B) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y₀) («Y» := Y₀))
      ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableSymbols) («Y» := (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀))) (distributionBaseIso.hom.toFun q))).val =
      ((NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound).hom.toFun
        ((prod.fst : Y ⨯ Y ⟶ Y).toFun ((prod.snd : B ⟶ Y ⨯ Y).toFun q))).val := by
  have ho := pairedIso_snd_point variableIso formulaPairIso q
  have hi := pairedIso_fst_point formulaIso formulaIso ((prod.snd : B ⟶ Y ⨯ Y).toFun q)
  exact (congrArg (fun z : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗣𝗔) Y₀ Y₀) =>
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y₀) («Y» := Y₀)) z).val) ho).trans
      ((congrArg Subtype.val hi).trans (formulaIso_value _))

private theorem occurrence_congr (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    {x w x' w' : ℕ} (hx : x = x') (hw : w = w') :
    ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.freeVariables (M := ℕ) V σ π d w) =
      ConcreteNamedSubstitution.member x' (ConcreteNamedSubstitution.freeVariables (M := ℕ) V σ π d w') := by
  cases hx
  cases hw
  rfl

/-- The two actual false-fiber inclusions have the same point image
under the already constructed name/formula product chart. -/
theorem image_iff (q : NumericalTuples.Point B) :
    (∃ a, (S).distributionInclusion.toFun a = q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj (S₀).distributionParameters),
        (numericalInterpretation.map (S₀).distributionInclusion).toFun a =
          distributionBaseIso.hom.toFun q := by
  have hn := DistributionValues.parameter_image_iff NumericalNamed.variableObject functions relations bound q
  have hp := DistributionModels.parameter_image_iff 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ
    (distributionBaseIso.hom.toFun q)
  have hx := (DistributionValues.base_name_value NumericalNamed.variableObject functions relations bound q).trans
    (NumericalTuples.code_one _)
  have hw := DistributionValues.base_formula_value NumericalNamed.variableObject functions relations bound q
  have hnc := occurrence_congr (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
    (LiteralSignature.coefficients functionSymbols) (LiteralSignature.coefficients relationSymbols) bound hx hw
  have hpc := occurrence_congr variableSymbols functionSymbols relationSymbols bound
    (model_name q) (model_formula q)
  have hn' := hn.trans (Iff.of_eq (congrArg (fun n : ℕ => n = 0) hnc))
  have hp' := hp.trans (Iff.of_eq (congrArg (fun n : ℕ => n = 0) hpc))
  have hf := Algorithms.freeVariables_signature (M := ℕ)
    (NumericalCoordinates.codedPredicate NumericalNamed.variableObject) variableSymbols
    (LiteralSignature.coefficients functionSymbols) functionSymbols
    (LiteralSignature.coefficients relationSymbols) relationSymbols bound
    ((NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound).hom.toFun
      ((prod.fst : Y ⨯ Y ⟶ Y).toFun ((prod.snd : B ⟶ Y ⨯ Y).toFun q))).val
  have hb := Iff.of_eq (congrArg (fun a : ℕ => ConcreteNamedSubstitution.member (M := ℕ)
    ((prod.fst : B ⟶ NumericalNamed.variableObject).toFun q).val a = 0) hf)
  have hi :
      (∃ a : PredicateInterpretation.Obj ℕ (S₀).distributionParameters,
        (F).map (S₀).distributionInclusion a = distributionBaseIso.hom.toFun q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj (S₀).distributionParameters),
        (numericalInterpretation.map (S₀).distributionInclusion).toFun a =
          distributionBaseIso.hom.toFun q := by
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,(numericalInterpretation_value (S₀).distributionInclusion a).trans ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,(numericalInterpretation_value (S₀).distributionInclusion a).symm.trans ha⟩
  exact hn'.trans (hb.trans (hp'.symm.trans hi))

private theorem forward_image (a : NumericalTuples.Point (S).distributionParameters) :
    ∃ b, (numericalInterpretation.map (S₀).distributionInclusion).toFun b =
      ((S).distributionInclusion ≫ distributionBaseIso.hom).toFun a :=
  (image_iff ((S).distributionInclusion.toFun a)).mp ⟨a,rfl⟩

def forward : (S).distributionParameters ⟶ numericalInterpretation.obj (S₀).distributionParameters :=
  imageLift (numericalInterpretation.map (S₀).distributionInclusion)
    ((S).distributionInclusion ≫ distributionBaseIso.hom) forward_image

@[reassoc] theorem forward_inclusion :
    forward ≫ numericalInterpretation.map (S₀).distributionInclusion =
      (S).distributionInclusion ≫ distributionBaseIso.hom := imageLift_comp _ _ forward_image

private theorem backward_image
    (a : NumericalTuples.Point (numericalInterpretation.obj (S₀).distributionParameters)) :
    ∃ b, (S).distributionInclusion.toFun b =
      (numericalInterpretation.map (S₀).distributionInclusion ≫ distributionBaseIso.inv).toFun a := by
  let q : NumericalTuples.Point B := distributionBaseIso.inv.toFun
    ((numericalInterpretation.map (S₀).distributionInclusion).toFun a)
  apply (image_iff q).mpr
  exact ⟨a,(congrArg (fun f => f.toFun ((numericalInterpretation.map (S₀).distributionInclusion).toFun a))
    distributionBaseIso.inv_hom_id).symm⟩

def backward : numericalInterpretation.obj (S₀).distributionParameters ⟶ (S).distributionParameters :=
  imageLift (S).distributionInclusion
    (numericalInterpretation.map (S₀).distributionInclusion ≫ distributionBaseIso.inv) backward_image

@[reassoc] theorem backward_inclusion : backward ≫ (S).distributionInclusion =
    numericalInterpretation.map (S₀).distributionInclusion ≫ distributionBaseIso.inv := imageLift_comp _ _ backward_image

/-- Its programs come from the actual pullback projection isomorphisms;
they need not be total outside these coefficient carriers. -/
def iso : (S).distributionParameters ≅ numericalInterpretation.obj (S₀).distributionParameters where
  hom := forward
  inv := backward
  hom_inv_id := by
    apply (cancel_mono (S).distributionInclusion).1
    rw [Category.assoc,backward_inclusion,← Category.assoc,forward_inclusion]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (numericalInterpretation.map (S₀).distributionInclusion)).1
    rw [Category.assoc,forward_inclusion,← Category.assoc,backward_inclusion]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Category.id_comp]

@[reassoc] theorem inclusion : iso.hom ≫ numericalInterpretation.map (S₀).distributionInclusion =
    (S).distributionInclusion ≫ distributionBaseIso.hom := forward_inclusion

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionParameters
