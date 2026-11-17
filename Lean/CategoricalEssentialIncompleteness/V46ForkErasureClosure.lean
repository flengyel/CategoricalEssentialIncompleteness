/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RuleClosureFactors
public import CategoricalEssentialIncompleteness.V46ForkDerivationImages
public import CategoricalEssentialIncompleteness.V46ForkErasedSchemeProofs
public import CategoricalEssentialIncompleteness.V46ForkParameterizedDeduction
public import CategoricalEssentialIncompleteness.V46ForkPropositionalEmbedding

/-! # Erasure bounds the generated first-order fork theory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkErasureClosure
open ForkDerivation.Diagram ForkFirstOrderErasure
open ForkPropositionalEmbedding (embedding formulaEmbedding)
local notation "S" => firstOrder
abbrev propTheory := ForkDerivationImages.LiteralDiagram.theoremSubobject

def labelInclusion (a : Idem EffectiveFork.V) :
    realization.obj (ForkDerivation.axiomDomain a) ⟶ labels :=
  realization.map (ForkDerivation.axiomInclusion a)

variable (a b : Idem EffectiveFork.V)

def positive := labelInclusion a ≫ NullaryInterpretation.atomSentence (S)
def negative := labelInclusion b ≫ NullaryInterpretation.atomSentence (S) ≫ (S).sentenceNegation

def signedAxioms := coprod.desc (positive a) (negative b)
def axiomImage := imageSubobject (signedAxioms a b)

theorem signed_image : axiomImage a b =
    imageSubobject (positive a) ⊔ imageSubobject (negative b) :=
  PresentationLemmas.image_copair _ _

theorem positive_embedding : coefficientShapeConclusion a b 3 ≫ embedding = positive a := by
  change (𝟙 _ ≫ realization.map (ForkDerivation.axiomInclusion a ≫ ForkDerivation.atom)) ≫
    embedding = _
  rw [Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun f => labelInclusion a ≫ f) ForkPropositionalEmbedding.atom

theorem negative_embedding : coefficientShapeConclusion a b 4 ≫ embedding = negative b := by
  change (𝟙 _ ≫ realization.map (ForkDerivation.axiomInclusion b ≫
    ForkDerivation.atom ≫ ForkDerivation.negation)) ≫ embedding = _
  simp only [Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  change labelInclusion b ≫ atom ≫ negation ≫ embedding = _
  rw [ForkPropositionalEmbedding.negation, ForkPropositionalEmbedding.atom_assoc]
  rfl

abbrev proofFamily := ForkParameterizedDeduction.nullaryPresentations.proofs labels
def formulaTheory := FirstOrderReflection.formulaTheory proofFamily (axiomImage a b)
def sentenceTheory := FirstOrderReflection.generated proofFamily (axiomImage a b)

theorem sentence_restriction : sentenceTheory a b =
    (Subobject.pullback (S).sentenceInclusion).obj (formulaTheory a b) :=
  FirstOrderReflection.generated_eq_pullback _ _

def erasedTheory := (Subobject.pullback erase).obj (propTheory a b)

private theorem erased_coefficient (i : Fin 5) :
    (propTheory a b).Factors (coefficientShapeConclusion a b i) := by
  let p := ForkPropositionalProofs.axiomProof a b i
  rw [← p.conclusion]
  exact imageSubobject_factors_comp_self _ p.hom

/-- Factor the signed presentation into the sentence pullback and use
image leastness to descend to the actual nonlogical axiom subobject. -/
theorem signed_le : axiomImage a b ≤
    (Subobject.pullback (S).sentenceInclusion).obj (erasedTheory a b) := by
  let U := (Subobject.pullback (S).sentenceInclusion).obj (erasedTheory a b)
  have branch {W : Object} (f : W ⟶ sentences) (hf : (propTheory a b).Factors f) :
      U.Factors (f ≫ embedding) := by
    apply pullback_factors
    apply pullback_factors
    simpa only [Category.assoc, ForkPropositionalEmbedding.retraction, Category.comp_id] using hf
  have hp := branch _ (erased_coefficient a b 3)
  have hn := branch _ (erased_coefficient a b 4)
  rw [positive_embedding] at hp
  rw [negative_embedding] at hn
  change imageSubobject (signedAxioms a b) ≤ U
  exact imageSubobject_le _ (coprod.desc (U.factorThru _ hp) (U.factorThru _ hn))
    (by simp [signedAxioms, coprod.desc_comp])

theorem generalization {W : Object} (z : W ⟶ ForkFirstOrderFormula.numbers ⨯ formulas)
    (h : (erasedTheory a b).Factors (z ≫ prod.snd)) :
    (erasedTheory a b).Factors (z ≫ (S).quantifierConstructor) := by
  apply pullback_factors
  simpa only [Category.assoc, quantifier] using
    (pullback_factors_iff erase _ _).mp h

theorem modus_ponens {W : Object} (z : W ⟶ formulas ⨯ formulas)
    (hp : (erasedTheory a b).Factors (z ≫ prod.fst))
    (hq : (erasedTheory a b).Factors (z ≫ (S).implicationConstructor)) :
    (erasedTheory a b).Factors (z ≫ prod.snd) := by
  have hT := (ForkDerivationImages.LiteralDiagram.theoremSubobject_isLeast a b).1
  apply pullback_factors
  have h := RuleClosureFactors.propositional_mp (lambda a b) implication (propTheory a b) hT
    (z ≫ prod.map erase erase)
  simpa only [Category.assoc, prod.map_snd] using
    h (by simpa only [Category.assoc, prod.map_fst] using
        (pullback_factors_iff erase _ _).mp hp)
      (by simpa only [Category.assoc, implication_law] using
        (pullback_factors_iff erase _ _).mp hq)

theorem closed : ClosedUnder ((S).logicalRules (axiomImage a b).arrow).inference
    (erasedTheory a b).arrow := by
  apply RuleClosureFactors.firstOrder_closed
  · let T := erasedTheory a b
    have hl : T.Factors (S).logicalAxioms := pullback_factors erase _ _
      ((Subobject.factors_iff _ _).mpr (ForkErasedSchemeProofs.image_factor a b))
    have hn := (pullback_factors_iff (S).sentenceInclusion T _).mp
      (Subobject.factors_of_le _ (signed_le a b) (Subobject.factors_self _))
    change T.Factors _
    apply (Subobject.factors_iff _ _).mpr
    exact ⟨coprod.desc (T.factorThru _ hl) (T.factorThru _ hn), by
      simp [coprod.desc_comp]⟩
  · exact generalization a b
  · exact modus_ponens a b

/-- Leastness of the initial proof image gives the formula-level bound. -/
theorem formula_le : formulaTheory a b ≤ (Subobject.pullback erase).obj (propTheory a b) := by
  let Q := proofFamily (axiomImage a b)
  obtain ⟨w, hw⟩ := ((S).logicalRules (axiomImage a b).arrow).least_theorem_subobject Q
    (ForkParameterizedDeduction.nullaryPresentations.initial labels _) |>.2
      (erasedTheory a b).arrow (closed a b)
  change imageSubobject Q.a.hom ≤ erasedTheory a b
  exact imageSubobject_le Q.a.hom (factorThruImage _ ≫ w) (by rw [Category.assoc, hw, image.fac])

end CategoricalEssentialIncompleteness.V46.ForkErasureClosure
