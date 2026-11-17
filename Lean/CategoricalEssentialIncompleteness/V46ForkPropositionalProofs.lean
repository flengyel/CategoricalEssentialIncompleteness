/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PropositionalProofCombinators
public import CategoricalEssentialIncompleteness.V46PropositionalSchemeTransport
public import CategoricalEssentialIncompleteness.V46ForkFirstOrderErasure

/-! # Uniform derivations in the original propositional fork proof carrier -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkPropositionalProofs
open ForkDerivation.Diagram PropositionalProofCombinators

private theorem source_one : ForkDerivation.H1 =
    ErasureLogicalSchemes.one ForkDerivation.implication := rfl

private theorem source_two : ForkDerivation.H2 =
    ErasureLogicalSchemes.two ForkDerivation.implication := by
  have h : prod.lift
      (prod.fst ≫ (prod.fst : ForkDerivation.sentenceObject ⨯
        ForkDerivation.sentenceObject ⟶ _))
      (prod.fst ≫ (prod.snd : ForkDerivation.sentenceObject ⨯
        ForkDerivation.sentenceObject ⟶ _)) =
      (prod.fst : (ForkDerivation.sentenceObject ⨯ ForkDerivation.sentenceObject) ⨯
        ForkDerivation.sentenceObject ⟶ _) := by
    apply prod.hom_ext <;> simp
  simp only [ForkDerivation.H2, ErasureLogicalSchemes.two, h]

private theorem source_three : ForkDerivation.H3 =
    ErasureLogicalSchemes.three ForkDerivation.negation ForkDerivation.implication := by
  simp [ForkDerivation.H3, ErasureLogicalSchemes.three]

theorem coefficient_one (a b : Idem EffectiveFork.V) :
    coefficientShapeConclusion a b 0 = ErasureLogicalSchemes.one implication := by
  change inv (prodComparison realization ForkDerivation.sentenceObject
    ForkDerivation.sentenceObject) ≫ realization.map ForkDerivation.H1 = _
  rw [source_one, PropositionalSchemeTransport.one]
  simp only [IsIso.inv_hom_id_assoc]
  rfl

theorem coefficient_two (a b : Idem EffectiveFork.V) :
    coefficientShapeConclusion a b 1 = ErasureLogicalSchemes.two implication := by
  change (coefficientShapeIso a b 1).inv ≫ realization.map ForkDerivation.H2 = _
  rw [source_two, PropositionalSchemeTransport.two]
  have h : (coefficientShapeIso a b 1).hom =
      PropositionalSchemeTransport.ternaryComparison realization ForkDerivation.sentenceObject :=
    rfl
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

theorem coefficient_three (a b : Idem EffectiveFork.V) :
    coefficientShapeConclusion a b 2 =
      ErasureLogicalSchemes.three ForkFirstOrderErasure.negation implication := by
  change inv (prodComparison realization ForkDerivation.sentenceObject
    ForkDerivation.sentenceObject) ≫ realization.map ForkDerivation.H3 = _
  rw [source_three, PropositionalSchemeTransport.three]
  simp only [IsIso.inv_hom_id_assoc]
  rfl

def axiomProof (a b : Idem EffectiveFork.V) (i : Fin 5) :
    Proof (inferenceAlgebra a b) (coefficientShapeConclusion a b i) where
  hom := Sigma.ι (coefficientShape a b) i ≫ (axiomShapeIso a b).inv ≫
    (rules a b).nullaryToProof (inferenceAlgebra a b)
  conclusion := by
    rw [Category.assoc, Category.assoc, RulePresentation.nullaryToProof_conclusion]
    change Sigma.ι (coefficientShape a b) i ≫ (axiomShapeIso a b).inv ≫ lambda a b = _
    rw [axiomShapeIso_inverse_conclusion, shapedLambda_branch]
    rfl

/-- The scheme witnesses are constructed from the actual Fin 5 coproduct. -/
def schemes (a b : Idem EffectiveFork.V) :
    Schemes (inferenceAlgebra a b) ForkFirstOrderErasure.negation where
  one := (axiomProof a b 0).restate (coefficient_one a b)
  two := (axiomProof a b 1).restate (coefficient_two a b)
  three := (axiomProof a b 2).restate (coefficient_three a b)

def identity (a b : Idem EffectiveFork.V) {W : Object} (f : W ⟶ sentences) :
    Proof (inferenceAlgebra a b) (implies implication f f) := (schemes a b).identity f

def weaken (a b : Idem EffectiveFork.V) {W : Object} {f : W ⟶ sentences}
    (p : Proof (inferenceAlgebra a b) f) (g : W ⟶ sentences) :
    Proof (inferenceAlgebra a b) (implies implication g f) := (schemes a b).weaken p g

/-- The printed p_* ⇒ p_* has an actual global finite derivation. -/
def truth (a b : Idem EffectiveFork.V) :
    Proof (inferenceAlgebra a b) ForkFirstOrderErasure.truth :=
  identity a b ForkFirstOrderErasure.distinguishedAtom

end CategoricalEssentialIncompleteness.V46.ForkPropositionalProofs
