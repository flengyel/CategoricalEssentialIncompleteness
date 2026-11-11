/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationComponentsCoordinates

/-! # Component rule and slice-algebra comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

private theorem nativeH1_value (x : NumericalTuples.Point (finitePower Component.formulaObject 2)) :
    (nativeH1.toFun x).val =
      (ForkSyntax.H1 (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x))).encode := by
  have h : Component.formulaAt (nativeH1.toFun x) =
      ForkSyntax.H1 (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x)) := by
    simp only [nativeH1,NumericalTuples.composition_apply,native_implication_formula,
      point_lift_fst,point_lift_snd,ForkSyntax.H1]
    rfl
  simpa only [Component.formulaAt,ForkSyntax.Formula.encode_decode] using congrArg ForkSyntax.Formula.encode h

private theorem nativeH2_value (x : NumericalTuples.Point (finitePower Component.formulaObject 3)) :
    (nativeH2.toFun x).val =
      (ForkSyntax.H2 (Component.formulaAt (Component.firstPoint (Component.firstPoint x)))
        (Component.formulaAt (Component.secondPoint (Component.firstPoint x))) (Component.formulaAt (Component.secondPoint x))).encode := by
  have h : Component.formulaAt (nativeH2.toFun x) =
      ForkSyntax.H2 (Component.formulaAt (Component.firstPoint (Component.firstPoint x)))
        (Component.formulaAt (Component.secondPoint (Component.firstPoint x))) (Component.formulaAt (Component.secondPoint x)) := by
    simp only [nativeH2,NumericalTuples.composition_apply,native_implication_formula,
      point_lift_fst,point_lift_snd,ForkSyntax.H2]
    rfl
  simpa only [Component.formulaAt,ForkSyntax.Formula.encode_decode] using congrArg ForkSyntax.Formula.encode h

private theorem nativeH3_value (x : NumericalTuples.Point (finitePower Component.formulaObject 2)) :
    (nativeH3.toFun x).val =
      (ForkSyntax.H3 (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x))).encode := by
  have h : Component.formulaAt (nativeH3.toFun x) =
      ForkSyntax.H3 (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x)) := by
    simp only [nativeH3,NumericalTuples.composition_apply,native_implication_formula,native_negation_formula,
      point_lift_fst,point_lift_snd,ForkSyntax.H3]
    rfl
  simpa only [Component.formulaAt,ForkSyntax.Formula.encode_decode] using congrArg ForkSyntax.Formula.encode h

@[reassoc] theorem componentTripleIso_first (j : WalkingSpan) :
    ((componentPowerIso j 3).hom ≫ prod.fst) ≫ prod.fst =
      (componentFunctor j).map ((prod.fst : (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject ⟶
        sentenceObject ⨯ sentenceObject) ≫ prod.fst) ≫ (componentFormulaIso j).hom := by
  rw [componentTripleIso_fst,Category.assoc,componentPowerIso_fst,← Functor.map_comp_assoc]

@[reassoc] theorem componentTripleIso_second (j : WalkingSpan) :
    ((componentPowerIso j 3).hom ≫ prod.fst) ≫ prod.snd =
      (componentFunctor j).map ((prod.fst : (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject ⟶
        sentenceObject ⨯ sentenceObject) ≫ prod.snd) ≫ (componentFormulaIso j).hom := by
  rw [componentTripleIso_fst,Category.assoc,componentPowerIso_snd,← Functor.map_comp_assoc]

theorem component_H1 (j : WalkingSpan) :
    (componentFunctor j).map H1 ≫ (componentFormulaIso j).hom = (componentPowerIso j 2).hom ≫ nativeH1 := by
  simp only [H1,component_pair_implication,nativeH1,← Category.assoc,prod.comp_lift]
  erw [componentPowerIso_fst j,componentPowerIso_snd j]

theorem component_H2 (j : WalkingSpan) :
    (componentFunctor j).map H2 ≫ (componentFormulaIso j).hom = (componentPowerIso j 3).hom ≫ nativeH2 := by
  simp only [H2,component_pair_implication,nativeH2,← Category.assoc,prod.comp_lift]
  erw [componentTripleIso_first j,componentTripleIso_second j,componentTripleIso_snd j]

theorem component_H3 (j : WalkingSpan) :
    (componentFunctor j).map H3 ≫ (componentFormulaIso j).hom = (componentPowerIso j 2).hom ≫ nativeH3 := by
  simp only [H3,component_pair_implication,component_composed_negation,nativeH3,
    ← Category.assoc,prod.comp_lift]
  erw [componentPowerIso_fst j,componentPowerIso_snd j]

private theorem native_logical1_conclusion (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    Component.logical1Proof A B hA hB ≫ Component.conclusion A B hA hB = nativeH1 := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact (Component.proofPoint_conclusion A B hA hB (ForkSyntax.Concludes.logical1
    (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x)))).trans
      (nativeH1_value x).symm

private theorem native_logical2_conclusion (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    Component.logical2Proof A B hA hB ≫ Component.conclusion A B hA hB = nativeH2 := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact (Component.proofPoint_conclusion A B hA hB (ForkSyntax.Concludes.logical2
    (Component.formulaAt (Component.firstPoint (Component.firstPoint x)))
    (Component.formulaAt (Component.secondPoint (Component.firstPoint x))) (Component.formulaAt (Component.secondPoint x)))).trans
      (nativeH2_value x).symm

private theorem native_logical3_conclusion (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    Component.logical3Proof A B hA hB ≫ Component.conclusion A B hA hB = nativeH3 := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact (Component.proofPoint_conclusion A B hA hB (ForkSyntax.Concludes.logical3
    (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x)))).trans
      (nativeH3_value x).symm

private theorem native_positive_conclusion (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    Component.positiveProof A B hA hB ≫ Component.conclusion A B hA hB = nativeInclusion A hA ≫ nativeAtom := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact Component.proofPoint_conclusion A B hA hB (ForkSyntax.Concludes.positive x.property)

private theorem native_negative_conclusion (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    Component.negativeProof A B hA hB ≫ Component.conclusion A B hA hB =
      nativeInclusion B hB ≫ nativeAtom ≫ nativeNegation := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact Component.proofPoint_conclusion A B hA hB (ForkSyntax.Concludes.negative x.property)


@[reassoc] theorem componentAxiomIso_iota (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 5) :
    (componentFunctor j).map (Sigma.ι (axiomCoefficients a b) i) ≫ (componentAxiomIso a b j).hom =
      (componentCoefficientIso a b j i).hom ≫
        Sigma.ι (Component.axiomFamily (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)) i := by
  simp only [componentAxiomIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

theorem component_positive (j : WalkingSpan) (a : Idem EffectiveFork.V) :
    (componentFunctor j).map (axiomInclusion a ≫ atom) ≫ (componentFormulaIso j).hom =
      (componentAxiomDomainIso j a).hom ≫
        nativeInclusion (componentSupport j a) (componentSupport_re j a) ≫ nativeAtom := by
  rw [Functor.map_comp,Category.assoc,component_atom,← Category.assoc,
    component_axiomInclusion,Category.assoc]

theorem component_negative (j : WalkingSpan) (a : Idem EffectiveFork.V) :
    (componentFunctor j).map (axiomInclusion a ≫ atom ≫ negation) ≫ (componentFormulaIso j).hom =
      (componentAxiomDomainIso j a).hom ≫
        nativeInclusion (componentSupport j a) (componentSupport_re j a) ≫ nativeAtom ≫ nativeNegation := by
  calc
    _ = (componentFunctor j).map (axiomInclusion a) ≫ (componentFunctor j).map atom ≫
        (componentFunctor j).map negation ≫ (componentFormulaIso j).hom := by
      simp only [Functor.map_comp,Category.assoc]
    _ = (componentFunctor j).map (axiomInclusion a) ≫ (componentFunctor j).map atom ≫
        (componentFormulaIso j).hom ≫ nativeNegation := by rw [component_negation]
    _ = _ := by
      simpa only [Functor.map_comp,Category.assoc] using
        congrArg (fun g => g ≫ nativeNegation) (component_positive j a)

section FiniteSumComparison
variable {C D : Type} [Category C] [Category D]
variable [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable {I : Type} [Finite I]

/-- The coproduct comparison follows from the individual coefficient squares. -/
private theorem map_sum_constructor (K : C ⥤ D) [PreservesFiniteCoproducts K]
    (X : I → C) (Y : I → D) (e : ∀ i, K.obj (X i) ≅ Y i)
    {F : C} {G : D} (p : ∀ i, X i ⟶ F) (f : K.obj F ⟶ G) (q : (∐ Y) ⟶ G)
    (h : ∀ i, K.map (p i) ≫ f = (e i).hom ≫ Limits.Sigma.ι Y i ≫ q) :
    K.map (Limits.Sigma.desc p) ≫ f =
      ((asIso (sigmaComparison K X)).symm ≪≫ Limits.Sigma.mapIso e).hom ≫ q := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Limits.Sigma.hom_ext
  intro i
  calc
    _ = K.map (Limits.Sigma.ι X i) ≫ K.map (Limits.Sigma.desc p) ≫ f := by
      rw [← Category.assoc,ι_comp_sigmaComparison]
    _ = K.map (p i) ≫ f := by rw [← Category.assoc,← K.map_comp,Limits.Sigma.ι_comp_desc]
    _ = (e i).hom ≫ Limits.Sigma.ι Y i ≫ q := h i
    _ = _ := by
      simp only [Iso.trans_hom,Iso.symm_hom,asIso_inv,
        Category.assoc,IsIso.hom_inv_id_assoc,Limits.Sigma.ι_mapIso_hom_assoc]
end FiniteSumComparison

private theorem native_axiom_iota_conclusion (A B : Set ℕ)
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) (i : Fin 5) :
    Limits.Sigma.ι (Component.axiomFamily A B hA hB) i ≫ (Component.rules A B hA hB).conclusion 0 =
      Component.axiomBranch A B hA hB i ≫ Component.conclusion A B hA hB := by
  change Limits.Sigma.ι (Component.axiomFamily A B hA hB) i ≫
      (Limits.Sigma.desc (Component.axiomBranch A B hA hB) ≫ Component.conclusion A B hA hB) = _
  rw [← Category.assoc,Limits.Sigma.ι_comp_desc]

private theorem component_coefficient_conclusion (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 5) :
    (componentFunctor j).map (axiomConclusions a b i) ≫ (componentFormulaIso j).hom =
      (componentCoefficientIso a b j i).hom ≫
        Limits.Sigma.ι (Component.axiomFamily (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)) i ≫
            (Component.rules (componentSupport j a) (componentSupport j b)
              (componentSupport_re j a) (componentSupport_re j b)).conclusion 0 := by
  erw [native_axiom_iota_conclusion (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) i]
  fin_cases i
  · change (componentFunctor j).map H1 ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 2).hom ≫ (Component.logical1Proof _ _ _ _ ≫ Component.conclusion _ _ _ _)
    erw [native_logical1_conclusion]
    exact component_H1 j
  · change (componentFunctor j).map H2 ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 3).hom ≫ (Component.logical2Proof _ _ _ _ ≫ Component.conclusion _ _ _ _)
    erw [native_logical2_conclusion]
    exact component_H2 j
  · change (componentFunctor j).map H3 ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 2).hom ≫ (Component.logical3Proof _ _ _ _ ≫ Component.conclusion _ _ _ _)
    erw [native_logical3_conclusion]
    exact component_H3 j
  · change (componentFunctor j).map (axiomInclusion a ≫ atom) ≫ (componentFormulaIso j).hom =
      (componentAxiomDomainIso j a).hom ≫ (Component.positiveProof _ _ _ _ ≫ Component.conclusion _ _ _ _)
    erw [native_positive_conclusion]
    exact component_positive j a
  · change (componentFunctor j).map (axiomInclusion b ≫ atom ≫ negation) ≫ (componentFormulaIso j).hom =
      (componentAxiomDomainIso j b).hom ≫ (Component.negativeProof _ _ _ _ ≫ Component.conclusion _ _ _ _)
    erw [native_negative_conclusion]
    exact component_negative j b

/-- The finite axiom-family comparison commutes with the actual
conclusion maps, on every logical and nonlogical branch. -/
theorem component_lambda (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (lambda a b) ≫ (componentFormulaIso j).hom =
      (componentAxiomIso a b j).hom ≫
        (Component.rules (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)).conclusion 0 := by
  have h := map_sum_constructor (componentFunctor j) (axiomCoefficients a b)
    (Component.axiomFamily (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b))
    (componentCoefficientIso a b j) (axiomConclusions a b)
    (componentFormulaIso j).hom
    ((Component.rules (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)).conclusion 0)
    (component_coefficient_conclusion a b j)
  exact h

@[simp] theorem powerCongr_hom {X Y : NumericalTuples.Object} (e : X ≅ Y) (n : ℕ) :
    (powerCongr e n).hom = finitePowerMap e.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [powerCongr,prod.mapIso_hom,finitePowerMap,ih]

theorem componentPowerIso_hom (j : WalkingSpan) (n : ℕ) :
    (componentPowerIso j n).hom =
      (Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject n).hom ≫
        finitePowerMap (componentFormulaIso j).hom n := by
  simp only [componentPowerIso,Iso.trans_hom,powerCongr_hom]

theorem component_premise_pair (j : WalkingSpan) :
    (componentPowerIso j 2).hom ≫ prod.lift prod.fst Component.implication =
      (componentFunctor j).map (prod.lift prod.fst implication) ≫ (componentPowerIso j 2).hom := by
  apply prod.hom_ext
  · simp only [Category.assoc,prod.lift_fst,componentPowerIso_fst,
      ← Functor.map_comp_assoc]
  · simp only [Category.assoc,prod.lift_snd,componentPowerIso_snd,
      ← Functor.map_comp_assoc,component_implication]

theorem component_rule_premises (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).premises i =
      (componentRebasedRules a b j).premises i := by
  fin_cases i
  · exact terminal.hom_ext _ _
  · exact (initialIsInitial.ofIso (componentRuleIso a b j 1).symm).hom_ext _ _
  · change (componentPowerIso j 2).hom ≫ prod.lift prod.fst Component.implication =
      (componentFunctor j).map (prod.lift prod.fst implication) ≫
        ((Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject 2).hom ≫
          finitePowerMap (componentFormulaIso j).hom 2)
    rw [← componentPowerIso_hom]
    exact component_premise_pair j

theorem component_rule_conclusion (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).conclusion i =
      (componentRebasedRules a b j).conclusion i := by
  fin_cases i
  · exact (component_lambda a b j).symm
  · exact (initialIsInitial.ofIso (componentRuleIso a b j 1).symm).hom_ext _ _
  · change (componentPowerIso j 2).hom ≫ prod.snd =
      (componentFunctor j).map prod.snd ≫ (componentFormulaIso j).hom
    exact componentPowerIso_snd j

def componentRuleHom (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    RulePresentation.Hom (componentRebasedRules a b j)
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)) where
  map i := (componentRuleIso a b j i).hom
  premises := component_rule_premises a b j
  conclusion := component_rule_conclusion a b j

def componentRuleInverse (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    RulePresentation.Hom
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)) (componentRebasedRules a b j) where
  map i := (componentRuleIso a b j i).inv
  premises i := by rw [← component_rule_premises a b j i,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  conclusion i := by rw [← component_rule_conclusion a b j i,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

def componentInferenceIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentRebasedRules a b j).inference ≅
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference :=
  NumericalRuleRelabel.inferenceIso (componentRuleHom a b j) (componentRuleInverse a b j)
    (fun i => (componentRuleIso a b j i).hom_inv_id)
    (fun i => (componentRuleIso a b j i).inv_hom_id)


def componentOver (Q : Over sentenceObject) (j : WalkingSpan) : Over Component.formulaObject :=
  Over.mk ((componentFunctor j).map Q.hom ≫ (componentFormulaIso j).hom)

def componentOverFunctor (j : WalkingSpan) : Over sentenceObject ⥤ Over Component.formulaObject :=
  Over.post (componentFunctor j) ⋙ (NumericalRuleRebase.slice (componentFormulaIso j)).functor

def componentOverMap {Q Q' : Over sentenceObject} (f : Q ⟶ Q') (j : WalkingSpan) :
    componentOver Q j ⟶ componentOver Q' j := (componentOverFunctor j).map f

@[simp] theorem componentOverMap_left {Q Q' : Over sentenceObject} (f : Q ⟶ Q') (j : WalkingSpan) :
    (componentOverMap f j).left = (componentFunctor j).map f.left := rfl

def componentInputComparison (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (rules a b).inference ⋙ componentOverFunctor j ≅ componentOverFunctor j ⋙
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference := by
  let L := Evaluation.overFunctor (K := componentFunctor j) (rules a b)
  let E := (NumericalRuleRebase.slice (componentFormulaIso j)).functor
  exact (Functor.associator (rules a b).inference L E).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (Evaluation.comparison (K := componentFunctor j) (rules a b)) E ≪≫
    Functor.associator L (evaluatedRules a b j).inference E ≪≫
    CategoryTheory.Functor.isoWhiskerLeft L (NumericalRuleRebase.comparison (evaluatedRules a b j) (componentFormulaIso j)) ≪≫
    (Functor.associator L E (componentRebasedRules a b j).inference).symm ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (L ⋙ E) (componentInferenceIso a b j)

def componentOverInputIso (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) :
    componentOver ((rules a b).inference.obj Q) j ≅
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j) :=
  (componentInputComparison a b j).app Q

def componentInputIso (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) :
    (componentFunctor j).obj ((rules a b).inference.obj Q).left ≅
      ((Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j)).left :=
  (Over.forget Component.formulaObject).mapIso (componentOverInputIso a b Q j)

@[reassoc] theorem componentInputIso_conclusion (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (j : WalkingSpan) :
    (componentInputIso a b Q j).hom ≫
      ((Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j)).hom =
      (componentFunctor j).map ((rules a b).inference.obj Q).hom ≫ (componentFormulaIso j).hom :=
  Over.w (componentOverInputIso a b Q j).hom

theorem componentInputIso_hom (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) :
    (componentInputIso a b Q j).hom =
      (Evaluation.sumIso (K := componentFunctor j) (rules a b) Q).hom ≫
        (Limits.Sigma.mapIso (NumericalRuleRebase.inputIso (evaluatedRules a b j) (componentFormulaIso j)
          ((Evaluation.overFunctor (K := componentFunctor j) (rules a b)).obj Q))).hom ≫
        Limits.Sigma.map ((componentRuleHom a b j).mapRule (componentOver Q j)) := by
  rfl

theorem componentOverInputIso_natural (a b : Idem EffectiveFork.V)
    {Q Q' : Over sentenceObject} (f : Q ⟶ Q') (j : WalkingSpan) :
    componentOverMap ((rules a b).inference.map f) j ≫ (componentOverInputIso a b Q' j).hom =
      (componentOverInputIso a b Q j).hom ≫
        (Component.rules (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)).inference.map (componentOverMap f j) :=
  (componentInputComparison a b j).hom.naturality f

@[reassoc] theorem componentInputIso_natural (a b : Idem EffectiveFork.V)
    {Q Q' : Over sentenceObject} (f : Q ⟶ Q') (j : WalkingSpan) :
    (componentFunctor j).map ((rules a b).inference.map f).left ≫ (componentInputIso a b Q' j).hom =
      (componentInputIso a b Q j).hom ≫
        ((Component.rules (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)).inference.map (componentOverMap f j)).left :=
  congrArg (fun k => k.left) (componentOverInputIso_natural a b f j)

def componentComparison (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (rules a b).inference ⋙ componentOverFunctor j ≅ componentOverFunctor j ⋙
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference :=
  componentInputComparison a b j

section AlgebraFunctor
variable {C D : Type} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D}
variable (K : C ⥤ D) (α : F ⋙ K ≅ K ⋙ G)

def mappedComponentAlgebra (A : Endofunctor.Algebra F) : Endofunctor.Algebra G where
  a := K.obj A.a
  str := α.inv.app A.a ≫ K.map A.str

/-- Constructor compatibility is reflected to an equality after K.
No faithfulness of the individual component functor is required. -/
theorem mapped_hom_condition (A B : Endofunctor.Algebra F) (f : A.a ⟶ B.a) :
    G.map (K.map f) ≫ (mappedComponentAlgebra K α B).str =
      (mappedComponentAlgebra K α A).str ≫ K.map f ↔
      K.map (F.map f ≫ B.str) = K.map (A.str ≫ f) := by
  have hn : G.map (K.map f) ≫ α.inv.app B.a = α.inv.app A.a ≫ K.map (F.map f) := by
    simpa only [Functor.comp_map] using α.inv.naturality f
  change G.map (K.map f) ≫ (α.inv.app B.a ≫ K.map B.str) =
      (α.inv.app A.a ≫ K.map A.str) ≫ K.map f ↔ _
  erw [← Category.assoc,hn,Category.assoc,Category.assoc,← K.map_comp,← K.map_comp,cancel_epi]

def mappedComponentFunctor : Endofunctor.Algebra F ⥤ Endofunctor.Algebra G where
  obj := mappedComponentAlgebra K α
  map f := ⟨K.map f.f,(mapped_hom_condition K α _ _ f.f).mpr (congrArg K.map f.h)⟩
  map_id A := Endofunctor.Algebra.Hom.ext (K.map_id A.a)
  map_comp f g := Endofunctor.Algebra.Hom.ext (K.map_comp f.f g.f)
end AlgebraFunctor

def toComponentAlgebra (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    Endofunctor.Algebra (rules a b).inference ⥤
      Endofunctor.Algebra (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference :=
  mappedComponentFunctor (componentOverFunctor j) (componentComparison a b j)

def componentAlgebra (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :=
  (toComponentAlgebra a b j).obj B

@[simp] theorem componentAlgebra_carrier (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentAlgebra a b B j).a.left = (componentFunctor j).obj B.a.left := rfl

@[simp] theorem componentAlgebra_str (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentAlgebra a b B j).str.left =
      (componentInputIso a b B.a j).inv ≫ (componentFunctor j).map B.str.left := rfl

theorem componentAlgebra_str_left (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentAlgebra a b B j).str.left =
      (componentInputIso a b B.a j).inv ≫ (componentFunctor j).map B.str.left :=
  componentAlgebra_str a b B j

@[simp] theorem toComponentAlgebra_map_left (a b : Idem EffectiveFork.V)
    {A B : Endofunctor.Algebra (rules a b).inference} (f : A ⟶ B) (j : WalkingSpan) :
    ((toComponentAlgebra a b j).map f).f.left = (componentFunctor j).map f.f.left := rfl

private theorem over_eq_iff {F : NumericalTuples.Object} {Q Q' : Over F} (f g : Q ⟶ Q') :
    f = g ↔ f.left = g.left :=
  ⟨congrArg (fun k : Q ⟶ Q' => k.left),Over.OverMorphism.ext⟩

theorem component_hom_condition (a b : Idem EffectiveFork.V)
    (A B : Endofunctor.Algebra (rules a b).inference) (f : A.a ⟶ B.a) (j : WalkingSpan) :
    (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.map (componentOverMap f j) ≫
        (componentAlgebra a b B j).str =
      (componentAlgebra a b A j).str ≫ componentOverMap f j ↔
    (componentFunctor j).map (((rules a b).inference.map f) ≫ B.str).left =
      (componentFunctor j).map (A.str ≫ f).left := by
  exact (mapped_hom_condition (componentOverFunctor j) (componentComparison a b j) A B f).trans
    (over_eq_iff _ _)


def componentTransition {j k : WalkingSpan} (g : j ⟶ k) : componentFunctor j ⟶ componentFunctor k where
  app X := Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g)
  naturality {X Y} f := by
    change Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.map f).app j) ≫
        Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g) =
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫
        Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.map f).app k)
    rw [← Functor.map_comp,← Functor.map_comp]
    exact congrArg Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.map f).naturality g).symm

@[simp] theorem componentTransition_id (j : WalkingSpan) (X : EffectiveFork.Total) :
    (componentTransition (𝟙 j)).app X = 𝟙 ((componentFunctor j).obj X) := by
  change Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map (𝟙 j)) =
    𝟙 (Naturality.unaryFunctor.obj ((EffectiveFork.totalFunctor.obj X).obj j))
  rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]

def spanAtoms : {j k : WalkingSpan} → (j ⟶ k) → ℕ → ℕ
  | _,_,.id _ => id
  | _,_,.init .left => EffectiveFork.leftCoordinate
  | _,_,.init .right => EffectiveFork.rightCoordinate

theorem spanAtoms_computable {j k : WalkingSpan} (g : j ⟶ k) : Computable (spanAtoms g) := by
  cases g with
  | id j => exact Computable.id
  | init i =>
    cases i
    · exact EffectiveFork.leftCoordinate_computable
    · exact EffectiveFork.rightCoordinate_computable

theorem componentSupport_map {j k : WalkingSpan} (g : j ⟶ k) (a : Idem EffectiveFork.V) :
    ∀ x ∈ componentSupport j a, spanAtoms g x ∈ componentSupport k a := by
  cases g with
  | id j => exact fun _ hx => hx
  | init i =>
    cases i
    · exact ForkSyntax.left_axioms a
    · exact ForkSyntax.right_axioms a

theorem component_formula_transition {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app sentenceObject ≫ (componentFormulaIso k).hom =
      (componentFormulaIso j).hom ≫ Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g) := by
  cases g with
  | id j =>
    erw [componentTransition_id j sentenceObject]
    simp only [spanAtoms,Naturality.formulaMap_id,Category.id_comp,Category.comp_id]
  | init i =>
    cases i
    all_goals
      simpa only [componentTransition,componentFormulaIso,EffectiveFork.totalFunctor,
        EffectiveFork.totalDiagram,ForkSyntax.S,sentenceObject,spanAtoms,Functor.comp_map,
        Naturality.unaryFunctor,span,WidePushoutShape.wideSpan,componentFunctor,
        EffectiveFork.totalEquivalence,Functor.comp_obj,Iso.refl_hom,Category.id_comp,Category.comp_id] using
          (Naturality.formulaMap_unary _ _).symm

theorem component_proof_transition (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app (proofObject a b) ≫ (componentProofIso a b k).hom =
      (componentProofIso a b j).hom ≫ Naturality.proofMap
        (componentSupport_re j a) (componentSupport_re j b)
        (componentSupport_re k a) (componentSupport_re k b)
        (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b) := by
  cases g with
  | id j =>
    erw [componentTransition_id j (proofObject a b)]
    simp only [spanAtoms,Naturality.proofMap_id,Category.id_comp,Category.comp_id]
  | init i =>
    cases i
    all_goals
      simpa only [componentTransition,componentProofIso,proofObject,ForkSyntax.Prf,
        componentSupport,componentIdem,EffectiveFork.totalFunctor,EffectiveFork.totalDiagram,
        spanAtoms,Functor.comp_map,Naturality.unaryFunctor,span,WidePushoutShape.wideSpan,
        componentFunctor,EffectiveFork.totalEquivalence,Functor.comp_obj,Iso.refl_hom,
        Category.id_comp,Category.comp_id] using (Naturality.proofMap_unary _ _ _ _ _ _ _ _).symm

/-- The map of target components lies over the actual formula relabeling. -/
theorem componentOver_transition (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app Q.left ≫ (componentOver Q k).hom =
      (componentOver Q j).hom ≫ Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g) := by
  calc
    _ = ((componentTransition g).app Q.left ≫ (componentFunctor k).map Q.hom) ≫
        (componentFormulaIso k).hom := (Category.assoc _ _ _).symm
    _ = ((componentFunctor j).map Q.hom ≫ (componentTransition g).app sentenceObject) ≫
        (componentFormulaIso k).hom :=
      congrArg (fun f => f ≫ (componentFormulaIso k).hom) ((componentTransition g).naturality Q.hom).symm
    _ = _ := by erw [Category.assoc,component_formula_transition,← Category.assoc]


theorem componentPowerIso_transition {j k : WalkingSpan} (g : j ⟶ k) (n : ℕ) :
    (componentTransition g).app (finitePower sentenceObject n) ≫ (componentPowerIso k n).hom =
      (componentPowerIso j n).hom ≫ finitePowerMap
        (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) n := by
  calc
    _ = ((componentTransition g).app (finitePower sentenceObject n) ≫
        (Evaluation.finitePowerIso (K := componentFunctor k) sentenceObject n).hom) ≫
          finitePowerMap (componentFormulaIso k).hom n := by erw [componentPowerIso_hom,← Category.assoc]
    _ = ((Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject n).hom ≫
        finitePowerMap ((componentTransition g).app sentenceObject) n) ≫
          finitePowerMap (componentFormulaIso k).hom n := by
      erw [Evaluation.finitePowerIso_transformation]
    _ = (Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject n).hom ≫
        finitePowerMap ((componentTransition g).app sentenceObject ≫ (componentFormulaIso k).hom) n := by
      erw [Category.assoc,← finitePowerMap_comp]
    _ = (Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject n).hom ≫
        finitePowerMap ((componentFormulaIso j).hom ≫
          Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) n := by
      erw [component_formula_transition]
    _ = _ := by erw [finitePowerMap_comp,← Category.assoc,← componentPowerIso_hom]

def componentRelabelInputIso (a b : Idem EffectiveFork.V) (Q : Over Component.formulaObject)
    (j : WalkingSpan) (i : Fin 3) :
    (componentRebasedRules a b j).ruleObject Q i ≅
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).ruleObject Q i where
  hom := (componentRuleHom a b j).mapRule Q i
  inv := (componentRuleInverse a b j).mapRule Q i
  hom_inv_id := NumericalRuleRelabel.mapRule_inverse (componentRuleHom a b j) (componentRuleInverse a b j)
    (fun i => (componentRuleIso a b j i).hom_inv_id) Q i
  inv_hom_id := NumericalRuleRelabel.mapRule_inverse (componentRuleInverse a b j) (componentRuleHom a b j)
    (fun i => (componentRuleIso a b j i).inv_hom_id) Q i

def componentBranchIso (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) (i : Fin 3) :
    (componentFunctor j).obj ((rules a b).ruleObject Q i) ≅
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).ruleObject (componentOver Q j) i :=
  Evaluation.inputIso (K := componentFunctor j) (rules a b) Q i ≪≫
    NumericalRuleRebase.inputIso (evaluatedRules a b j) (componentFormulaIso j)
      ((Evaluation.overFunctor (K := componentFunctor j) (rules a b)).obj Q) i ≪≫
    componentRelabelInputIso a b (componentOver Q j) j i

@[reassoc] theorem componentBranchIso_fst (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (j : WalkingSpan) (i : Fin 3) :
    (componentBranchIso a b Q j i).hom ≫ pullback.fst _ _ =
      (componentFunctor j).map (pullback.fst ((rules a b).premises i) (finitePowerMap Q.hom i.val)) ≫
        (componentRuleIso a b j i).hom := by
  simp only [componentBranchIso,Iso.trans_hom,componentRelabelInputIso,Category.assoc,
    RulePresentation.Hom.mapRule_fst,componentRuleHom]
  erw [NumericalRuleRebase.input_fst_assoc,Evaluation.inputIso_fst_assoc]

@[reassoc] theorem componentBranchIso_snd (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (j : WalkingSpan) (i : Fin 3) :
    (componentBranchIso a b Q j i).hom ≫ pullback.snd _ _ =
      (componentFunctor j).map (pullback.snd ((rules a b).premises i) (finitePowerMap Q.hom i.val)) ≫
        (Evaluation.finitePowerIso (K := componentFunctor j) Q.left i.val).hom := by
  simp only [componentBranchIso,Iso.trans_hom,componentRelabelInputIso,Category.assoc,
    RulePresentation.Hom.mapRule_snd]
  erw [NumericalRuleRebase.input_snd,Evaluation.inputIso_snd]


end CategoricalEssentialIncompleteness.V46.ForkDerivation
