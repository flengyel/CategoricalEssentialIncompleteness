/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationEvaluation
public import CategoricalEssentialIncompleteness.V46ForkDerivationNaturality
public import CategoricalEssentialIncompleteness.V46NumericalRuleRebase
public import CategoricalEssentialIncompleteness.V46NumericalRuleRelabel
public import Mathlib.Tactic.FinCases
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # The component objects and finite coefficient charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

abbrev componentFunctor (j : WalkingSpan) : EffectiveFork.Total ⥤ NumericalTuples.Object :=
  EffectiveFork.totalEquivalence.functor ⋙
    (evaluation WalkingSpan EnumerableCarriers.Total).obj j ⋙ Naturality.unaryFunctor

instance componentFunctor_preservesFiniteLimits (j : WalkingSpan) :
    PreservesFiniteLimits (componentFunctor j) := by
  dsimp only [componentFunctor]
  infer_instance

instance componentEvaluation_preservesFiniteCoproducts (j : WalkingSpan) :
    PreservesFiniteCoproducts ((evaluation WalkingSpan EnumerableCarriers.Total).obj j) where
  preserves _ := inferInstance

instance componentFunctor_preservesFiniteCoproducts (j : WalkingSpan) :
    PreservesFiniteCoproducts (componentFunctor j) := by
  dsimp only [componentFunctor]
  infer_instance

def componentIdem (j : WalkingSpan) (a : Idem EffectiveFork.V) : Idem EffectiveFork.natCarrier := by
  rcases j with _ | (_ | _)
  · exact EffectiveFork.centerIdem a
  · exact EffectiveFork.leftIdem a
  · exact EffectiveFork.rightIdem a

def componentSupport (j : WalkingSpan) (a : Idem EffectiveFork.V) : Set ℕ :=
  EnumerableCarriers.support (componentIdem j a)

theorem componentSupport_re (j : WalkingSpan) (a : Idem EffectiveFork.V) :
    REPred (· ∈ componentSupport j a) := EnumerableCarriers.support_re _

def componentFormulaIso (j : WalkingSpan) :
    (componentFunctor j).obj sentenceObject ≅ Component.formulaObject := by
  rcases j with _ | (_ | _) <;> exact Iso.refl _

def powerCongr {X Y : NumericalTuples.Object} (e : X ≅ Y) :
    (n : ℕ) → finitePower X n ≅ finitePower Y n
  | 0 => Iso.refl _
  | 1 => e
  | n + 2 => prod.mapIso (powerCongr e (n+1)) e

def componentPowerIso (j : WalkingSpan) (n : ℕ) :
    (componentFunctor j).obj (finitePower sentenceObject n) ≅ finitePower Component.formulaObject n :=
  Evaluation.finitePowerIso (K := componentFunctor j) sentenceObject n ≪≫
    powerCongr (componentFormulaIso j) n

def componentAxiomDomainIso (j : WalkingSpan) (a : Idem EffectiveFork.V) :
    (componentFunctor j).obj (axiomDomain a) ≅
      Component.scalarObject (componentSupport j a) (componentSupport_re j a) := by
  rcases j with _ | (_ | _) <;> exact Iso.refl _

def componentCoefficientIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 5) :
    (componentFunctor j).obj (axiomCoefficients a b i) ≅
      Component.axiomFamily (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) i :=
  Fin.cases (componentPowerIso j 2)
    (Fin.cases (componentPowerIso j 3)
      (Fin.cases (componentPowerIso j 2)
        (Fin.cases (componentAxiomDomainIso j a)
          (Fin.cases (componentAxiomDomainIso j b) (fun i => Fin.elim0 i))))) i

def componentAxiomIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).obj (axiomObject a b) ≅
      Component.axiomObject (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) :=
  (asIso (sigmaComparison (componentFunctor j) (axiomCoefficients a b))).symm ≪≫
    Sigma.mapIso (componentCoefficientIso a b j)

def evaluatedRules (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    RulePresentation ((componentFunctor j).obj sentenceObject) 2 :=
  Evaluation.interpretedRules (K := componentFunctor j) (rules a b)

def componentRebasedRules (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    RulePresentation Component.formulaObject 2 :=
  NumericalRuleRebase.rules (evaluatedRules a b j) (componentFormulaIso j)

def componentRuleIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRebasedRules a b j).instances i ≅
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).instances i :=
  Fin.cases (componentAxiomIso a b j)
    (Fin.cases (asIso (initialComparison (componentFunctor j))).symm
      (Fin.cases (componentPowerIso j 2) (fun i => Fin.elim0 i))) i

def componentProofIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).obj (proofObject a b) ≅
      Component.proofObject (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) := by
  rcases j with _ | (_ | _) <;> exact Iso.refl _

theorem component_conclusion (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (conclusion a b) ≫ (componentFormulaIso j).hom =
      (componentProofIso a b j).hom ≫
        Component.conclusion (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b) := by
  rcases j with _ | (_ | _)
  all_goals
    change Naturality.unaryMap (⟨ForkSyntax.conclusionArrow _ _ _ _,_⟩) =
      Component.conclusion _ _ _ _
    exact (Naturality.conclusion_unary _ _ _ _).symm

@[simp] theorem componentFormulaIso_value (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj sentenceObject)) :
    ((componentFormulaIso j).hom.toFun x).val = x.val := by
  rcases j with _ | (_ | _) <;> rfl

@[reassoc] theorem componentPowerIso_fst (j : WalkingSpan) :
    (componentPowerIso j 2).hom ≫ prod.fst =
      (componentFunctor j).map (prod.fst : sentenceObject ⨯ sentenceObject ⟶ sentenceObject) ≫
        (componentFormulaIso j).hom := by
  simp [componentPowerIso,Evaluation.finitePowerIso,powerCongr,Category.assoc]
  erw [prodComparison_fst_assoc]
  all_goals rfl

@[reassoc] theorem componentPowerIso_snd (j : WalkingSpan) :
    (componentPowerIso j 2).hom ≫ prod.snd =
      (componentFunctor j).map (prod.snd : sentenceObject ⨯ sentenceObject ⟶ sentenceObject) ≫
        (componentFormulaIso j).hom := by
  simp [componentPowerIso,Evaluation.finitePowerIso,powerCongr,Category.assoc]
  erw [prodComparison_snd_assoc]
  all_goals rfl

@[reassoc] theorem componentTripleIso_fst (j : WalkingSpan) :
    (componentPowerIso j 3).hom ≫ prod.fst =
      (componentFunctor j).map (prod.fst :
        (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject ⟶ sentenceObject ⨯ sentenceObject) ≫
        (componentPowerIso j 2).hom := by
  simp [componentPowerIso,Evaluation.finitePowerIso,powerCongr,Category.assoc,prod.map_map]
  erw [prodComparison_fst_assoc]
  all_goals rfl

@[reassoc] theorem componentTripleIso_snd (j : WalkingSpan) :
    (componentPowerIso j 3).hom ≫ prod.snd =
      (componentFunctor j).map (prod.snd :
        (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject ⟶ sentenceObject) ≫
        (componentFormulaIso j).hom := by
  simp [componentPowerIso,Evaluation.finitePowerIso,powerCongr,Category.assoc,prod.map_map]
  erw [prodComparison_snd_assoc]
  all_goals rfl

@[simp] theorem componentProofIso_value (a b : Idem EffectiveFork.V) (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj (proofObject a b))) :
    ((componentProofIso a b j).hom.toFun x).val = x.val := by
  rcases j with _ | (_ | _) <;> rfl

/-- The compatible unary components give a natural transformation. -/
def componentNatural {X Y : EffectiveFork.Total}
    (f : ∀ j, (componentFunctor j).obj X ⟶ (componentFunctor j).obj Y)
    (hn : ∀ ⦃j k : WalkingSpan⦄ (g : j ⟶ k),
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫ f k =
        f j ≫ Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g)) :
    EffectiveFork.totalEquivalence.functor.obj X ⟶ EffectiveFork.totalEquivalence.functor.obj Y where
  app j := Naturality.unaryFunctor.preimage (f j)
  naturality {j k} g := by
    apply Naturality.unaryFunctor.map_injective
    erw [Functor.map_comp,Functor.map_comp,Functor.map_preimage,Functor.map_preimage]
    exact hn g

/-- A compatible family is recovered through the explicit unary presentation. -/
def fromComponents {X Y : EffectiveFork.Total}
    (f : ∀ j, (componentFunctor j).obj X ⟶ (componentFunctor j).obj Y)
    (hn : ∀ ⦃j k : WalkingSpan⦄ (g : j ⟶ k),
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫ f k =
        f j ≫ Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g)) : X ⟶ Y :=
  EffectiveFork.totalEquivalence.functor.preimage (componentNatural f hn)

@[simp] theorem component_fromComponents {X Y : EffectiveFork.Total}
    (f : ∀ j, (componentFunctor j).obj X ⟶ (componentFunctor j).obj Y)
    (hn : ∀ ⦃j k : WalkingSpan⦄ (g : j ⟶ k),
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫ f k =
        f j ≫ Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g))
    (j : WalkingSpan) : (componentFunctor j).map (fromComponents f hn) = f j := by
  have h := congrArg (fun n => Naturality.unaryFunctor.map (n.app j))
    (EffectiveFork.totalEquivalence.functor.map_preimage (componentNatural f hn))
  exact h.trans (Naturality.unaryFunctor.map_preimage (f j))

theorem component_jointly_faithful {X Y : EffectiveFork.Total} (f g : X ⟶ Y)
    (h : ∀ j, (componentFunctor j).map f = (componentFunctor j).map g) : f = g := by
  apply EffectiveFork.totalEquivalence.functor.map_injective
  apply NatTrans.ext
  funext j
  exact Naturality.unaryFunctor.map_injective (h j)

theorem fromComponents_unique {X Y : EffectiveFork.Total}
    (f : ∀ j, (componentFunctor j).obj X ⟶ (componentFunctor j).obj Y)
    (hn : ∀ ⦃j k : WalkingSpan⦄ (g : j ⟶ k),
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫ f k =
        f j ≫ Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g))
    (u : X ⟶ Y) (hu : ∀ j, (componentFunctor j).map u = f j) : u = fromComponents f hn := by
  apply component_jointly_faithful
  intro j
  erw [component_fromComponents]
  exact hu j

/-- Component maps retain their old partial-program graph. -/
theorem component_map_mem {X Y : EffectiveFork.Total} (j : WalkingSpan) (f : X ⟶ Y)
    (x : NumericalTuples.Point ((componentFunctor j).obj X)) :
    (((componentFunctor j).map f).toFun x).val ∈
      EnumerableCarriers.val ((EffectiveFork.totalFunctor.map f).app j).hom x.val :=
  EnumerableCarriers.totalFunction_mem _ x

def componentVariableIso (j : WalkingSpan) :
    (componentFunctor j).obj variableObject ≅ Component.formulaObject := by
  rcases j with _ | (_ | _) <;> exact Iso.refl _

def nativeAtom : Component.formulaObject ⟶ Component.formulaObject :=
  Component.scalarMap (REPred.const True) (REPred.const True) ForkSyntax.atomCode
    ForkSyntax.atomCode_computable (fun _ _ => Set.mem_univ _)

def nativeNegation : Component.formulaObject ⟶ Component.formulaObject :=
  Component.scalarMap (REPred.const True) (REPred.const True) ForkSyntax.negCode
    ForkSyntax.negCode_computable (fun _ _ => Set.mem_univ _)

def nativeInclusion (C : Set ℕ) (hC : REPred (· ∈ C)) :
    Component.scalarObject C hC ⟶ Component.formulaObject :=
  Component.scalarMap hC (REPred.const True) id Computable.id (fun _ _ => Set.mem_univ _)

private theorem component_atom_value (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj variableObject)) :
    (((componentFunctor j).map atom).toFun x).val = ForkSyntax.atomCode x.val := by
  have h := component_map_mem j atom x
  rcases j with _ | (_ | _)
  all_goals exact ((EnumerableCarriers.mem_totalFromFunction
    (X := EffectiveFork.natCarrier) (Y := EffectiveFork.natCarrier)
    ForkSyntax.atomCode ForkSyntax.atomCode_computable
    (fun n _ => Set.mem_univ (ForkSyntax.atomCode n)) x.val _).mp h).2

private theorem component_negation_value (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj sentenceObject)) :
    (((componentFunctor j).map negation).toFun x).val = ForkSyntax.negCode x.val := by
  have h := component_map_mem j negation x
  rcases j with _ | (_ | _)
  all_goals exact ((EnumerableCarriers.mem_totalFromFunction
    (X := EffectiveFork.natCarrier) (Y := EffectiveFork.natCarrier)
    ForkSyntax.negCode ForkSyntax.negCode_computable
    (fun n _ => Set.mem_univ (ForkSyntax.negCode n)) x.val _).mp h).2

theorem component_atom (j : WalkingSpan) :
    (componentFunctor j).map atom ≫ (componentFormulaIso j).hom =
      (componentVariableIso j).hom ≫ nativeAtom := by
  rcases j with _ | (_ | _)
  all_goals
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    exact component_atom_value _ x

theorem component_negation (j : WalkingSpan) :
    (componentFunctor j).map negation ≫ (componentFormulaIso j).hom =
      (componentFormulaIso j).hom ≫ nativeNegation := by
  rcases j with _ | (_ | _)
  all_goals
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    exact component_negation_value _ x

private theorem component_inclusion_value (j : WalkingSpan) (a : Idem EffectiveFork.V)
    (x : NumericalTuples.Point ((componentFunctor j).obj (axiomDomain a))) :
    (((componentFunctor j).map (axiomInclusion a)).toFun x).val = x.val := by
  have h := component_map_mem j (axiomInclusion a) x
  rcases j with _ | (_ | _)
  all_goals
    change _ ∈ EnumerableCarriers.val (EnumerableCarriers.into _) x.val at h
    rw [EnumerableCarriers.into,EnumerableCarriers.val_arrow] at h
    exact ((EnumerableCarriers.mem_val_idem _ _ _).mp h).2

theorem component_axiomInclusion (j : WalkingSpan) (a : Idem EffectiveFork.V) :
    (componentFunctor j).map (axiomInclusion a) ≫ (componentVariableIso j).hom =
      (componentAxiomDomainIso j a).hom ≫ nativeInclusion (componentSupport j a) (componentSupport_re j a) := by
  rcases j with _ | (_ | _)
  all_goals
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    exact component_inclusion_value _ a x

private theorem component_codedFst_value (j : WalkingSpan) (X Y : EffectiveFork.Total)
    (x : NumericalTuples.Point ((componentFunctor j).obj (codedProduct X Y))) :
    (((componentFunctor j).map (codedFst X Y)).toFun x).val = (Nat.unpair x.val).1 := by
  have h := component_map_mem j (codedFst X Y) x
  rcases j with _ | (_ | _)
  all_goals exact ((EnumerableCarriers.mem_partialFst _ _ x.val _).mp h).2.symm

private theorem component_codedSnd_value (j : WalkingSpan) (X Y : EffectiveFork.Total)
    (x : NumericalTuples.Point ((componentFunctor j).obj (codedProduct X Y))) :
    (((componentFunctor j).map (codedSnd X Y)).toFun x).val = (Nat.unpair x.val).2 := by
  have h := component_map_mem j (codedSnd X Y) x
  rcases j with _ | (_ | _)
  all_goals exact ((EnumerableCarriers.mem_partialSnd _ _ x.val _).mp h).2.symm

def codedImplication : codedProduct sentenceObject sentenceObject ⟶ sentenceObject :=
  ⟨ForkSyntax.implication,ForkSyntax.implication_total⟩

private theorem component_codedImplication_value (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj (codedProduct sentenceObject sentenceObject))) :
    (((componentFunctor j).map codedImplication).toFun x).val = ForkSyntax.impCode x.val := by
  have h := component_map_mem j codedImplication x
  rcases j with _ | (_ | _)
  all_goals exact ((EnumerableCarriers.mem_totalFromFunction
    (X := EnumerableCarriers.product EffectiveFork.natCarrier EffectiveFork.natCarrier)
    (Y := EffectiveFork.natCarrier) ForkSyntax.impCode ForkSyntax.impCode_computable
    (fun n _ => Set.mem_univ (ForkSyntax.impCode n)) x.val _).mp h).2

private theorem component_pair_first_code (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj (sentenceObject ⨯ sentenceObject))) :
    (Component.firstPoint ((componentPowerIso j 2).hom.toFun x)).val =
      (Nat.unpair (((componentFunctor j).map (productComparison sentenceObject sentenceObject).hom).toFun x).val).1 := by
  have hn := congrArg (fun f => (f.toFun x).val) (componentPowerIso_fst j)
  have hs := congrArg (fun f => (f.toFun x).val)
    (((componentFunctor j).map_comp (productComparison sentenceObject sentenceObject).hom
      (codedFst sentenceObject sentenceObject)).symm.trans
        (congrArg (componentFunctor j).map (productComparison_fst sentenceObject sentenceObject)))
  exact hn.trans ((componentFormulaIso_value j _).trans
    (hs.symm.trans (component_codedFst_value j sentenceObject sentenceObject _)))

private theorem component_pair_second_code (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj (sentenceObject ⨯ sentenceObject))) :
    (Component.secondPoint ((componentPowerIso j 2).hom.toFun x)).val =
      (Nat.unpair (((componentFunctor j).map (productComparison sentenceObject sentenceObject).hom).toFun x).val).2 := by
  have hn := congrArg (fun f => (f.toFun x).val) (componentPowerIso_snd j)
  have hs := congrArg (fun f => (f.toFun x).val)
    (((componentFunctor j).map_comp (productComparison sentenceObject sentenceObject).hom
      (codedSnd sentenceObject sentenceObject)).symm.trans
        (congrArg (componentFunctor j).map (productComparison_snd sentenceObject sentenceObject)))
  exact hn.trans ((componentFormulaIso_value j _).trans
    (hs.symm.trans (component_codedSnd_value j sentenceObject sentenceObject _)))

/-- The chosen product chart computes the original ordered pair of
formula codes before the implication constructor is applied. -/
theorem component_implication (j : WalkingSpan) :
    (componentFunctor j).map implication ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 2).hom ≫ Component.implication := by
  rcases j with _ | (_ | _)
  all_goals
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    have hm := congrArg (fun f => (f.toFun x).val)
      ((componentFunctor _).map_comp (productComparison sentenceObject sentenceObject).hom codedImplication)
    have hv := Component.implication_value ((componentPowerIso _ 2).hom.toFun x)
    have hp := component_pair_first_code _ x
    have hq := component_pair_second_code _ x
    have hc : ((((componentFunctor _).map implication).toFun x).val : ℕ) =
        ForkSyntax.impCode (((componentFunctor _).map (productComparison sentenceObject sentenceObject).hom).toFun x).val :=
      hm.trans (component_codedImplication_value _ _)
    have he : (((componentFormulaIso _).hom.toFun
        (((componentFunctor _).map implication).toFun x)).val : ℕ) =
          ((((componentFunctor _).map implication).toFun x).val : ℕ) :=
      componentFormulaIso_value _ _
    have hn : ForkSyntax.impCode
        (((componentFunctor _).map (productComparison sentenceObject sentenceObject).hom).toFun x).val =
          (Component.implication.toFun ((componentPowerIso _ 2).hom.toFun x)).val := by
      simpa only [ForkSyntax.impCode,ForkSyntax.Formula.encode,Component.formulaAt,
        ForkSyntax.Formula.encode_decode,hp,hq,Nat.pair_unpair] using hv.symm
    have ht := he.trans (hc.trans hn)
    exact ht


theorem component_pair {X : EffectiveFork.Total} (j : WalkingSpan) (f g : X ⟶ sentenceObject) :
    (componentFunctor j).map (prod.lift f g) ≫ (componentPowerIso j 2).hom =
      prod.lift ((componentFunctor j).map f ≫ (componentFormulaIso j).hom)
        ((componentFunctor j).map g ≫ (componentFormulaIso j).hom) := by
  apply prod.hom_ext
  · simp only [Category.assoc,componentPowerIso_fst,← Functor.map_comp_assoc,prod.lift_fst]
  · simp only [Category.assoc,componentPowerIso_snd,← Functor.map_comp_assoc]
    exact (congrArg (fun h : X ⟶ sentenceObject => (componentFunctor j).map h ≫
        (componentFormulaIso j).hom) (prod.lift_snd f g)).trans
      (prod.lift_snd ((componentFunctor j).map f ≫ (componentFormulaIso j).hom)
        ((componentFunctor j).map g ≫ (componentFormulaIso j).hom)).symm

theorem component_pair_implication {X : EffectiveFork.Total} (j : WalkingSpan)
    (f g : X ⟶ sentenceObject) :
    (componentFunctor j).map (prod.lift f g ≫ implication) ≫ (componentFormulaIso j).hom =
      prod.lift ((componentFunctor j).map f ≫ (componentFormulaIso j).hom)
        ((componentFunctor j).map g ≫ (componentFormulaIso j).hom) ≫ Component.implication := by
  rw [Functor.map_comp,Category.assoc,component_implication,← Category.assoc,component_pair]

theorem component_composed_negation {X : EffectiveFork.Total} (j : WalkingSpan) (f : X ⟶ sentenceObject) :
    (componentFunctor j).map (f ≫ negation) ≫ (componentFormulaIso j).hom =
      ((componentFunctor j).map f ≫ (componentFormulaIso j).hom) ≫ nativeNegation := by
  rw [Functor.map_comp,Category.assoc,component_negation,← Category.assoc]

def nativeH1 : Component.formulaObject ⨯ Component.formulaObject ⟶ Component.formulaObject :=
  prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ Component.implication) ≫ Component.implication

def nativeH2 : (Component.formulaObject ⨯ Component.formulaObject) ⨯ Component.formulaObject ⟶
    Component.formulaObject :=
  prod.lift
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ Component.implication) ≫ Component.implication)
    (prod.lift
      (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) ≫ Component.implication)
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ Component.implication) ≫ Component.implication) ≫
    Component.implication

def nativeH3 : Component.formulaObject ⨯ Component.formulaObject ⟶ Component.formulaObject :=
  prod.lift (prod.lift (prod.snd ≫ nativeNegation) (prod.fst ≫ nativeNegation) ≫ Component.implication)
    (prod.lift prod.fst prod.snd ≫ Component.implication) ≫ Component.implication

@[simp] theorem point_lift_fst {X Y Z : NumericalTuples.Object} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : NumericalTuples.Point X) : Component.firstPoint ((prod.lift f g).toFun x) = f.toFun x :=
  congrArg (fun k => k.toFun x) (prod.lift_fst f g)

@[simp] theorem point_lift_snd {X Y Z : NumericalTuples.Object} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : NumericalTuples.Point X) : Component.secondPoint ((prod.lift f g).toFun x) = g.toFun x :=
  congrArg (fun k => k.toFun x) (prod.lift_snd f g)

@[simp] theorem native_implication_formula (x : NumericalTuples.Point (Component.formulaObject ⨯ Component.formulaObject)) :
    Component.formulaAt (Component.implication.toFun x) =
      .imp (Component.formulaAt (Component.firstPoint x)) (Component.formulaAt (Component.secondPoint x)) := by
  change ForkSyntax.Formula.decode _ = _
  rw [Component.implication_value,ForkSyntax.Formula.decode_encode]

@[simp] theorem native_negation_formula (x : NumericalTuples.Point Component.formulaObject) :
    Component.formulaAt (nativeNegation.toFun x) = .neg (Component.formulaAt x) := by
  simpa only [nativeNegation,Component.scalarMap,Component.formulaAt,ForkSyntax.negCode,
    ForkSyntax.Formula.encode,ForkSyntax.Formula.encode_decode] using
      ForkSyntax.Formula.decode_encode (.neg (ForkSyntax.Formula.decode x.val))


end CategoricalEssentialIncompleteness.V46.ForkDerivation
