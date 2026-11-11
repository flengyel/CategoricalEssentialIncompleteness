/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionAlgebra
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionRoots
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInputGeometry
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationPullbackPowers
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessAdjunction
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSliceInitial
public import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables

/-! The validator success functor is the original dependent rule functor. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : PredicateCategory T} {N : ℕ}
  (R : RulePresentation F N)

def equality (_R : RulePresentation F N) (i : Fin (N + 1)) : DecidableVariables (finitePower F i.val) :=
  SyntacticDecidableVariables.decidableVariables T _

abbrev validator : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  OptionAlgebra.validator R (equality T R)

abbrev success : Over (OptionSyntax.obj F) ⥤ Over F :=
  Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)

def inputComponent (X : Over (OptionSyntax.obj F)) (i : Fin (N + 1)) :
    R.ruleObject ((success T).obj X) i ⟶ R.instances i ⨯ finitePower X.left i.val :=
  CheckedRoot.matchingMap R ((success T).obj X) i ≫
    prod.map (𝟙 _) (finitePowerMap (pullback.fst X.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F)) i.val)

theorem rootComponent_isPullback (i : Fin (N + 1)) :
    IsPullback
      (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i ≫
        prod.map (𝟙 _) (finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val))
      (R.ruleConclusion (Over.mk (𝟙 F)) i)
      (OptionAlgebra.component R (equality T R) (Over.mk (𝟙 F)) i
        (R.ruleConclusion (Over.mk (𝟙 F)) i)) coprod.inr := by
  let m := CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i
  let h := R.ruleConclusion (Over.mk (𝟙 F)) i
  let g := CheckedRoot.operation R (Over.mk (𝟙 F)) i (equality T R i) h
  have hc := PullbackPowers.fixedProduct (R.instances i) (OptionPullbacks.collect T F i.val)
  simp only [prod.map_id_id] at hc
  have hi := (IsPullback.id_vert m).paste_horiz hc
  have hl := OptionRoots.predicate T g m h
    (CheckedRoot.operation_isPullback R (Over.mk (𝟙 F)) i (equality T R i) h)
  simpa only [Category.id_comp, OptionAlgebra.component, m, h, g, Over.mk_left] using hi.paste_vert hl

theorem component_isPullback (X : Over (OptionSyntax.obj F)) (i : Fin (N + 1)) :
    IsPullback (inputComponent T R X i) (R.ruleConclusion ((success T).obj X) i)
      (prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
        OptionAlgebra.component R (equality T R) (Over.mk (𝟙 F)) i
          (R.ruleConclusion (Over.mk (𝟙 F)) i)) coprod.inr := by
  have hm := InputGeometry.matching_isPullback R ((success T).obj X) i
  have hp := PullbackPowers.fixedProduct (R.instances i)
    (PullbackPowers.power (IsPullback.of_hasPullback X.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F)) i.val)
  have hh := (hm.paste_horiz hp).paste_vert (rootComponent_isPullback T R i)
  have hq : R.ruleMap (InputGeometry.toJudgement ((success T).obj X)) i ≫
      R.ruleConclusion (Over.mk (𝟙 F)) i = R.ruleConclusion ((success T).obj X) i := by
    have he := congrArg (fun k => k ≫ R.conclusion i)
      (R.ruleMap_fst (InputGeometry.toJudgement ((success T).obj X)) i)
    simpa only [RulePresentation.ruleConclusion, Category.assoc] using he
  simpa only [inputComponent, hq] using hh

def input (X : Over (OptionSyntax.obj F)) :
    (R.inference.obj ((success T).obj X)).left ⟶ (PolynomialComparison.ordinary R).obj X.left :=
  Sigma.desc (fun i => inputComponent T R X i ≫
    Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower X.left i.val) i)

theorem input_eq_forget (X : Over (OptionSyntax.obj F)) :
    input T R X = InputGeometry.forget R ((success T).obj X) ≫
      (PolynomialComparison.ordinary R).map
        (pullback.fst X.hom (coprod.inr : F ⟶ OptionSyntax.obj F)) := by
  apply Sigma.hom_ext
  intro i
  simp [input, InputGeometry.forget, PolynomialComparison.ordinary, inputComponent,
    Category.assoc]

theorem input_isPullback (X : Over (OptionSyntax.obj F)) :
    IsPullback (input T R X) (R.inference.obj ((success T).obj X)).hom
      ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).obj X).hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  have h := PullbackPowers.finiteSum (inputComponent T R X)
    (R.ruleConclusion ((success T).obj X))
    (fun i => prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
      OptionAlgebra.component R (equality T R) (Over.mk (𝟙 F)) i
        (R.ruleConclusion (Over.mk (𝟙 F)) i))
    (coprod.inr : F ⟶ OptionSyntax.obj F) (component_isPullback T R X)
  have he : ((SliceInitial.functor (PolynomialComparison.ordinary R)
      (validator T R)).obj X).hom =
      Sigma.desc (fun i => prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
        OptionAlgebra.component R (equality T R) (Over.mk (𝟙 F)) i
          (R.ruleConclusion (Over.mk (𝟙 F)) i)) := by
    apply Sigma.hom_ext
    intro i
    simp [SliceInitial.functor, PolynomialComparison.ordinary, validator, OptionAlgebra.validator]
  rw [he]
  exact h

def componentIso (X : Over (OptionSyntax.obj F)) :
    R.inference.obj ((success T).obj X) ≅
      (success T).obj ((SliceInitial.functor (PolynomialComparison.ordinary R)
        (validator T R)).obj X) :=
  Over.isoMk (input_isPullback T R X).isoPullback (by simp)

@[simp, reassoc] theorem componentIso_input (X : Over (OptionSyntax.obj F)) :
    (componentIso T R X).hom.left ≫ pullback.fst
      ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).obj X).hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) = input T R X := by
  simp [componentIso]

theorem inputComponent_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y)
    (i : Fin (N + 1)) :
    R.ruleMap ((success T).map f) i ≫ inputComponent T R Y i =
      inputComponent T R X i ≫ prod.map (𝟙 _) (finitePowerMap f.left i.val) := by
  have hbase : ((success T).map f).left ≫ pullback.fst Y.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) =
    pullback.fst X.hom (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ f.left := by
    simp [Over.pullback]
  have hm : R.ruleMap ((success T).map f) i ≫
      CheckedRoot.matchingMap R ((success T).obj Y) i =
      CheckedRoot.matchingMap R ((success T).obj X) i ≫
        prod.map (𝟙 _) (finitePowerMap ((success T).map f).left i.val) := by
    apply prod.hom_ext <;> simp [CheckedRoot.matchingMap, RulePresentation.ruleMap]
  unfold inputComponent
  rw [← Category.assoc, hm, Category.assoc, prod.map_map, Category.comp_id,
    ← finitePowerMap_comp, hbase, finitePowerMap_comp]
  rw [Category.assoc, prod.map_map, Category.comp_id]

theorem input_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y) :
    (R.inference.map ((success T).map f)).left ≫ input T R Y =
      input T R X ≫ (PolynomialComparison.ordinary R).map f.left := by
  apply Sigma.hom_ext
  intro i
  simp only [RulePresentation.inference, Over.homMk_left, Sigma.ι_map_assoc,
    input, Sigma.ι_comp_desc_assoc, PolynomialComparison.ordinary]
  simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_map]
  rw [← Category.assoc, inputComponent_natural, Category.assoc]

theorem componentIso_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y) :
    R.inference.map ((success T).map f) ≫ (componentIso T R Y).hom =
      (componentIso T R X).hom ≫ (success T).map
        ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).map f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hp : ((success T).map
          ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).map f)).left ≫
        pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).obj Y).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) =
      pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R)).obj X).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (PolynomialComparison.ordinary R).map f.left := by
      simp [Over.pullback, SliceInitial.functor]
    simp only [Over.comp_left, Category.assoc]
    rw [componentIso_input, hp, ← Category.assoc, componentIso_input]
    exact input_natural T R f
  · exact (Over.w _).trans (Over.w _).symm

def comparison :
    SliceInitial.functor (PolynomialComparison.ordinary R) (validator T R) ⋙ success T ≅
      success T ⋙ R.inference :=
  (NatIso.ofComponents (componentIso T R) (fun f => componentIso_natural T R f)).symm

@[simp] theorem comparison_inv_app (X : Over (OptionSyntax.obj F)) :
    (comparison T R).inv.app X = (componentIso T R X).hom := rfl

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessComparison
