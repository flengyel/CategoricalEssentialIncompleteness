import CategoricalEssentialIncompleteness.V46SyntacticDerivationModelPullbacks
import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionAlgebra
import CategoricalEssentialIncompleteness.V46SyntacticDerivationInputGeometry
import CategoricalEssentialIncompleteness.V46SyntacticDerivationPullbackPowers
import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessAdjunction
import CategoricalEssentialIncompleteness.V46SyntacticDerivationSliceInitial

/-! The success comparison for a concrete conservative interpretation family.
No validation, evaluation, or initiality conclusion is an input field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessComparisonCore
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {J : Type w} (K : D ⥤ (Discrete J ⥤ Type)) [K.ReflectsIsomorphisms]
  [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K]
  {F : D} {N : ℕ} (R : RulePresentation F N)
  (E : ∀ i : Fin (N + 1), DecidableVariables (finitePower F i.val))

abbrev validator : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  OptionAlgebra.validator R E

abbrev success : Over (OptionSyntax.obj F) ⥤ Over F :=
  Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)

def inputComponent (X : Over (OptionSyntax.obj F)) (i : Fin (N + 1)) :
    R.ruleObject ((success (F := F)).obj X) i ⟶ R.instances i ⨯ finitePower X.left i.val :=
  CheckedRoot.matchingMap R ((success (F := F)).obj X) i ≫
    prod.map (𝟙 _) (finitePowerMap (pullback.fst X.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F)) i.val)

include K in
theorem rootComponent_isPullback (i : Fin (N + 1)) :
    IsPullback
      (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i ≫
        prod.map (𝟙 _) (finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val))
      (R.ruleConclusion (Over.mk (𝟙 F)) i)
      (OptionAlgebra.component R E (Over.mk (𝟙 F)) i
        (R.ruleConclusion (Over.mk (𝟙 F)) i)) coprod.inr := by
  let m := CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i
  let h := R.ruleConclusion (Over.mk (𝟙 F)) i
  let g := CheckedRoot.operation R (Over.mk (𝟙 F)) i (E i) h
  have hc := PullbackPowers.fixedProduct (R.instances i) (ModelPullbacks.collect K F i.val)
  simp only [prod.map_id_id] at hc
  have hi := (IsPullback.id_vert m).paste_horiz hc
  have hl := ModelPullbacks.liftRoot K g m h
    (CheckedRoot.operation_isPullback R (Over.mk (𝟙 F)) i (E i) h)
  simpa only [Category.id_comp, OptionAlgebra.component, m, h, g, Over.mk_left] using hi.paste_vert hl

include K in
theorem component_isPullback (X : Over (OptionSyntax.obj F)) (i : Fin (N + 1)) :
    IsPullback (inputComponent R X i) (R.ruleConclusion ((success (F := F)).obj X) i)
      (prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
        OptionAlgebra.component R E (Over.mk (𝟙 F)) i
          (R.ruleConclusion (Over.mk (𝟙 F)) i)) coprod.inr := by
  have hm := InputGeometry.matching_isPullback R ((success (F := F)).obj X) i
  have hp := PullbackPowers.fixedProduct (R.instances i)
    (PullbackPowers.power (IsPullback.of_hasPullback X.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F)) i.val)
  have hh := (hm.paste_horiz hp).paste_vert (rootComponent_isPullback K R E i)
  have hq : R.ruleMap (InputGeometry.toJudgement ((success (F := F)).obj X)) i ≫
      R.ruleConclusion (Over.mk (𝟙 F)) i = R.ruleConclusion ((success (F := F)).obj X) i := by
    have he := congrArg (fun k => k ≫ R.conclusion i)
      (R.ruleMap_fst (InputGeometry.toJudgement ((success (F := F)).obj X)) i)
    simpa only [RulePresentation.ruleConclusion, Category.assoc] using he
  simpa only [inputComponent, hq] using hh

def input (X : Over (OptionSyntax.obj F)) :
    (R.inference.obj ((success (F := F)).obj X)).left ⟶ (PolynomialComparison.ordinary R).obj X.left :=
  Sigma.desc (fun i => inputComponent R X i ≫
    Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower X.left i.val) i)

theorem input_eq_forget (X : Over (OptionSyntax.obj F)) :
    input R X = InputGeometry.forget R ((success (F := F)).obj X) ≫
      (PolynomialComparison.ordinary R).map
        (pullback.fst X.hom (coprod.inr : F ⟶ OptionSyntax.obj F)) := by
  apply Sigma.hom_ext
  intro i
  simp [input, InputGeometry.forget, PolynomialComparison.ordinary, inputComponent,
    Category.assoc]

include K in
theorem input_isPullback (X : Over (OptionSyntax.obj F)) :
    IsPullback (input R X) (R.inference.obj ((success (F := F)).obj X)).hom
      ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).obj X).hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  have h := PullbackPowers.finiteSum (inputComponent R X)
    (R.ruleConclusion ((success (F := F)).obj X))
    (fun i => prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
      OptionAlgebra.component R E (Over.mk (𝟙 F)) i
        (R.ruleConclusion (Over.mk (𝟙 F)) i))
    (coprod.inr : F ⟶ OptionSyntax.obj F) (component_isPullback K R E X)
  have he : ((SliceInitial.functor (PolynomialComparison.ordinary R)
      (validator R E)).obj X).hom =
      Sigma.desc (fun i => prod.map (𝟙 _) (finitePowerMap X.hom i.val) ≫
        OptionAlgebra.component R E (Over.mk (𝟙 F)) i
          (R.ruleConclusion (Over.mk (𝟙 F)) i)) := by
    apply Sigma.hom_ext
    intro i
    simp [SliceInitial.functor, PolynomialComparison.ordinary, validator, OptionAlgebra.validator]
  rw [he]
  exact h

def componentIso (X : Over (OptionSyntax.obj F)) :
    R.inference.obj ((success (F := F)).obj X) ≅
      (success (F := F)).obj ((SliceInitial.functor (PolynomialComparison.ordinary R)
        (validator R E)).obj X) :=
  Over.isoMk (input_isPullback K R E X).isoPullback (by simp)

@[simp, reassoc] theorem componentIso_input (X : Over (OptionSyntax.obj F)) :
    (componentIso K R E X).hom.left ≫ pullback.fst
      ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).obj X).hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) = input R X := by
  simp [componentIso]

theorem inputComponent_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y)
    (i : Fin (N + 1)) :
    R.ruleMap ((success (F := F)).map f) i ≫ inputComponent R Y i =
      inputComponent R X i ≫ prod.map (𝟙 _) (finitePowerMap f.left i.val) := by
  have hbase : ((success (F := F)).map f).left ≫ pullback.fst Y.hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) =
    pullback.fst X.hom (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ f.left := by
    simp [Over.pullback]
  have hm : R.ruleMap ((success (F := F)).map f) i ≫
      CheckedRoot.matchingMap R ((success (F := F)).obj Y) i =
      CheckedRoot.matchingMap R ((success (F := F)).obj X) i ≫
        prod.map (𝟙 _) (finitePowerMap ((success (F := F)).map f).left i.val) := by
    apply prod.hom_ext <;> simp [CheckedRoot.matchingMap, RulePresentation.ruleMap]
  unfold inputComponent
  rw [← Category.assoc, hm, Category.assoc, prod.map_map, Category.comp_id,
    ← finitePowerMap_comp, hbase, finitePowerMap_comp]
  rw [Category.assoc, prod.map_map, Category.comp_id]

theorem input_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y) :
    (R.inference.map ((success (F := F)).map f)).left ≫ input R Y =
      input R X ≫ (PolynomialComparison.ordinary R).map f.left := by
  apply Sigma.hom_ext
  intro i
  simp only [RulePresentation.inference, Over.homMk_left, Sigma.ι_map_assoc,
    input, Sigma.ι_comp_desc_assoc, PolynomialComparison.ordinary]
  simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_map]
  rw [← Category.assoc, inputComponent_natural, Category.assoc]

theorem componentIso_natural {X Y : Over (OptionSyntax.obj F)} (f : X ⟶ Y) :
    R.inference.map ((success (F := F)).map f) ≫ (componentIso K R E Y).hom =
      (componentIso K R E X).hom ≫ (success (F := F)).map
        ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).map f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hp : ((success (F := F)).map
          ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).map f)).left ≫
        pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).obj Y).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) =
      pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E)).obj X).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (PolynomialComparison.ordinary R).map f.left := by
      simp [Over.pullback, SliceInitial.functor]
    simp only [Over.comp_left, Category.assoc]
    rw [componentIso_input, hp, ← Category.assoc, componentIso_input]
    exact input_natural R f
  · exact (Over.w _).trans (Over.w _).symm

def comparison :
    SliceInitial.functor (PolynomialComparison.ordinary R) (validator R E) ⋙ success (F := F) ≅
      success (F := F) ⋙ R.inference :=
  (NatIso.ofComponents (componentIso K R E) (fun f => componentIso_natural K R E f)).symm

@[simp] theorem comparison_inv_app (X : Over (OptionSyntax.obj F)) :
    (comparison K R E).inv.app X = (componentIso K R E X).hom := rfl

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessComparisonCore
