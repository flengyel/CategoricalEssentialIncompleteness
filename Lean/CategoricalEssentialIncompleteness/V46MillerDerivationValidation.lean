/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationEquality
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessComparisonCore

/-! # Actual ordered-premise validation in the uniform carrier category

The successful source is the original pullback of the ordered child
conclusion tuple along the prescribed premise tuple. Children may have
different conclusions, and none is equated with the parent conclusion.
The Boolean/conclusion algebra always returns the label's actual q_n
conclusion, including at a failed validation node.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation
open SyntacticDerivation
variable {P : Uniform.Family}

abbrev interpretation : Total.TotalCategory P ⥤ (Discrete PUnit.{1} ⥤ Type) :=
  Total.underlying ⋙ Functor.const (Discrete PUnit.{1})

instance interpretation_reflectsIsomorphisms : (interpretation (P := P)).ReflectsIsomorphisms where
  reflects f hf := by
    let := hf
    have he : IsIso (((evaluation (Discrete PUnit.{1}) Type).obj ⟨PUnit.unit⟩).map
      ((interpretation (P := P)).map f)) := inferInstance
    change IsIso (Total.underlying.map f) at he
    let := he
    exact isIso_of_reflects_iso f Total.underlying

instance interpretation_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (interpretation (P := P)) := by
  dsimp only [interpretation]
  infer_instance

instance interpretation_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (interpretation (P := P)) := by
  dsimp only [interpretation]
  infer_instance

variable {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)

def ruleEquality (_R : RulePresentation F N) (i : Fin (N+1)) :
    DecidableVariables (finitePower F i.val) := equality _

abbrev validator : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  SuccessComparisonCore.validator R (ruleEquality R)

abbrev success : Over (OptionSyntax.obj F) ⥤ Over F :=
  Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)

def successComparison :
    SliceInitial.functor (PolynomialComparison.ordinary R) (validator R) ⋙ (success (F := F)) ≅
      (success (F := F)) ⋙ R.inference :=
  SuccessComparisonCore.comparison (interpretation (P := P)) R (ruleEquality R)

theorem ordered_success_pullback (Q : Over (OptionSyntax.obj F)) :
    IsPullback (SuccessComparisonCore.input R Q)
      (R.inference.obj ((success (F := F)).obj Q)).hom
      ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R)).obj Q).hom
      (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  SuccessComparisonCore.input_isPullback (interpretation (P := P)) R (ruleEquality R) Q

def checkedOperation (Q : Over F) (i : Fin (N+1)) {Z : Total.TotalCategory P}
    (h : R.ruleObject Q i ⟶ Z) : R.instances i ⨯ finitePower Q.left i.val ⟶ OptionSyntax.obj Z :=
  CheckedRoot.operation R Q i (ruleEquality R i) h

theorem checkedOperation_success (Q : Over F) (i : Fin (N+1)) {Z : Total.TotalCategory P}
    (h : R.ruleObject Q i ⟶ Z) :
    IsPullback (CheckedRoot.matchingMap R Q i) h (checkedOperation R Q i h) coprod.inr :=
  CheckedRoot.operation_isPullback R Q i (ruleEquality R i) h

def successFlag (Z : Total.TotalCategory P) : OptionSyntax.obj Z ⟶ Two (Total.TotalCategory P) :=
  coprod.desc (Two.constant (⊤_ (Total.TotalCategory P)) false) (Two.constant Z true)

theorem successFlag_fail (Z W : Total.TotalCategory P) :
    (OptionSyntax.fail : W ⟶ OptionSyntax.obj Z) ≫ successFlag Z=Two.constant W false := by
  simp [OptionSyntax.fail,successFlag,Two.constant,Two.point]

@[simp,reassoc] theorem successFlag_some (Z : Total.TotalCategory P) :
    (coprod.inr : Z ⟶ OptionSyntax.obj Z) ≫ successFlag Z=Two.constant Z true := by
  simp [successFlag]

def fromBoolean (Z : Total.TotalCategory P) : Two (Total.TotalCategory P) ⨯ Z ⟶ OptionSyntax.obj Z :=
  SumFibers.caseOf (prod.fst : Two (Total.TotalCategory P) ⨯ Z ⟶ Two (Total.TotalCategory P)) OptionSyntax.fail
    (pullback.fst (prod.fst : Two (Total.TotalCategory P) ⨯ Z ⟶ Two (Total.TotalCategory P)) coprod.inr ≫
      prod.snd ≫ coprod.inr)

def successfulChild (Z : Total.TotalCategory P) : Z ⟶ Two (Total.TotalCategory P) ⨯ Z :=
  prod.lift (Two.constant Z true) (𝟙 Z)

@[simp,reassoc] theorem fromBoolean_successful (Z : Total.TotalCategory P) :
    successfulChild Z ≫ fromBoolean Z=coprod.inr := by
  unfold fromBoolean
  rw [SumFibers.comp_caseOf_inr _ _ _ (successfulChild Z) (terminal.from Z) (by simp [successfulChild,Two.constant,Two.point])]
  simp [successfulChild]

def booleanComponent (i : Fin (N+1)) :
    R.instances i ⨯ finitePower (Two (Total.TotalCategory P) ⨯ F) i.val ⟶ Two (Total.TotalCategory P) ⨯ F :=
  prod.lift
    (prod.map (𝟙 _) (finitePowerMap (fromBoolean F) i.val) ≫
      OptionAlgebra.component R (ruleEquality R) (Over.mk (𝟙 F)) i
        (R.ruleConclusion (Over.mk (𝟙 F)) i) ≫ successFlag F)
    (prod.fst ≫ R.conclusion i)

theorem booleanComponent_conclusion (i : Fin (N+1)) :
    booleanComponent R i ≫ prod.snd=prod.fst ≫ R.conclusion i := by
  simp [booleanComponent]

theorem booleanComponent_matching (i : Fin (N+1)) :
    (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i ≫
      prod.map (𝟙 _) (finitePowerMap (successfulChild F) i.val)) ≫ booleanComponent R i=
        R.ruleConclusion (Over.mk (𝟙 F)) i ≫ successfulChild F := by
  apply prod.hom_ext
  · simp only [Category.assoc,booleanComponent,prod.lift_fst]
    have hc : prod.map (𝟙 (R.instances i)) (finitePowerMap (successfulChild F) i.val) ≫
        prod.map (𝟙 (R.instances i)) (finitePowerMap (fromBoolean F) i.val)=
          prod.map (𝟙 (R.instances i)) (finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val) := by
      rw [prod.map_map,Category.comp_id,← finitePowerMap_comp,fromBoolean_successful]
    rw [← Category.assoc (prod.map _ _) (prod.map _ _),hc]
    have hm := OptionAlgebra.component_matching R (ruleEquality R) (Over.mk (𝟙 F)) i
      (R.ruleConclusion (Over.mk (𝟙 F)) i)
    have hv := congrArg (fun k => k ≫ successFlag F) hm
    simp only [Category.assoc] at hv
    rw [successFlag_some] at hv
    simp only [successfulChild,prod.lift_fst]
    exact hv

  · simp [booleanComponent,successfulChild,CheckedRoot.matchingMap,RulePresentation.ruleConclusion]

def booleanValidator : Endofunctor.Algebra (PolynomialComparison.ordinary R) where
  a := Two (Total.TotalCategory P) ⨯ F
  str := Sigma.desc (booleanComponent R)

@[simp,reassoc] theorem booleanValidator_conclusion (i : Fin (N+1)) :
    Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (Two (Total.TotalCategory P) ⨯ F) j.val) i ≫
      (booleanValidator R).str ≫ prod.snd=prod.fst ≫ R.conclusion i := by
  change Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (Two (Total.TotalCategory P) ⨯ F) j.val) i ≫
    Sigma.desc (booleanComponent R) ≫ prod.snd=prod.fst ≫ R.conclusion i
  rw [Sigma.ι_comp_desc_assoc,booleanComponent_conclusion]

end CategoricalEssentialIncompleteness.V46.Miller.Derivation
