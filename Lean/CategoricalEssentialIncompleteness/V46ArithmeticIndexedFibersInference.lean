/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersSlices
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationPullbackPowers

/-! # Inference base change from actual premise and conclusion diagrams

The natural isomorphism is derived from finite-power pullbacks, pullback
pasting and universal finite coproducts. It is not an input assumption.
The statement includes the nullary component and retains ordered children.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.RuleBaseChange
open SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {F F' : D} {N : ℕ} (j : F' ⟶ F)
variable (R' : RulePresentation F' N) (R : RulePresentation F N)

/-- A cartesian map of the actual rule coefficients. Its fields are
premise/conclusion diagrams, with no evaluation or initiality conclusion. -/
structure Data where
  instanceMap : ∀ i, R'.instances i ⟶ R.instances i
  premises : ∀ i, R'.premises i ≫ finitePowerMap j i.val = instanceMap i ≫ R.premises i
  conclusion : ∀ i, IsPullback (instanceMap i) (R'.conclusion i) (R.conclusion i) j

variable (h : Data j R' R)

abbrev fiber : Over F ⥤ Over F' := Over.pullback j

omit [FinitaryExtensive D] in
private theorem childPower_comm (Q : Over F) (n : ℕ) :
    finitePowerMap ((fiber j).obj Q).hom n ≫ finitePowerMap j n =
      finitePowerMap (pullback.fst Q.hom j) n ≫ finitePowerMap Q.hom n := by
  change finitePowerMap (pullback.snd Q.hom j) n ≫ finitePowerMap j n =
    finitePowerMap (pullback.fst Q.hom j) n ≫ finitePowerMap Q.hom n
  simpa only [finitePowerMap_comp] using
    (congrArg (fun f => finitePowerMap f n) (pullback.condition (f := Q.hom) (g := j))).symm

def inputComponent (Q : Over F) (i : Fin (N+1)) :
    R'.ruleObject ((fiber j).obj Q) i ⟶ R.ruleObject Q i :=
  pullback.lift (pullback.fst _ _ ≫ h.instanceMap i)
    (pullback.snd _ _ ≫ finitePowerMap (pullback.fst Q.hom j) i.val) (by
      calc
        (pullback.fst _ _ ≫ h.instanceMap i) ≫ R.premises i =
            pullback.fst _ _ ≫ R'.premises i ≫ finitePowerMap j i.val := by
          rw [Category.assoc,← h.premises i]
        _ = pullback.snd _ _ ≫ finitePowerMap ((fiber j).obj Q).hom i.val ≫
            finitePowerMap j i.val := by rw [← Category.assoc,pullback.condition,Category.assoc]
        _ = _ := by rw [childPower_comm j Q i.val]; simp only [Category.assoc])

omit [FinitaryExtensive D] in
@[simp, reassoc] theorem inputComponent_fst (Q : Over F) (i : Fin (N+1)) :
    inputComponent j R' R h Q i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ h.instanceMap i := by simp [inputComponent]

omit [FinitaryExtensive D] in
@[simp, reassoc] theorem inputComponent_snd (Q : Over F) (i : Fin (N+1)) :
    inputComponent j R' R h Q i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (pullback.fst Q.hom j) i.val := by simp [inputComponent]

omit [FinitaryExtensive D] in
/-- The rule-input pullback is cartesian over its coefficient; this
uses the full tuple of the independently typed ordered child conclusions. -/
theorem inputCoefficientSquare (Q : Over F) (i : Fin (N+1)) :
    IsPullback (inputComponent j R' R h Q i) (pullback.fst _ _)
      (pullback.fst _ _) (h.instanceMap i) := by
  have hp := PullbackPowers.power (IsPullback.of_hasPullback Q.hom j) i.val
  have outer := (IsPullback.of_hasPullback (R'.premises i)
    (finitePowerMap ((fiber j).obj Q).hom i.val)).flip.paste_horiz hp
  have outer' : IsPullback
      (inputComponent j R' R h Q i ≫ pullback.snd (R.premises i) (finitePowerMap Q.hom i.val))
      (pullback.fst (R'.premises i) (finitePowerMap ((fiber j).obj Q).hom i.val))
      (finitePowerMap Q.hom i.val) (h.instanceMap i ≫ R.premises i) := by
    simpa only [inputComponent_snd,h.premises] using outer
  exact outer'.of_right (inputComponent_fst j R' R h Q i)
    (IsPullback.of_hasPullback (R.premises i) (finitePowerMap Q.hom i.val)).flip

omit [FinitaryExtensive D] in
/-- Pasting the actual coefficient conclusion square gives the required
base-change square for each inference arity, including arity zero. -/
theorem component_isPullback (Q : Over F) (i : Fin (N+1)) :
    IsPullback (inputComponent j R' R h Q i)
      (R'.ruleConclusion ((fiber j).obj Q) i) (R.ruleConclusion Q i) j :=
  (inputCoefficientSquare j R' R h Q i).paste_vert (h.conclusion i)

def input (Q : Over F) :
    (R'.inference.obj ((fiber j).obj Q)).left ⟶ (R.inference.obj Q).left :=
  Sigma.desc (fun i => inputComponent j R' R h Q i ≫ Sigma.ι (R.ruleObject Q) i)

theorem input_isPullback (Q : Over F) :
    IsPullback (input j R' R h Q) (R'.inference.obj ((fiber j).obj Q)).hom
      (R.inference.obj Q).hom j :=
  PullbackPowers.finiteSum (inputComponent j R' R h Q)
    (R'.ruleConclusion ((fiber j).obj Q)) (R.ruleConclusion Q) j
    (component_isPullback j R' R h Q)

def componentIso (Q : Over F) :
    R'.inference.obj ((fiber j).obj Q) ≅ (fiber j).obj (R.inference.obj Q) :=
  Over.isoMk (input_isPullback j R' R h Q).isoPullback (by simp)

@[simp, reassoc] theorem componentIso_input (Q : Over F) :
    (componentIso j R' R h Q).hom.left ≫ pullback.fst (R.inference.obj Q).hom j =
      input j R' R h Q := by simp [componentIso]

omit [FinitaryExtensive D] in
theorem inputComponent_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N+1)) :
    R'.ruleMap ((fiber j).map f) i ≫ inputComponent j R' R h Q' i =
      inputComponent j R' R h Q i ≫ R.ruleMap f i := by
  have hc : ((fiber j).map f).left ≫ pullback.fst Q'.hom j =
      pullback.fst Q.hom j ≫ f.left := by simp [Over.pullback]
  apply pullback.hom_ext
  · calc
      _ = R'.ruleMap ((fiber j).map f) i ≫
          (pullback.fst _ _ ≫ h.instanceMap i) := by
        rw [Category.assoc]
        exact congrArg (fun k => R'.ruleMap ((fiber j).map f) i ≫ k)
          (inputComponent_fst j R' R h Q' i)
      _ = pullback.fst _ _ ≫ h.instanceMap i := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ h.instanceMap i)
          (R'.ruleMap_fst ((fiber j).map f) i)
      _ = inputComponent j R' R h Q i ≫ pullback.fst _ _ :=
        (inputComponent_fst j R' R h Q i).symm
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun k => inputComponent j R' R h Q i ≫ k) (R.ruleMap_fst f i).symm
  · calc
      _ = R'.ruleMap ((fiber j).map f) i ≫
          (pullback.snd _ _ ≫ finitePowerMap (pullback.fst Q'.hom j) i.val) := by
        rw [Category.assoc]
        exact congrArg (fun k => R'.ruleMap ((fiber j).map f) i ≫ k)
          (inputComponent_snd j R' R h Q' i)
      _ = pullback.snd _ _ ≫ finitePowerMap ((fiber j).map f).left i.val ≫
          finitePowerMap (pullback.fst Q'.hom j) i.val := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ finitePowerMap (pullback.fst Q'.hom j) i.val)
          (R'.ruleMap_snd ((fiber j).map f) i)
      _ = pullback.snd _ _ ≫ finitePowerMap (pullback.fst Q.hom j) i.val ≫
          finitePowerMap f.left i.val := by
        rw [← finitePowerMap_comp,hc,finitePowerMap_comp]
      _ = inputComponent j R' R h Q i ≫ pullback.snd _ _ ≫ finitePowerMap f.left i.val := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ finitePowerMap f.left i.val)
          (inputComponent_snd j R' R h Q i).symm
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun k => inputComponent j R' R h Q i ≫ k) (R.ruleMap_snd f i).symm

theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (R'.inference.map ((fiber j).map f)).left ≫ input j R' R h Q' =
      input j R' R h Q ≫ (R.inference.map f).left := by
  apply Sigma.hom_ext
  intro i
  simp only [RulePresentation.inference,Over.homMk_left,Sigma.ι_map_assoc,
    input,Sigma.ι_comp_desc_assoc,Category.assoc,Sigma.ι_comp_desc,Sigma.ι_map]
  rw [← Category.assoc,inputComponent_natural,Category.assoc]

theorem componentIso_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    R'.inference.map ((fiber j).map f) ≫ (componentIso j R' R h Q').hom =
      (componentIso j R' R h Q).hom ≫ (fiber j).map (R.inference.map f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hp : ((fiber j).map (R.inference.map f)).left ≫
        pullback.fst (R.inference.obj Q').hom j =
      pullback.fst (R.inference.obj Q).hom j ≫ (R.inference.map f).left := by simp [Over.pullback]
    simp only [Over.comp_left,Category.assoc]
    rw [componentIso_input,hp,← Category.assoc,componentIso_input]
    exact input_natural j R' R h f
  · exact (Over.w _).trans (Over.w _).symm

/-- The actual constructor-compatible inference comparison is obtained
from the proved pullback squares and their naturality. -/
def comparison : R.inference ⋙ fiber j ≅ fiber j ⋙ R'.inference :=
  (NatIso.ofComponents (componentIso j R' R h)
    (fun f => componentIso_natural j R' R h f)).symm

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.RuleBaseChange
