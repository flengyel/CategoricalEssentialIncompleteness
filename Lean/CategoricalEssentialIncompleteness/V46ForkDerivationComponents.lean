/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ForkDerivationComponentsBase

/-! # Span naturality of the actual finite-rule inputs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

private theorem paste_three {C : Type} [Category C]
    {A B C₀ D X Y Z W : C}
    (a₀ : X ⟶ A) (a₁ : Y ⟶ B) (a₂ : Z ⟶ C₀) (a₃ : W ⟶ D)
    (f : A ⟶ B) (g : B ⟶ C₀) (h : C₀ ⟶ D)
    (u : X ⟶ Y) (v : Y ⟶ Z) (w : Z ⟶ W)
    (h₀ : a₀ ≫ f = u ≫ a₁) (h₁ : a₁ ≫ g = v ≫ a₂) (h₂ : a₂ ≫ h = w ≫ a₃) :
    a₀ ≫ (f ≫ g ≫ h) = (u ≫ v ≫ w) ≫ a₃ := by
  calc
    _ = (a₀ ≫ f) ≫ g ≫ h := by simp only [Category.assoc]
    _ = (u ≫ a₁) ≫ g ≫ h := congrArg (fun k => k ≫ g ≫ h) h₀
    _ = u ≫ (a₁ ≫ g) ≫ h := by simp only [Category.assoc]
    _ = u ≫ (v ≫ a₂) ≫ h := congrArg (fun k => u ≫ k ≫ h) h₁
    _ = (u ≫ v) ≫ (a₂ ≫ h) := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ (w ≫ a₃) := congrArg (fun k => (u ≫ v) ≫ k) h₂
    _ = _ := by simp only [Category.assoc]

theorem componentInputIso_iota (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (j : WalkingSpan) (i : Fin 3) :
    (componentFunctor j).map (Sigma.ι ((rules a b).ruleObject Q) i) ≫ (componentInputIso a b Q j).hom =
      (componentBranchIso a b Q j i).hom ≫
        Sigma.ι ((Component.rules (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)).ruleObject (componentOver Q j)) i := by
  let M := NumericalRuleRebase.inputIso (evaluatedRules a b j) (componentFormulaIso j)
    ((Evaluation.overFunctor (K := componentFunctor j) (rules a b)).obj Q)
  let μ := (componentRuleHom a b j).mapRule (componentOver Q j)
  have h₀ := Evaluation.sumIso_iota (K := componentFunctor j) (rules a b) Q i
  have h₁ := Limits.Sigma.ι_mapIso_hom M i
  have h₂ := Limits.Sigma.ι_map μ i
  have h := paste_three _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂
  exact h

def componentLabelTransition (a b : Idem EffectiveFork.V) {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    (Component.rules (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)).instances i ⟶
    (Component.rules (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)).instances i :=
  (componentRuleIso a b j i).inv ≫ (componentTransition g).app ((rules a b).instances i) ≫
    (componentRuleIso a b k i).hom

theorem componentLabelTransition_square (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫ componentLabelTransition a b g i =
      (componentTransition g).app ((rules a b).instances i) ≫ (componentRuleIso a b k i).hom := by
  simp only [componentLabelTransition,← Category.assoc,Iso.hom_inv_id,Category.id_comp]

private theorem component_rule_source_premises (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).premises i =
      (componentFunctor j).map ((rules a b).premises i) ≫ (componentPowerIso j i.val).hom := by
  simpa only [componentRebasedRules,evaluatedRules,Evaluation.interpretedRules,NumericalRuleRebase.rules,
    componentPowerIso_hom,Category.assoc] using component_rule_premises a b j i

private theorem component_rule_source_conclusion (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).conclusion i =
      (componentFunctor j).map ((rules a b).conclusion i) ≫ (componentFormulaIso j).hom :=
  component_rule_conclusion a b j i

theorem componentLabelTransition_premises (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    componentLabelTransition a b g i ≫
      (Component.rules (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b)).premises i =
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).premises i ≫
          finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) i.val := by
  apply (cancel_epi (componentRuleIso a b j i).hom).mp
  erw [← Category.assoc,componentLabelTransition_square,Category.assoc,component_rule_source_premises,
    ← Category.assoc,← (componentTransition g).naturality,Category.assoc,componentPowerIso_transition,
    ← Category.assoc,← component_rule_source_premises,Category.assoc]

theorem componentLabelTransition_conclusion (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    componentLabelTransition a b g i ≫
      (Component.rules (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b)).conclusion i =
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).conclusion i ≫
          Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g) := by
  apply (cancel_epi (componentRuleIso a b j i).hom).mp
  erw [← Category.assoc,componentLabelTransition_square,Category.assoc,component_rule_source_conclusion,
    ← Category.assoc,← (componentTransition g).naturality,Category.assoc,component_formula_transition,
    ← Category.assoc,← component_rule_source_conclusion,Category.assoc]

private theorem power_square {W X Y F G : NumericalTuples.Object} (n : ℕ)
    (s : W ⟶ finitePower X n) (a : X ⟶ Y) (q₀ : X ⟶ F) (q₁ : Y ⟶ G) (f : F ⟶ G)
    (h : a ≫ q₁ = q₀ ≫ f) :
    (s ≫ finitePowerMap q₀ n) ≫ finitePowerMap f n =
      (s ≫ finitePowerMap a n) ≫ finitePowerMap q₁ n := by
  simp only [Category.assoc,← finitePowerMap_comp,h]

def componentBranchTransition (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    (Component.rules (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)).ruleObject (componentOver Q j) i ⟶
    (Component.rules (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)).ruleObject (componentOver Q k) i :=
  pullback.lift (pullback.fst _ _ ≫ componentLabelTransition a b g i)
    (pullback.snd _ _ ≫ finitePowerMap ((componentTransition g).app Q.left) i.val) (by
      calc
        _ = (pullback.fst _ _ ≫
            (Component.rules (componentSupport j a) (componentSupport j b)
              (componentSupport_re j a) (componentSupport_re j b)).premises i) ≫
                finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) i.val := by
          rw [Category.assoc,componentLabelTransition_premises,← Category.assoc]
        _ = (pullback.snd _ _ ≫ finitePowerMap (componentOver Q j).hom i.val) ≫
            finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) i.val :=
          congrArg (fun h => h ≫ finitePowerMap
            (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) i.val)
            (pullback.condition
              (f := (Component.rules (componentSupport j a) (componentSupport j b)
                (componentSupport_re j a) (componentSupport_re j b)).premises i)
              (g := finitePowerMap (componentOver Q j).hom i.val))
        _ = _ := power_square i.val (pullback.snd _ _)
          ((componentTransition g).app Q.left) (componentOver Q j).hom (componentOver Q k).hom
          (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) (componentOver_transition Q g))

@[simp] theorem componentBranchTransition_fst (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    componentBranchTransition a b Q g i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ componentLabelTransition a b g i := by
  simp only [componentBranchTransition,pullback.lift_fst]

@[simp] theorem componentBranchTransition_snd (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    componentBranchTransition a b Q g i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap ((componentTransition g).app Q.left) i.val := by
  simp only [componentBranchTransition,pullback.lift_snd]

def componentInputTransition (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k) :
    ((Component.rules (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j)).left ⟶
    ((Component.rules (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)).inference.obj (componentOver Q k)).left :=
  Limits.Sigma.map (componentBranchTransition a b Q g)

private theorem input_square_leg {C : Type} [Category C]
    {P₀ P₁ Q₀ Q₁ R₀ R₁ S₀ S₁ : C}
    (u₀ : P₀ ⟶ Q₀) (u₁ : P₁ ⟶ Q₁) (s : P₀ ⟶ P₁) (t : Q₀ ⟶ Q₁)
    (p₀ : Q₀ ⟶ R₀) (p₁ : Q₁ ⟶ R₁) (q₀ : P₀ ⟶ S₀) (q₁ : P₁ ⟶ S₁)
    (a₀ : S₀ ⟶ R₀) (a₁ : S₁ ⟶ R₁) (r : S₀ ⟶ S₁) (c : R₀ ⟶ R₁)
    (hu₀ : u₀ ≫ p₀ = q₀ ≫ a₀) (hu₁ : u₁ ≫ p₁ = q₁ ≫ a₁)
    (hs : s ≫ q₁ = q₀ ≫ r) (ha : r ≫ a₁ = a₀ ≫ c) (ht : t ≫ p₁ = p₀ ≫ c) :
    (s ≫ u₁) ≫ p₁ = (u₀ ≫ t) ≫ p₁ := by
  calc
    _ = s ≫ (q₁ ≫ a₁) := by rw [Category.assoc,hu₁]
    _ = q₀ ≫ r ≫ a₁ := by rw [← Category.assoc,hs,Category.assoc]
    _ = q₀ ≫ a₀ ≫ c := by rw [ha]
    _ = (u₀ ≫ p₀) ≫ c := by rw [hu₀,Category.assoc]
    _ = _ := by simp only [Category.assoc,ht]

theorem componentBranchIso_transition (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    (componentTransition g).app ((rules a b).ruleObject Q i) ≫ (componentBranchIso a b Q k i).hom =
      (componentBranchIso a b Q j i).hom ≫ componentBranchTransition a b Q g i := by
  apply pullback.hom_ext
  · exact input_square_leg
      (componentBranchIso a b Q j i).hom (componentBranchIso a b Q k i).hom
      ((componentTransition g).app ((rules a b).ruleObject Q i)) (componentBranchTransition a b Q g i)
      (pullback.fst _ _) (pullback.fst _ _)
      ((componentFunctor j).map (pullback.fst ((rules a b).premises i) (finitePowerMap Q.hom i.val)))
      ((componentFunctor k).map (pullback.fst ((rules a b).premises i) (finitePowerMap Q.hom i.val)))
      (componentRuleIso a b j i).hom (componentRuleIso a b k i).hom
      ((componentTransition g).app ((rules a b).instances i)) (componentLabelTransition a b g i)
      (componentBranchIso_fst a b Q j i) (componentBranchIso_fst a b Q k i)
      ((componentTransition g).naturality (pullback.fst ((rules a b).premises i) (finitePowerMap Q.hom i.val))).symm
      (componentLabelTransition_square a b g i).symm (componentBranchTransition_fst a b Q g i)
  · exact input_square_leg
      (componentBranchIso a b Q j i).hom (componentBranchIso a b Q k i).hom
      ((componentTransition g).app ((rules a b).ruleObject Q i)) (componentBranchTransition a b Q g i)
      (pullback.snd _ _) (pullback.snd _ _)
      ((componentFunctor j).map (pullback.snd ((rules a b).premises i) (finitePowerMap Q.hom i.val)))
      ((componentFunctor k).map (pullback.snd ((rules a b).premises i) (finitePowerMap Q.hom i.val)))
      (Evaluation.finitePowerIso (K := componentFunctor j) Q.left i.val).hom
      (Evaluation.finitePowerIso (K := componentFunctor k) Q.left i.val).hom
      ((componentTransition g).app (finitePower Q.left i.val))
      (finitePowerMap ((componentTransition g).app Q.left) i.val)
      (componentBranchIso_snd a b Q j i) (componentBranchIso_snd a b Q k i)
      ((componentTransition g).naturality (pullback.snd ((rules a b).premises i) (finitePowerMap Q.hom i.val))).symm
      (Evaluation.finitePowerIso_transformation (componentTransition g) Q.left i.val)
      (componentBranchTransition_snd a b Q g i)

private theorem sum_natural
    (K L : EffectiveFork.Total ⥤ NumericalTuples.Object)
    [PreservesFiniteCoproducts K] [PreservesFiniteCoproducts L] (α : K ⟶ L)
    {I : Type} [Finite I] (X : I → EffectiveFork.Total) (Y Z : I → NumericalTuples.Object)
    (f : ∀ i, K.obj (X i) ⟶ Y i) (g : ∀ i, L.obj (X i) ⟶ Z i) (t : ∀ i, Y i ⟶ Z i)
    (u : K.obj (∐ X) ⟶ ∐ Y) (v : L.obj (∐ X) ⟶ ∐ Z)
    (h₀ : ∀ i, K.map (Limits.Sigma.ι X i) ≫ u = f i ≫ Limits.Sigma.ι Y i)
    (h₁ : ∀ i, L.map (Limits.Sigma.ι X i) ≫ v = g i ≫ Limits.Sigma.ι Z i)
    (h₂ : ∀ i, α.app (X i) ≫ g i = f i ≫ t i) :
    α.app (∐ X) ≫ v = u ≫ Limits.Sigma.map t := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Limits.Sigma.hom_ext
  intro i
  calc
    _ = K.map (Limits.Sigma.ι X i) ≫ α.app (∐ X) ≫ v := by
      simp only [← Category.assoc,ι_comp_sigmaComparison]
    _ = α.app (X i) ≫ L.map (Limits.Sigma.ι X i) ≫ v := by
      rw [← Category.assoc,α.naturality,Category.assoc]
    _ = α.app (X i) ≫ g i ≫ Limits.Sigma.ι Z i := by rw [h₁ i]
    _ = f i ≫ t i ≫ Limits.Sigma.ι Z i := by rw [← Category.assoc,h₂ i,Category.assoc]
    _ = (f i ≫ Limits.Sigma.ι Y i) ≫ Limits.Sigma.map t := by
      rw [Category.assoc,Limits.Sigma.ι_map]
    _ = (K.map (Limits.Sigma.ι X i) ≫ u) ≫ Limits.Sigma.map t :=
      congrArg (fun k => k ≫ Limits.Sigma.map t) (h₀ i).symm
    _ = _ := by simp only [← Category.assoc,ι_comp_sigmaComparison]

/-- The full input chart is natural for both span arrows and identities,
using the original rule-label pullbacks and finite coproduct maps. -/
theorem componentInputIso_transition (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app ((rules a b).inference.obj Q).left ≫ (componentInputIso a b Q k).hom =
      (componentInputIso a b Q j).hom ≫ componentInputTransition a b Q g := by
  have h := sum_natural (componentFunctor j) (componentFunctor k) (componentTransition g)
    ((rules a b).ruleObject Q)
    ((Component.rules (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)).ruleObject (componentOver Q j))
    ((Component.rules (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)).ruleObject (componentOver Q k))
    (fun i => (componentBranchIso a b Q j i).hom) (fun i => (componentBranchIso a b Q k i).hom)
    (componentBranchTransition a b Q g) (componentInputIso a b Q j).hom (componentInputIso a b Q k).hom
    (componentInputIso_iota a b Q j) (componentInputIso_iota a b Q k)
    (componentBranchIso_transition a b Q g)
  exact h


def componentCoefficientTransition (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 5) :
    Component.axiomFamily (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b) i ⟶
    Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b) i :=
  (componentCoefficientIso a b j i).inv ≫ (componentTransition g).app (axiomCoefficients a b i) ≫
    (componentCoefficientIso a b k i).hom

private theorem conjugate_iota {C : Type} [Category C]
    {X₀ X₁ Y₀ Y₁ A₀ A₁ B₀ B₁ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) [Epi e₀]
    (i₀ : Y₀ ⟶ B₀) (i₁ : Y₁ ⟶ B₁) (s₀ : X₀ ⟶ A₀) (s₁ : X₁ ⟶ A₁)
    (E₀ : A₀ ⟶ B₀) (E₁ : A₁ ⟶ B₁) (L : B₀ ⟶ B₁)
    (α : A₀ ⟶ A₁) (a : X₀ ⟶ X₁) (t : Y₀ ⟶ Y₁)
    (h₀ : s₀ ≫ E₀ = e₀ ≫ i₀) (hL : E₀ ≫ L = α ≫ E₁)
    (hn : s₀ ≫ α = a ≫ s₁) (h₁ : s₁ ≫ E₁ = e₁ ≫ i₁) (ht : e₀ ≫ t = a ≫ e₁) :
    i₀ ≫ L = t ≫ i₁ := by
  apply (cancel_epi e₀).mp
  calc
    _ = (s₀ ≫ E₀) ≫ L := by rw [h₀,Category.assoc]
    _ = s₀ ≫ (α ≫ E₁) := by rw [Category.assoc,hL]
    _ = (a ≫ s₁) ≫ E₁ := by rw [← Category.assoc,hn]
    _ = a ≫ (e₁ ≫ i₁) := by rw [Category.assoc,h₁]
    _ = (e₀ ≫ t) ≫ i₁ := by rw [ht,Category.assoc]
    _ = _ := Category.assoc _ _ _

private theorem componentCoefficientTransition_square (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 5) :
    (componentCoefficientIso a b j i).hom ≫ componentCoefficientTransition a b g i =
      (componentTransition g).app (axiomCoefficients a b i) ≫ (componentCoefficientIso a b k i).hom := by
  simp only [componentCoefficientTransition,← Category.assoc,Iso.hom_inv_id,Category.id_comp]

theorem componentLabelTransition_iota (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 5) :
    Sigma.ι (Component.axiomFamily (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)) i ≫ componentLabelTransition a b g 0 =
      componentCoefficientTransition a b g i ≫
        Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
          (componentSupport_re k a) (componentSupport_re k b)) i := by
  have hL : (componentAxiomIso a b j).hom ≫ componentLabelTransition a b g 0 =
      (componentTransition g).app (axiomObject a b) ≫ (componentAxiomIso a b k).hom :=
    componentLabelTransition_square a b g 0
  have h := conjugate_iota (componentCoefficientIso a b j i).hom (componentCoefficientIso a b k i).hom
    _ _ _ _ _ _ _ _ _ _ (componentAxiomIso_iota a b j i) hL
    ((componentTransition g).naturality (Limits.Sigma.ι (axiomCoefficients a b) i))
    (componentAxiomIso_iota a b k i) (componentCoefficientTransition_square a b g i)
  exact h

private theorem coefficientTransition_logical1 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    componentCoefficientTransition a b g 0 =
      finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) 2 := by
  apply (cancel_epi (componentPowerIso j 2).hom).mp
  change (componentPowerIso j 2).hom ≫
      ((componentPowerIso j 2).inv ≫ (componentTransition g).app (finitePower sentenceObject 2) ≫
        (componentPowerIso k 2).hom) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  exact componentPowerIso_transition g 2

private theorem coefficientTransition_logical2 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    componentCoefficientTransition a b g 1 =
      finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) 3 := by
  apply (cancel_epi (componentPowerIso j 3).hom).mp
  change (componentPowerIso j 3).hom ≫
      ((componentPowerIso j 3).inv ≫ (componentTransition g).app (finitePower sentenceObject 3) ≫
        (componentPowerIso k 3).hom) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  exact componentPowerIso_transition g 3

private theorem coefficientTransition_logical3 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    componentCoefficientTransition a b g 2 =
      finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) 2 := by
  apply (cancel_epi (componentPowerIso j 2).hom).mp
  change (componentPowerIso j 2).hom ≫
      ((componentPowerIso j 2).inv ≫ (componentTransition g).app (finitePower sentenceObject 2) ≫
        (componentPowerIso k 2).hom) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  exact componentPowerIso_transition g 2

private theorem component_domain_transition_value {j k : WalkingSpan} (g : j ⟶ k)
    (a : Idem EffectiveFork.V) (x : NumericalTuples.Point ((componentFunctor j).obj (axiomDomain a))) :
    (((componentTransition g).app (axiomDomain a)).toFun x).val = spanAtoms g x.val := by
  cases g with
  | id j =>
    erw [componentTransition_id j (axiomDomain a)]
    rfl
  | init i =>
    cases i
    · have h := EnumerableCarriers.totalFunction_mem
        ((EffectiveFork.totalFunctor.obj (axiomDomain a)).map WalkingSpan.Hom.fst) x
      change _ ∈ EnumerableCarriers.val (EnumerableCarriers.restrictMap EffectiveFork.V.leftMap
        (EffectiveFork.centerIdem a) (EffectiveFork.leftIdem a) (EffectiveFork.closed_left a)) x.val at h
      exact (EffectiveFork.mem_V_left _ _).mp
        ((EnumerableCarriers.mem_val_restrictMap _ _ _ _ _ _).mp h).2
    · have h := EnumerableCarriers.totalFunction_mem
        ((EffectiveFork.totalFunctor.obj (axiomDomain a)).map WalkingSpan.Hom.snd) x
      change _ ∈ EnumerableCarriers.val (EnumerableCarriers.restrictMap EffectiveFork.V.rightMap
        (EffectiveFork.centerIdem a) (EffectiveFork.rightIdem a) (EffectiveFork.closed_right a)) x.val at h
      exact (EffectiveFork.mem_V_right _ _).mp
        ((EnumerableCarriers.mem_val_restrictMap _ _ _ _ _ _).mp h).2

private theorem coefficientTransition_positive_value (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (x : NumericalTuples.Point
      (Component.axiomFamily (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) 3)) :
    ((componentCoefficientTransition a b g 3).toFun x).val = spanAtoms g x.val := by
  cases g with
  | id j =>
    simp only [componentCoefficientTransition]
    erw [componentTransition_id j (axiomCoefficients a b 3),Category.id_comp,Iso.inv_hom_id]
    rfl
  | init i =>
    cases i
    · let x₀ : NumericalTuples.Point ((componentFunctor .zero).obj (axiomDomain a)) := x
      have h := component_domain_transition_value WalkingSpan.Hom.fst a x₀
      exact h
    · let x₀ : NumericalTuples.Point ((componentFunctor .zero).obj (axiomDomain a)) := x
      have h := component_domain_transition_value WalkingSpan.Hom.snd a x₀
      exact h

private theorem coefficientTransition_negative_value (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (x : NumericalTuples.Point
      (Component.axiomFamily (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) 4)) :
    ((componentCoefficientTransition a b g 4).toFun x).val = spanAtoms g x.val := by
  cases g with
  | id j =>
    simp only [componentCoefficientTransition]
    erw [componentTransition_id j (axiomCoefficients a b 4),Category.id_comp,Iso.inv_hom_id]
    rfl
  | init i =>
    cases i
    · let x₀ : NumericalTuples.Point ((componentFunctor .zero).obj (axiomDomain b)) := x
      have h := component_domain_transition_value WalkingSpan.Hom.fst b x₀
      exact h
    · let x₀ : NumericalTuples.Point ((componentFunctor .zero).obj (axiomDomain b)) := x
      have h := component_domain_transition_value WalkingSpan.Hom.snd b x₀
      exact h

private theorem pairPoint_map {X X' Y Y' : NumericalTuples.Object} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : NumericalTuples.Point X) (y : NumericalTuples.Point Y) :
    (prod.map f g).toFun (Component.pairPoint x y) = Component.pairPoint (f.toFun x) (g.toFun y) := by
  apply Component.prodPoint_ext <;> simp

private theorem formulaPair_map (f : ℕ → ℕ) (hf : Computable f) (p q : ForkSyntax.Formula) :
    (finitePowerMap (Naturality.formulaMap f hf) 2).toFun
      (Component.pairPoint (Component.formulaPoint p) (Component.formulaPoint q)) =
      Component.pairPoint (Component.formulaPoint (p.mapAtoms f)) (Component.formulaPoint (q.mapAtoms f)) :=
  (pairPoint_map (Naturality.formulaMap f hf) (Naturality.formulaMap f hf) _ _).trans
    (congrArg₂ Component.pairPoint (Naturality.formulaMap_encoded f hf p) (Naturality.formulaMap_encoded f hf q))

private theorem formulaTriple_map (f : ℕ → ℕ) (hf : Computable f) (p q r : ForkSyntax.Formula) :
    (finitePowerMap (Naturality.formulaMap f hf) 3).toFun
      (Component.pairPoint (Component.pairPoint (Component.formulaPoint p) (Component.formulaPoint q))
        (Component.formulaPoint r)) =
      Component.pairPoint
        (Component.pairPoint (Component.formulaPoint (p.mapAtoms f)) (Component.formulaPoint (q.mapAtoms f)))
        (Component.formulaPoint (r.mapAtoms f)) :=
  (pairPoint_map (finitePowerMap (Naturality.formulaMap f hf) 2) (Naturality.formulaMap f hf) _ _).trans
    (congrArg₂ Component.pairPoint (formulaPair_map f hf p q) (Naturality.formulaMap_encoded f hf r))

theorem componentLabelTransition_logical1 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (p q : ForkSyntax.Formula) :
    (componentLabelTransition a b g 0).toFun
      (Component.logical1Label (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) p q) =
      Component.logical1Label (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) := by
  have h := congrArg (fun f => f.toFun (Component.pairPoint (Component.formulaPoint p) (Component.formulaPoint q)))
    (componentLabelTransition_iota a b g 0)
  exact h.trans (congrArg
    (Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)) 0).toFun (by
        erw [coefficientTransition_logical1]
        exact formulaPair_map _ _ p q))

theorem componentLabelTransition_logical2 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (p q r : ForkSyntax.Formula) :
    (componentLabelTransition a b g 0).toFun
      (Component.logical2Label (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) p q r) =
      Component.logical2Label (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b)
        (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) (r.mapAtoms (spanAtoms g)) := by
  have h := congrArg (fun f => f.toFun
    (Component.pairPoint (Component.pairPoint (Component.formulaPoint p) (Component.formulaPoint q))
      (Component.formulaPoint r))) (componentLabelTransition_iota a b g 1)
  exact h.trans (congrArg
    (Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)) 1).toFun (by
        erw [coefficientTransition_logical2]
        exact formulaTriple_map _ _ p q r))

theorem componentLabelTransition_logical3 (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (p q : ForkSyntax.Formula) :
    (componentLabelTransition a b g 0).toFun
      (Component.logical3Label (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) p q) =
      Component.logical3Label (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) := by
  have h := congrArg (fun f => f.toFun (Component.pairPoint (Component.formulaPoint p) (Component.formulaPoint q)))
    (componentLabelTransition_iota a b g 2)
  exact h.trans (congrArg
    (Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)) 2).toFun (by
        erw [coefficientTransition_logical3]
        exact formulaPair_map _ _ p q))

theorem componentLabelTransition_positive (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (x : ℕ) (hx : x ∈ componentSupport j a) :
    (componentLabelTransition a b g 0).toFun
      (Component.positiveLabel (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) x hx) =
      Component.positiveLabel (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (spanAtoms g x) (componentSupport_map g a x hx) := by
  let z : NumericalTuples.Point (Component.positiveObject (componentSupport j a) (componentSupport_re j a)) := ⟨x,hx⟩
  have h := congrArg (fun f => f.toFun z) (componentLabelTransition_iota a b g 3)
  exact h.trans (congrArg
    (Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)) 3).toFun
        (Subtype.ext (coefficientTransition_positive_value a b g ⟨x,hx⟩)))

theorem componentLabelTransition_negative (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (x : ℕ) (hx : x ∈ componentSupport j b) :
    (componentLabelTransition a b g 0).toFun
      (Component.negativeLabel (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) x hx) =
      Component.negativeLabel (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (spanAtoms g x) (componentSupport_map g b x hx) := by
  let z : NumericalTuples.Point (Component.negativeObject (componentSupport j b) (componentSupport_re j b)) := ⟨x,hx⟩
  have h := congrArg (fun f => f.toFun z) (componentLabelTransition_iota a b g 4)
  exact h.trans (congrArg
    (Sigma.ι (Component.axiomFamily (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)) 4).toFun
        (Subtype.ext (coefficientTransition_negative_value a b g ⟨x,hx⟩)))

theorem componentLabelTransition_mp (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) (p q : ForkSyntax.Formula) :
    (componentLabelTransition a b g 2).toFun (Component.mpLabel p q) =
      Component.mpLabel (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) := by
  have h : componentLabelTransition a b g 2 =
      finitePowerMap (Naturality.formulaMap (spanAtoms g) (spanAtoms_computable g)) 2 := by
    apply (cancel_epi (componentPowerIso j 2).hom).mp
    exact (componentLabelTransition_square a b g 2).trans (componentPowerIso_transition g 2)
  erw [h]
  exact formulaPair_map _ _ p q


theorem componentInputTransition_iota (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) {j k : WalkingSpan} (g : j ⟶ k) (i : Fin 3) :
    Sigma.ι ((Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).ruleObject (componentOver Q j)) i ≫
        componentInputTransition a b Q g =
      componentBranchTransition a b Q g i ≫
        Sigma.ι ((Component.rules (componentSupport k a) (componentSupport k b)
          (componentSupport_re k a) (componentSupport_re k b)).ruleObject (componentOver Q k)) i :=
  Sigma.ι_map (componentBranchTransition a b Q g) i

private theorem componentInputTransition_nullary (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) {j k : WalkingSpan} (g : j ⟶ k)
    (ξ : NumericalTuples.Point (Component.axiomObject (componentSupport j a) (componentSupport j b)
      (componentSupport_re j a) (componentSupport_re j b)))
    (η : NumericalTuples.Point (Component.axiomObject (componentSupport k a) (componentSupport k b)
      (componentSupport_re k a) (componentSupport_re k b)))
    (hlabel : (componentLabelTransition a b g 0).toFun ξ = η) :
    (componentInputTransition a b Q g).toFun
      (Component.nullaryNodePoint (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) ξ) =
      Component.nullaryNodePoint (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k) η := by
  let u := Component.nullaryInputPoint (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) ξ
  have h := congrArg (fun f => f.toFun u) (componentInputTransition_iota a b Q g 0)
  apply h.trans
  apply congrArg (Sigma.ι ((Component.rules (componentSupport k a) (componentSupport k b)
    (componentSupport_re k a) (componentSupport_re k b)).ruleObject (componentOver Q k)) 0).toFun
  apply Component.pullbackPoint_ext
  · exact (congrArg (fun f => f.toFun u) (componentBranchTransition_fst a b Q g 0)).trans
      ((congrArg (componentLabelTransition a b g 0).toFun
        (Component.nullaryInputPoint_fst (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) ξ)).trans
        (hlabel.trans (Component.nullaryInputPoint_fst (componentSupport k a) (componentSupport k b)
          (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k) η).symm))
  · exact Component.terminalPoint_ext _ _

private theorem componentInputTransition_mp (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) {j k : WalkingSpan} (g : j ⟶ k) (p q : ForkSyntax.Formula)
    (x y : NumericalTuples.Point (componentOver Q j).left)
    (hx : ((componentOver Q j).hom.toFun x).val = p.encode)
    (hy : ((componentOver Q j).hom.toFun y).val = (ForkSyntax.Formula.imp p q).encode) :
    (componentInputTransition a b Q g).toFun
      (Component.mpNodePoint (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) p q x y hx hy) =
      Component.nodeInput (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
        (Naturality.mapNode (spanAtoms g) (spanAtoms_computable g)
          (componentSupport_map g a) (componentSupport_map g b)
          ((componentTransition g).app Q.left) (componentOver_transition Q g) (.mp p q x y hx hy)) := by
  let h : (componentOver Q j).left ⟶ (componentOver Q k).left := (componentTransition g).app Q.left
  let hcx := Naturality.point_relabel_conclusion (Q := componentOver Q j) (Q' := componentOver Q k)
    (spanAtoms g) (spanAtoms_computable g) h (componentOver_transition Q g) p x hx
  let hcy := Naturality.point_relabel_conclusion (Q := componentOver Q j) (Q' := componentOver Q k)
    (spanAtoms g) (spanAtoms_computable g) h (componentOver_transition Q g) (.imp p q) y hy
  let u := Component.mpInputPoint (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) p q x y hx hy
  let v := Component.mpInputPoint (componentSupport k a) (componentSupport k b)
    (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
    (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) (h.toFun x) (h.toFun y) hcx hcy
  have hs := congrArg (fun f => f.toFun u) (componentInputTransition_iota a b Q g 2)
  apply hs.trans
  apply congrArg (Sigma.ι ((Component.rules (componentSupport k a) (componentSupport k b)
    (componentSupport_re k a) (componentSupport_re k b)).ruleObject (componentOver Q k)) 2).toFun
  apply Component.pullbackPoint_ext
  · exact (congrArg (fun f => f.toFun u) (componentBranchTransition_fst a b Q g 2)).trans
      ((congrArg (componentLabelTransition a b g 2).toFun
        (Component.mpInputPoint_label (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) p q x y hx hy)).trans
        ((componentLabelTransition_mp a b g p q).trans
          (Component.mpInputPoint_label (componentSupport k a) (componentSupport k b)
            (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
            (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) (h.toFun x) (h.toFun y) hcx hcy).symm))
  · apply Component.prodPoint_ext
    · exact (congrArg (fun f => (Component.firstPoint (f.toFun u)))
        (componentBranchTransition_snd a b Q g 2)).trans
        ((Component.prodMap_first h h _).trans
          ((congrArg h.toFun (Component.mpInputPoint_first (componentSupport j a) (componentSupport j b)
            (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) p q x y hx hy)).trans
            (Component.mpInputPoint_first (componentSupport k a) (componentSupport k b)
              (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
              (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) (h.toFun x) (h.toFun y) hcx hcy).symm))
    · exact (congrArg (fun f => (Component.secondPoint (f.toFun u)))
        (componentBranchTransition_snd a b Q g 2)).trans
        ((Component.prodMap_second h h _).trans
          ((congrArg h.toFun (Component.mpInputPoint_second (componentSupport j a) (componentSupport j b)
            (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) p q x y hx hy)).trans
            (Component.mpInputPoint_second (componentSupport k a) (componentSupport k b)
              (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
              (p.mapAtoms (spanAtoms g)) (q.mapAtoms (spanAtoms g)) (h.toFun x) (h.toFun y) hcx hcy).symm))

/-- Every selected root and both ordered children have the actual
span relabeling under the canonical input maps. -/
theorem componentInputTransition_node (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k)
    (n : Component.Node (componentSupport j a) (componentSupport j b) (componentOver Q j)) :
    (componentInputTransition a b Q g).toFun
      (Component.nodeInput (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) n) =
      Component.nodeInput (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
        (Naturality.mapNode (spanAtoms g) (spanAtoms_computable g)
          (componentSupport_map g a) (componentSupport_map g b)
          ((componentTransition g).app Q.left) (componentOver_transition Q g) n) := by
  cases n with
  | logical1 p q => exact componentInputTransition_nullary a b Q g _ _ (componentLabelTransition_logical1 a b g p q)
  | logical2 p q r => exact componentInputTransition_nullary a b Q g _ _ (componentLabelTransition_logical2 a b g p q r)
  | logical3 p q => exact componentInputTransition_nullary a b Q g _ _ (componentLabelTransition_logical3 a b g p q)
  | positive x hx => exact componentInputTransition_nullary a b Q g _ _ (componentLabelTransition_positive a b g x hx)
  | negative x hx => exact componentInputTransition_nullary a b Q g _ _ (componentLabelTransition_negative a b g x hx)
  | mp p q x y hx hy => exact componentInputTransition_mp a b Q g p q x y hx hy

theorem componentInputIso_transition_node (a b : Idem EffectiveFork.V) (Q : Over sentenceObject)
    {j k : WalkingSpan} (g : j ⟶ k)
    (n : Component.Node (componentSupport j a) (componentSupport j b) (componentOver Q j)) :
    (componentInputIso a b Q k).hom.toFun
      (((componentTransition g).app ((rules a b).inference.obj Q).left).toFun
        ((componentInputIso a b Q j).inv.toFun
          (Component.nodeInput (componentSupport j a) (componentSupport j b)
            (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) n))) =
      Component.nodeInput (componentSupport k a) (componentSupport k b)
        (componentSupport_re k a) (componentSupport_re k b) (componentOver Q k)
        (Naturality.mapNode (spanAtoms g) (spanAtoms_computable g)
          (componentSupport_map g a) (componentSupport_map g b)
          ((componentTransition g).app Q.left) (componentOver_transition Q g) n) := by
  let u := Component.nodeInput (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) (componentOver Q j) n
  have h := congrArg (fun f => f.toFun ((componentInputIso a b Q j).inv.toFun u))
    (componentInputIso_transition a b Q g)
  have hi := congrArg (fun f => f.toFun u) (componentInputIso a b Q j).inv_hom_id
  exact h.trans ((congrArg (componentInputTransition a b Q g).toFun hi).trans
    (componentInputTransition_node a b Q g n))


theorem componentAlgebra_node_natural (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) {j k : WalkingSpan} (g : j ⟶ k)
    (n : Component.Node (componentSupport j a) (componentSupport j b) (componentOver B.a j)) :
    ((componentTransition g).app B.a.left).toFun
      ((componentAlgebra a b B j).str.left.toFun
        (Component.nodeInput (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b) (componentOver B.a j) n)) =
      (componentAlgebra a b B k).str.left.toFun
        (Component.nodeInput (componentSupport k a) (componentSupport k b)
          (componentSupport_re k a) (componentSupport_re k b) (componentOver B.a k)
          (Naturality.mapNode (spanAtoms g) (spanAtoms_computable g)
            (componentSupport_map g a) (componentSupport_map g b)
            ((componentTransition g).app B.a.left) (componentOver_transition B.a g) n)) := by
  let u := Component.nodeInput (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) (componentOver B.a j) n
  let x := (componentInputIso a b B.a j).inv.toFun u
  let v := Component.nodeInput (componentSupport k a) (componentSupport k b)
    (componentSupport_re k a) (componentSupport_re k b) (componentOver B.a k)
    (Naturality.mapNode (spanAtoms g) (spanAtoms_computable g)
      (componentSupport_map g a) (componentSupport_map g b)
      ((componentTransition g).app B.a.left) (componentOver_transition B.a g) n)
  have hn := componentInputIso_transition_node a b B.a g n
  have hi := congrArg (fun f => f.toFun
    (((componentTransition g).app ((rules a b).inference.obj B.a).left).toFun x))
      (componentInputIso a b B.a k).hom_inv_id
  have he : (((componentTransition g).app ((rules a b).inference.obj B.a).left).toFun x) =
      (componentInputIso a b B.a k).inv.toFun v :=
    hi.symm.trans (congrArg (componentInputIso a b B.a k).inv.toFun hn)
  have hc := congrArg (fun f => f.toFun x) ((componentTransition g).naturality B.str.left)
  exact hc.trans (congrArg ((componentFunctor k).map B.str.left).toFun he)

/-- The operation compatibility used for component folds is derived
from the given GLOBAL algebra's actual natural structure morphism. -/
theorem componentAlgebra_naturality (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) {j k : WalkingSpan} (g : j ⟶ k) :
    Naturality.AlgebraNaturality
      (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (componentAlgebra a b B j) (componentAlgebra a b B k)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
      ((componentTransition g).app B.a.left) (componentOver_transition B.a g) :=
  Naturality.algebraNaturalityOfNodes
    (componentSupport_re j a) (componentSupport_re j b)
    (componentSupport_re k a) (componentSupport_re k b)
    (componentAlgebra a b B j) (componentAlgebra a b B k)
    (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
    ((componentTransition g).app B.a.left) (componentOver_transition B.a g)
    (componentAlgebra_node_natural a b B g)

end CategoricalEssentialIncompleteness.V46.ForkDerivation
