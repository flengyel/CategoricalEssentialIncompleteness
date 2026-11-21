/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46FiniteRuleTransport
public import CategoricalEssentialIncompleteness.V46ForwardRuleRelabelling
public import CategoricalEssentialIncompleteness.V46ForkCanonicalFormulaStability

/-! # Evaluation and arbitrary transformations of finite inference inputs -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.FiniteInferenceEvaluation
open FiniteRuleTransport
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (K : C ⥤ D) [PreservesFiniteLimits K] [PreservesFiniteCoproducts K]
variable {F : C} {N : ℕ} (R : RulePresentation F N)

def sumIso (Q : Over F) : K.obj (∐ R.ruleObject Q) ≅
    ∐ (mappedRules K R).ruleObject ((Over.post K).obj Q) :=
  (asIso (sigmaComparison K (R.ruleObject Q))).symm ≪≫ Sigma.mapIso (ruleObjectIso K R Q)

@[reassoc (attr := simp)] theorem sumIso_iota (Q : Over F) (i : Fin (N + 1)) :
    K.map (Sigma.ι (R.ruleObject Q) i) ≫ (sumIso K R Q).hom =
      (ruleObjectIso K R Q i).hom ≫ Sigma.ι ((mappedRules K R).ruleObject ((Over.post K).obj Q)) i := by
  simp only [sumIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

omit [Regular C] [Regular D] [PreservesFiniteLimits K] in
theorem mapSum_hom_ext {I : Type} [Finite I] (X : I → C) {Y : D}
    (f g : K.obj (∐ X) ⟶ Y)
    (h : ∀ i, K.map (Sigma.ι X i) ≫ f = K.map (Sigma.ι X i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using h i

def overIso (Q : Over F) : (Over.post K).obj (R.inference.obj Q) ≅
    (mappedRules K R).inference.obj ((Over.post K).obj Q) :=
  Over.isoMk (sumIso K R Q) (by
    apply mapSum_hom_ext K (R.ruleObject Q)
    intro i
    rw [← Category.assoc, sumIso_iota, Category.assoc]
    change (ruleObjectIso K R Q i).hom ≫ Sigma.ι _ i ≫ Sigma.desc _ =
      K.map (Sigma.ι _ i) ≫ K.map (Sigma.desc _)
    rw [Sigma.ι_comp_desc, ← K.map_comp, Sigma.ι_comp_desc]
    exact ruleObjectIso_conclusion K R Q i)

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] [PreservesFiniteCoproducts K] in
theorem branch_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N + 1)) :
    K.map (R.ruleMap f i) ≫ (ruleObjectIso K R Q' i).hom =
      (ruleObjectIso K R Q i).hom ≫ (mappedRules K R).ruleMap ((Over.post K).map f) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, ruleObjectIso_fst, ← K.map_comp, R.ruleMap_fst,
      Category.assoc, RulePresentation.ruleMap_fst, ruleObjectIso_fst]
  · rw [Category.assoc, ruleObjectIso_snd, ← Category.assoc, ← K.map_comp,
      R.ruleMap_snd, K.map_comp, Category.assoc, power_naturality,
      ← Category.assoc, ← ruleObjectIso_snd]
    simp only [Category.assoc, RulePresentation.ruleMap_snd]
    rfl

def comparison : R.inference ⋙ Over.post K ≅ Over.post K ⋙ (mappedRules K R).inference :=
  NatIso.ofComponents (overIso K R) (by
    intro Q Q' f
    apply Over.OverMorphism.ext
    change K.map (Limits.Sigma.map (R.ruleMap f)) ≫ (sumIso K R Q').hom =
      (sumIso K R Q).hom ≫ Limits.Sigma.map ((mappedRules K R).ruleMap ((Over.post K).map f))
    apply mapSum_hom_ext K (R.ruleObject Q)
    intro i
    rw [← K.map_comp_assoc, Sigma.ι_map, K.map_comp_assoc, sumIso_iota_assoc,
      sumIso_iota, ← Category.assoc, branch_natural, Category.assoc]
    simp only [Sigma.ι_map])

abbrev algebra (B : Endofunctor.Algebra R.inference) :=
  AlgebraEvaluation.algebra (Over.post K) (comparison K R) B

theorem algebra_str (B : Endofunctor.Algebra R.inference) :
    (algebra K R B).str.left = (sumIso K R B.a).inv ≫ K.map B.str.left := rfl

section Transformations
variable (L : C ⥤ D) [PreservesFiniteLimits L] [PreservesFiniteCoproducts L]
variable (α : K ⟶ L)

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  [PreservesFiniteCoproducts K] [PreservesFiniteCoproducts L] in
@[reassoc] theorem power_transformation (X : C) (n : ℕ) :
    α.app (finitePower X n) ≫ (powerIso L X n).hom =
      (powerIso K X n).hom ≫ finitePowerMap (α.app X) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => simp [powerIso, finitePowerMap]; rfl
    | succ n =>
      have hp : α.app (finitePower X (n + 1) ⨯ X) ≫ prodComparison L _ _ =
          prodComparison K _ _ ≫ prod.map (α.app (finitePower X (n + 1))) (α.app X) := by
        apply prod.hom_ext
        · simpa only [Category.assoc, prodComparison_fst, prod.map_fst,
            prodComparison_fst_assoc] using (α.naturality prod.fst).symm
        · simpa only [Category.assoc, prodComparison_snd, prod.map_snd,
            prodComparison_snd_assoc] using (α.naturality prod.snd).symm
      simp only [powerIso, Iso.trans_hom, asIso_hom, prod.mapIso_hom, Iso.refl_hom,
        finitePowerMap]
      erw [← Category.assoc, hp, Category.assoc, prod.map_map, ih]
      simp only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id]

def relabelling : ForwardRuleRelabelling (mappedRules K R) (mappedRules L R) where
  formula := α.app F
  map i := α.app (R.instances i)
  premises i := by
    change α.app _ ≫ (L.map (R.premises i) ≫ _) = (K.map (R.premises i) ≫ _) ≫ _
    rw [← Category.assoc, ← α.naturality, Category.assoc, power_transformation, ← Category.assoc]
  conclusion i := (α.naturality (R.conclusion i)).symm

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  [PreservesFiniteCoproducts K] [PreservesFiniteCoproducts L] in
theorem branch_transformation (Q : Over F) (i : Fin (N + 1)) :
    α.app (R.ruleObject Q i) ≫ (ruleObjectIso L R Q i).hom =
      (ruleObjectIso K R Q i).hom ≫
        (relabelling K R L α).branch ((Over.post K).obj Q) ((Over.post L).obj Q)
          (α.app Q.left) (α.naturality Q.hom).symm i := by
  apply pullback.hom_ext
  · rw [Category.assoc, ruleObjectIso_fst, ← α.naturality,
      Category.assoc, ForwardRuleRelabelling.branch_fst, ← Category.assoc, ruleObjectIso_fst]
    rfl
  · rw [Category.assoc, ruleObjectIso_snd, ← Category.assoc, ← α.naturality,
      Category.assoc, power_transformation, ← Category.assoc, ← ruleObjectIso_snd]
    simp only [Category.assoc, ForwardRuleRelabelling.branch_snd]

/-- The complete inference comparison commutes with arbitrary natural
transformations. No equality-reflection property is required. -/
theorem sum_transformation (Q : Over F) :
    α.app (R.inference.obj Q).left ≫ (sumIso L R Q).hom =
      (sumIso K R Q).hom ≫
        (relabelling K R L α).input ((Over.post K).obj Q) ((Over.post L).obj Q)
          (α.app Q.left) (α.naturality Q.hom).symm := by
  apply mapSum_hom_ext K (R.ruleObject Q)
  intro i
  erw [← Category.assoc, α.naturality (Sigma.ι (R.ruleObject Q) i), Category.assoc, sumIso_iota,
    ← Category.assoc, branch_transformation, Category.assoc,
    ← ForwardRuleRelabelling.input_iota]
  simp only [← Category.assoc]
  erw [sumIso_iota]

/-- Naturality of every global algebra operation supplies its local constructor square; it
is not an extra compatibility hypothesis. -/
theorem algebra_transformation (B : Endofunctor.Algebra R.inference) :
    (relabelling K R L α).input (algebra K R B).a (algebra L R B).a
        (α.app B.a.left) (α.naturality B.a.hom).symm ≫ (algebra L R B).str.left =
      (algebra K R B).str.left ≫ α.app B.a.left := by
  rw [algebra_str, algebra_str]
  change (relabelling K R L α).input ((Over.post K).obj B.a) ((Over.post L).obj B.a)
      (α.app B.a.left) (α.naturality B.a.hom).symm ≫
      ((sumIso L R B.a).inv ≫ L.map B.str.left) =
    ((sumIso K R B.a).inv ≫ K.map B.str.left) ≫ α.app B.a.left
  apply (cancel_epi (sumIso K R B.a).hom).mp
  erw [← Category.assoc, ← sum_transformation, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (α.naturality B.str.left).symm
end Transformations
end CategoricalEssentialIncompleteness.V46.FiniteInferenceEvaluation
