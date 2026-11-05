import CategoricalEssentialIncompleteness.V46SyntacticDerivationCheckedRoot
import CategoricalEssentialIncompleteness.V46SyntacticDerivationPolynomialComparison

/-! The original rule pullbacks under the canonical map to the judgement object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InputGeometry
variable {D : Type u} [Category.{v} D] [Regular D]
variable {F : D} {N : ℕ} (R : RulePresentation F N) (Q : Over F) (i : Fin (N + 1))

def toJudgement : Q ⟶ Over.mk (𝟙 F) := Over.homMk Q.hom (by simp)

theorem matching_isPullback :
    IsPullback (CheckedRoot.matchingMap R Q i) (R.ruleMap (toJudgement Q) i)
      (prod.map (𝟙 (R.instances i)) (finitePowerMap Q.hom i.val))
      (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply prod.hom_ext
    · simp [CheckedRoot.matchingMap, RulePresentation.ruleMap]
    · simp [CheckedRoot.matchingMap, RulePresentation.ruleMap, toJudgement]
  · intro X a b hab _
    apply pullback.hom_ext
    · have he := congrArg (fun k => k ≫ prod.fst) hab
      simpa only [Category.assoc, CheckedRoot.matchingMap, prod.lift_fst] using he
    · have he := congrArg (fun k => k ≫ prod.snd) hab
      simpa only [Category.assoc, CheckedRoot.matchingMap, prod.lift_snd] using he
  · intro X a b hab
    have he₁ : a ≫ prod.fst = b ≫ pullback.fst (R.premises i) (finitePowerMap (𝟙 F) i.val) := by
      have he := congrArg (fun k => k ≫ prod.fst) hab
      simpa [CheckedRoot.matchingMap] using he
    have he₂ : (a ≫ prod.snd) ≫ finitePowerMap Q.hom i.val =
        b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val) := by
      have he := congrArg (fun k => k ≫ prod.snd) hab
      simpa [CheckedRoot.matchingMap] using he
    have hw : (a ≫ prod.fst) ≫ R.premises i =
        (a ≫ prod.snd) ≫ finitePowerMap Q.hom i.val := by
      have hid : (b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val)) ≫
          finitePowerMap (𝟙 F) i.val = b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val) := by
        simpa only [Category.comp_id] using congrArg
          (fun k => (b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val)) ≫ k)
          (finitePowerMap_id F i.val)
      calc
        _ = (b ≫ pullback.fst (R.premises i) (finitePowerMap (𝟙 F) i.val)) ≫ R.premises i := by rw [he₁]
        _ = (b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val)) ≫
            finitePowerMap (𝟙 F) i.val := by rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = b ≫ pullback.snd (R.premises i) (finitePowerMap (𝟙 F) i.val) := hid
        _ = _ := he₂.symm
    refine ⟨pullback.lift (a ≫ prod.fst) (a ≫ prod.snd) hw, ?_, ?_⟩
    · apply prod.hom_ext <;> simp [CheckedRoot.matchingMap]
    · apply pullback.hom_ext
      · simpa [RulePresentation.ruleMap] using he₁
      · simpa [RulePresentation.ruleMap, toJudgement] using he₂

variable [HasFiniteCoproducts D]

/-- Forgetting premise matching retains the same rule label and the same
ordered child tuple in the ordinary tree polynomial. -/
def forget : (R.inference.obj Q).left ⟶ (PolynomialComparison.ordinary R).obj Q.left :=
  Sigma.desc (fun i => CheckedRoot.matchingMap R Q i ≫
    Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower Q.left i.val) i)

theorem forget_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (R.inference.map f).left ≫ forget R Q' =
      forget R Q ≫ (PolynomialComparison.ordinary R).map f.left := by
  apply Sigma.hom_ext
  intro i
  have hm : R.ruleMap f i ≫ CheckedRoot.matchingMap R Q' i =
      CheckedRoot.matchingMap R Q i ≫ prod.map (𝟙 _) (finitePowerMap f.left i.val) := by
    apply prod.hom_ext <;> simp [CheckedRoot.matchingMap, RulePresentation.ruleMap]
  simp only [RulePresentation.inference, Over.homMk_left, Sigma.ι_map_assoc,
    forget, Sigma.ι_comp_desc_assoc, PolynomialComparison.ordinary]
  simp only [Category.assoc, Sigma.ι_comp_desc, Sigma.ι_map]
  rw [← Category.assoc, hm, Category.assoc]

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InputGeometry
