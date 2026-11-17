/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46LaxAlgebraAdjunction
public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # Rule relabelling along arbitrary formula morphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46
variable {C : Type u} [Category.{v} C] [Regular C]
variable {F G H : C} {N : ℕ}

/-- The existing rule-translation type permits formula and label morphisms
that identify elements. The forward inference comparison uses that type. -/
abbrev ForwardRuleRelabelling (R : RulePresentation F N) (S : RulePresentation G N) :=
  RulePresentation.Translation R S

namespace ForwardRuleRelabelling
variable {R : RulePresentation F N} {S : RulePresentation G N} {T : RulePresentation H N}

abbrev base (χ : ForwardRuleRelabelling R S) := χ.formula
abbrev labels (χ : ForwardRuleRelabelling R S) := χ.map

@[ext] theorem ext {χ ψ : ForwardRuleRelabelling R S} (hb : χ.base = ψ.base)
    (hl : χ.labels = ψ.labels) : χ = ψ := by
  cases χ
  cases ψ
  cases hb
  cases hl
  rfl

abbrev identity (R : RulePresentation F N) : ForwardRuleRelabelling R R :=
  RulePresentation.Translation.id R

abbrev comp (χ : ForwardRuleRelabelling R S) (ψ : ForwardRuleRelabelling S T) :
    ForwardRuleRelabelling R T := RulePresentation.Translation.comp χ ψ

variable (χ : ForwardRuleRelabelling R S) (Q : Over F) (Q' : Over G)
variable (m : Q.left ⟶ Q'.left) (hm : m ≫ Q'.hom = Q.hom ≫ χ.base)

abbrev branch (i : Fin (N + 1)) : R.ruleObject Q i ⟶ S.ruleObject Q' i :=
  RulePresentation.Translation.mapRule χ m hm i

@[reassoc (attr := simp)] theorem branch_fst (i : Fin (N + 1)) :
    branch χ Q Q' m hm i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ χ.labels i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem branch_snd (i : Fin (N + 1)) :
    branch χ Q Q' m hm i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ finitePowerMap m i.val :=
  pullback.lift_snd _ _ _

theorem branch_conclusion (i : Fin (N + 1)) :
    branch χ Q Q' m hm i ≫ S.ruleConclusion Q' i = R.ruleConclusion Q i ≫ χ.base := by
  simp only [RulePresentation.ruleConclusion, branch_fst_assoc, χ.conclusion, Category.assoc]

variable [HasFiniteCoproducts C]

def input : (R.inference.obj Q).left ⟶ (S.inference.obj Q').left :=
  Limits.Sigma.map (branch χ Q Q' m hm)

@[reassoc (attr := simp)] theorem input_iota (i : Fin (N + 1)) :
    Sigma.ι (R.ruleObject Q) i ≫ input χ Q Q' m hm =
      branch χ Q Q' m hm i ≫ Sigma.ι (S.ruleObject Q') i := Sigma.ι_map _ _

theorem input_conclusion : input χ Q Q' m hm ≫ (S.inference.obj Q').hom =
    (R.inference.obj Q).hom ≫ χ.base := by
  apply Sigma.hom_ext
  intro i
  simp only [input_iota_assoc, RulePresentation.inference, Over.mk_hom,
    Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  exact branch_conclusion χ Q Q' m hm i

omit χ Q' m hm in
theorem input_identity : input (identity R) Q Q (𝟙 _) (by simp [identity, base, RulePresentation.Translation.id]) = 𝟙 _ := by
  change Limits.Sigma.map (branch (identity R) Q Q (𝟙 _) _) = 𝟙 (∐ R.ruleObject Q)
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_map, Category.comp_id]
  have hb : branch (identity R) Q Q (𝟙 _) (by simp [identity, base, RulePresentation.Translation.id]) i = 𝟙 _ := by
    exact RulePresentation.Translation.mapRule_id Q i
  rw [hb, Category.id_comp]

omit Q' m hm in
theorem input_comp (ψ : ForwardRuleRelabelling S T) (Q' : Over G) (Q'' : Over H)
    (m : Q.left ⟶ Q'.left) (n : Q'.left ⟶ Q''.left)
    (hm : m ≫ Q'.hom = Q.hom ≫ χ.base) (hn : n ≫ Q''.hom = Q'.hom ≫ ψ.base) :
    input χ Q Q' m hm ≫ input ψ Q' Q'' n hn =
      input (comp χ ψ) Q Q'' (m ≫ n) (by
        change (m ≫ n) ≫ Q''.hom = Q.hom ≫ (χ.base ≫ ψ.base)
        rw [Category.assoc, hn, ← Category.assoc m Q'.hom, hm, Category.assoc]) := by
  change Limits.Sigma.map _ ≫ Limits.Sigma.map _ = Limits.Sigma.map _
  rw [Limits.Sigma.map_comp_map]
  congr 1
  funext i
  exact (RulePresentation.Translation.mapRule_comp χ ψ m hm n hn i).symm

def comparison : R.inference ⋙ Over.map χ.base ⟶ Over.map χ.base ⋙ S.inference where
  app Q := Over.homMk (input χ Q ((Over.map χ.base).obj Q) (𝟙 _) (by simp))
    (input_conclusion χ Q ((Over.map χ.base).obj Q) (𝟙 _) (by simp))
  naturality {Q Q'} f := by
    apply Over.OverMorphism.ext
    change Limits.Sigma.map (R.ruleMap f) ≫
      Limits.Sigma.map (branch χ Q' ((Over.map χ.base).obj Q') (𝟙 _) _) =
      Limits.Sigma.map (branch χ Q ((Over.map χ.base).obj Q) (𝟙 _) _) ≫
        Limits.Sigma.map (S.ruleMap ((Over.map χ.base).map f))
    rw [Limits.Sigma.map_comp_map, Limits.Sigma.map_comp_map]
    congr 1
    funext i
    apply pullback.hom_ext <;> simp [branch, base, RulePresentation.Translation.mapRule,
      RulePresentation.ruleMap, Category.assoc]

@[reassoc] theorem input_factor : ((comparison χ).app Q).left ≫
    (S.inference.map (Over.homMk m hm : (Over.map χ.base).obj Q ⟶ Q')).left =
      input χ Q Q' m hm := by
  change Limits.Sigma.map (branch χ Q ((Over.map χ.base).obj Q) (𝟙 _) _) ≫
    Limits.Sigma.map (S.ruleMap (Over.homMk m hm)) = Limits.Sigma.map (branch χ Q Q' m hm)
  rw [Limits.Sigma.map_comp_map]
  congr 1
  funext i
  apply pullback.hom_ext <;> simp [branch, base, RulePresentation.Translation.mapRule,
      RulePresentation.ruleMap, Category.assoc]

omit m hm in
@[reassoc] theorem input_factor_hom (g : (Over.map χ.base).obj Q ⟶ Q') :
    ((comparison χ).app Q).left ≫ (S.inference.map g).left =
      input χ Q Q' g.left (Over.w g) := by
  simpa only [Over.homMk_eta] using input_factor χ Q Q' g.left (Over.w g)

variable (A : Endofunctor.Algebra R.inference) (hA : IsInitial A)
variable (B : Endofunctor.Algebra S.inference)

def fold : (Over.map χ.base).obj A.a ⟶ B.a :=
  LaxAlgebraAdjunction.fold (Over.mapPullbackAdj χ.base) (comparison χ) A hA B

theorem fold_constructor : input χ A.a B.a (fold χ A hA B).left (Over.w _) ≫ B.str.left =
    A.str.left ≫ (fold χ A hA B).left := by
  have h := congrArg Over.Hom.left
    (LaxAlgebraAdjunction.fold_constructor (Over.mapPullbackAdj χ.base) (comparison χ) A hA B)
  change ((comparison χ).app A.a).left ≫ (S.inference.map (fold χ A hA B)).left ≫
    B.str.left = A.str.left ≫ (fold χ A hA B).left at h
  rw [← Category.assoc, input_factor_hom] at h
  exact h

include hA in
/-- Uniqueness is among all underlying carrier morphisms preserving
the conclusion and constructors, without an injectivity hypothesis. -/
theorem unique (m n : A.a.left ⟶ B.a.left)
    (hm : m ≫ B.a.hom = A.a.hom ≫ χ.base) (hn : n ≫ B.a.hom = A.a.hom ≫ χ.base)
    (hc : input χ A.a B.a m hm ≫ B.str.left = A.str.left ≫ m)
    (hd : input χ A.a B.a n hn ≫ B.str.left = A.str.left ≫ n) : m = n := by
  apply congrArg Over.Hom.left
    (LaxAlgebraAdjunction.unique (Over.mapPullbackAdj χ.base) (comparison χ) A hA B
      (Over.homMk m hm) (Over.homMk n hn) ?_ ?_)
  · apply Over.OverMorphism.ext
    change ((comparison χ).app A.a).left ≫ (S.inference.map (Over.homMk m hm)).left ≫
      B.str.left = A.str.left ≫ m
    rw [← Category.assoc, input_factor]
    exact hc
  · apply Over.OverMorphism.ext
    change ((comparison χ).app A.a).left ≫ (S.inference.map (Over.homMk n hn)).left ≫
      B.str.left = A.str.left ≫ n
    rw [← Category.assoc, input_factor]
    exact hd
end ForwardRuleRelabelling
end CategoricalEssentialIncompleteness.V46
