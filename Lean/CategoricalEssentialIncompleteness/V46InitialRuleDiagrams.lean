/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46FiniteInferenceEvaluation

/-! # Natural initial derivation diagrams from component initial algebras -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.InitialRuleDiagrams
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [Regular C] [HasFiniteCoproducts C] [Regular (J ⥤ C)]
variable {F : J ⥤ C} {N : ℕ} (R : RulePresentation F N)
abbrev evaluation (j : J) := (CategoryTheory.evaluation J C).obj j
abbrev rules (j : J) := FiniteRuleTransport.mappedRules (evaluation j) R
abbrev relabelling {j k : J} (f : j ⟶ k) :=
  FiniteInferenceEvaluation.relabelling (evaluation j) R (evaluation k)
    ((CategoryTheory.evaluation J C).map f)

omit [HasFiniteCoproducts C] in
theorem relabelling_id (j : J) : relabelling R (𝟙 j) = ForwardRuleRelabelling.identity (rules R j) := by
  apply ForwardRuleRelabelling.ext
  · exact F.map_id j
  · exact funext (fun i => (R.instances i).map_id j)

omit [HasFiniteCoproducts C] in
theorem relabelling_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    (relabelling R f).comp (relabelling R g) = relabelling R (f ≫ g) := by
  apply ForwardRuleRelabelling.ext
  · exact (F.map_comp f g).symm
  · exact funext (fun n => ((R.instances n).map_comp f g).symm)

variable (A : ∀ j, Endofunctor.Algebra (rules R j).inference) (hA : ∀ j, IsInitial (A j))

def transition {j k : J} (f : j ⟶ k) : (A j).a.left ⟶ (A k).a.left :=
  ((relabelling R f).fold (A j) (hA j) (A k)).left

theorem transition_conclusion {j k : J} (f : j ⟶ k) :
    transition R A hA f ≫ (A k).a.hom = (A j).a.hom ≫ F.map f := Over.w _

theorem transition_constructor {j k : J} (f : j ⟶ k) :
    (relabelling R f).input (A j).a (A k).a (transition R A hA f)
        (transition_conclusion R A hA f) ≫ (A k).str.left =
      (A j).str.left ≫ transition R A hA f :=
  ForwardRuleRelabelling.fold_constructor (relabelling R f) (A j) (hA j) (A k)

theorem transition_id (j : J) : transition R A hA (𝟙 j) = 𝟙 _ := by
  refine ForwardRuleRelabelling.unique (relabelling R (𝟙 j)) (A j) (hA j) (A j)
    _ (𝟙 _) (transition_conclusion R A hA _) ?_ (transition_constructor R A hA _) ?_
  · change (𝟙 _) ≫ (A j).a.hom = (A j).a.hom ≫ F.map (𝟙 j)
    simp
  · simp only [relabelling_id, ForwardRuleRelabelling.input_identity, Category.id_comp, Category.comp_id]

theorem transition_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    transition R A hA (f ≫ g) = transition R A hA f ≫ transition R A hA g := by
  refine ForwardRuleRelabelling.unique (relabelling R (f ≫ g)) (A i) (hA i) (A k)
    _ _ (transition_conclusion R A hA _) ?_ (transition_constructor R A hA _) ?_
  · change (transition R A hA f ≫ transition R A hA g) ≫ (A k).a.hom =
      (A i).a.hom ≫ F.map (f ≫ g)
    rw [Category.assoc, transition_conclusion, ← Category.assoc, transition_conclusion,
      Category.assoc, F.map_comp]
  · have hc := ForwardRuleRelabelling.input_comp (relabelling R f) (A i).a (relabelling R g)
      (A j).a (A k).a (transition R A hA f) (transition R A hA g)
      (transition_conclusion R A hA f) (transition_conclusion R A hA g)
    simp only [relabelling_comp] at hc
    rw [← hc]
    rw [Category.assoc, transition_constructor, ← Category.assoc, transition_constructor,
      Category.assoc]

def carrier : J ⥤ C where
  obj j := (A j).a.left
  map f := transition R A hA f
  map_id := transition_id R A hA
  map_comp := transition_comp R A hA

def conclusion : carrier R A hA ⟶ F where
  app j := (A j).a.hom
  naturality {_ _} f := transition_conclusion R A hA f

def source : Over F := Over.mk (conclusion R A hA)

def constructorComponent (j : J) : ((R.inference.obj (source R A hA)).left).obj j ⟶
    (carrier R A hA).obj j :=
  (FiniteInferenceEvaluation.sumIso (evaluation j) R (source R A hA)).hom ≫ (A j).str.left

theorem constructor_natural {j k : J} (f : j ⟶ k) :
    ((R.inference.obj (source R A hA)).left).map f ≫ constructorComponent R A hA k =
      constructorComponent R A hA j ≫ (carrier R A hA).map f := by
  dsimp only [constructorComponent]
  erw [← Category.assoc, FiniteInferenceEvaluation.sum_transformation (evaluation j) R
    (evaluation k) ((CategoryTheory.evaluation J C).map f) (source R A hA), Category.assoc]
  change _ ≫ ((relabelling R f).input (A j).a (A k).a (transition R A hA f) _ ≫
    (A k).str.left) = _
  rw [transition_constructor, ← Category.assoc]
  rfl

def algebra : Endofunctor.Algebra R.inference where
  a := source R A hA
  str := Over.homMk {
    app j := constructorComponent R A hA j
    naturality {_ _} f := constructor_natural R A hA f } (by
      apply NatTrans.ext
      funext j
      change constructorComponent R A hA j ≫ (A j).a.hom = _
      rw [constructorComponent, Category.assoc, Over.w (A j).str]
      exact Over.w (FiniteInferenceEvaluation.overIso (evaluation j) R (source R A hA)).hom)

def sourceIso (j : J) : FiniteInferenceEvaluation.algebra (evaluation j) R (algebra R A hA) ≅ A j :=
  Endofunctor.Algebra.isoMk (Over.isoMk (Iso.refl _) (by simp; rfl)) (by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, FiniteInferenceEvaluation.algebra_str]
    change (Limits.Sigma.map ((rules R j).ruleMap
      (Over.homMk (𝟙 _) (by exact Category.id_comp _)))) ≫ (A j).str.left =
      ((FiniteInferenceEvaluation.sumIso (evaluation j) R (source R A hA)).inv ≫
        ((FiniteInferenceEvaluation.sumIso (evaluation j) R (source R A hA)).hom ≫
          (A j).str.left)) ≫ 𝟙 _
    simp only [Category.comp_id, Iso.inv_hom_id_assoc]
    have hb (i : Fin (N + 1)) :
        (rules R j).ruleMap (Over.homMk (𝟙 _) (by exact Category.id_comp _) :
          (Over.post (evaluation j)).obj (source R A hA) ⟶ (A j).a) i =
          𝟙 ((rules R j).ruleObject (A j).a i) := by
      apply pullback.hom_ext
      · erw [RulePresentation.ruleMap_fst, Category.id_comp]
        rfl
      · erw [RulePresentation.ruleMap_snd]
        change (pullback.snd ((rules R j).premises i) (finitePowerMap (A j).a.hom i.val)) ≫
          finitePowerMap (𝟙 (A j).a.left) i.val = 𝟙 _ ≫
            pullback.snd ((rules R j).premises i) (finitePowerMap (A j).a.hom i.val)
        rw [finitePowerMap_id, Category.comp_id, Category.id_comp]
    have hs : Limits.Sigma.map ((rules R j).ruleMap
        (Over.homMk (𝟙 _) (by exact Category.id_comp _) :
          (Over.post (evaluation j)).obj (source R A hA) ⟶ (A j).a)) =
          𝟙 (∐ (rules R j).ruleObject (A j).a) := by
      apply Sigma.hom_ext
      intro i
      erw [Sigma.ι_map, hb, Category.id_comp, Category.comp_id]
      rfl
    erw [hs, Category.id_comp])

def componentInitial (j : J) : IsInitial
    (FiniteInferenceEvaluation.algebra (evaluation j) R (algebra R A hA)) :=
  (hA j).ofIso (sourceIso R A hA j).symm

abbrev componentFold (B : Endofunctor.Algebra R.inference) (j : J) :=
  (hA j).to (FiniteInferenceEvaluation.algebra (evaluation j) R B)

theorem fold_natural (B : Endofunctor.Algebra R.inference) {j k : J} (f : j ⟶ k) :
    transition R A hA f ≫ (componentFold R A hA B k).f.left =
      (componentFold R A hA B j).f.left ≫ B.a.left.map f := by
  let t : (Over.map (F.map f)).obj (FiniteInferenceEvaluation.algebra (evaluation j) R B).a ⟶
      (FiniteInferenceEvaluation.algebra (evaluation k) R B).a :=
    Over.homMk (B.a.left.map f) (B.a.hom.naturality f)
  have ht : ((relabelling R f).comparison).app
        (FiniteInferenceEvaluation.algebra (evaluation j) R B).a ≫
      (rules R k).inference.map t ≫ (FiniteInferenceEvaluation.algebra (evaluation k) R B).str =
    (Over.map (F.map f)).map (FiniteInferenceEvaluation.algebra (evaluation j) R B).str ≫ t := by
    apply Over.OverMorphism.ext
    change ((relabelling R f).comparison.app _).left ≫ ((rules R k).inference.map t).left ≫
      _ = _
    rw [← Category.assoc, ForwardRuleRelabelling.input_factor_hom]
    exact FiniteInferenceEvaluation.algebra_transformation (evaluation j) R (evaluation k)
      ((CategoryTheory.evaluation J C).map f) B
  exact congrArg Over.Hom.left (LaxAlgebraAdjunction.fold_natural
    (Over.mapPullbackAdj (F.map f)) (relabelling R f).comparison
    (A j) (FiniteInferenceEvaluation.algebra (evaluation j) R B) (hA j)
    (A k) (FiniteInferenceEvaluation.algebra (evaluation k) R B)
    ((relabelling R f).fold (A j) (hA j) (A k)) t
    (LaxAlgebraAdjunction.fold_constructor _ _ _ _ _) ht
    (componentFold R A hA B j) (componentFold R A hA B k))

def foldMap (B : Endofunctor.Algebra R.inference) : (algebra R A hA).a ⟶ B.a :=
  Over.homMk {
    app j := (componentFold R A hA B j).f.left
    naturality {_ _} f := fold_natural R A hA B f }
    (by ext j; exact Over.w (componentFold R A hA B j).f)

theorem fold_constructor (B : Endofunctor.Algebra R.inference) :
    R.inference.map (foldMap R A hA B) ≫ B.str = (algebra R A hA).str ≫ foldMap R A hA B := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext j
  let m := (sourceIso R A hA j).hom ≫ componentFold R A hA B j
  have he : (Over.post (evaluation j)).map (foldMap R A hA B) = m.f := by
    apply Over.OverMorphism.ext
    change _ = (𝟙 _) ≫ (componentFold R A hA B j).f.left
    rw [Category.id_comp]
    rfl
  exact congrArg Over.Hom.left ((AlgebraEvaluation.hom_condition_iff (Over.post (evaluation j))
    (FiniteInferenceEvaluation.comparison (evaluation j) R) (algebra R A hA) B _).mp
      (by rw [he]; exact m.h))

def fold (B : Endofunctor.Algebra R.inference) : algebra R A hA ⟶ B :=
  ⟨foldMap R A hA B, fold_constructor R A hA B⟩

/-- All global target families and all natural algebra morphisms are
included. The local initiality assumptions are discharged numerically. -/
def initial : IsInitial (algebra R A hA) :=
  IsInitial.ofUniqueHom (fold R A hA) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    exact congrArg (fun n => n.f.left) ((componentInitial R A hA j).hom_ext
      (⟨(Over.post (evaluation j)).map m.f,
        (AlgebraEvaluation.hom_condition_iff (Over.post (evaluation j))
          (FiniteInferenceEvaluation.comparison (evaluation j) R) (algebra R A hA) B m.f).mpr
            (congrArg (Over.post (evaluation j)).map m.h)⟩ :
          FiniteInferenceEvaluation.algebra (evaluation j) R (algebra R A hA) ⟶
            FiniteInferenceEvaluation.algebra (evaluation j) R B)
      (⟨(Over.post (evaluation j)).map (fold R A hA B).f,
        (AlgebraEvaluation.hom_condition_iff (Over.post (evaluation j))
          (FiniteInferenceEvaluation.comparison (evaluation j) R) (algebra R A hA) B _).mpr
            (congrArg (Over.post (evaluation j)).map (fold R A hA B).h)⟩ :
          FiniteInferenceEvaluation.algebra (evaluation j) R (algebra R A hA) ⟶
            FiniteInferenceEvaluation.algebra (evaluation j) R B)))
end CategoricalEssentialIncompleteness.V46.InitialRuleDiagrams
