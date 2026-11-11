/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Inference
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # Translation of finite derivations

A translation of rule presentations maps formula objects and rule labels,
preserving the ordered premises and conclusion of each rule. Pulling an
algebra back along its formula morphism gives an algebra for the source
rules. Initiality then translates finite derivations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RulePresentation

variable {D : Type u} [Category.{v} D] [Regular D]
variable {F G : D} {N : ℕ}

/-- Rule labels may change, while their arities and ordered premises are
preserved by the formula morphism. -/
structure Translation (R : RulePresentation F N) (R' : RulePresentation G N) where
  formula : F ⟶ G
  map : ∀ i, R.instances i ⟶ R'.instances i
  premises : ∀ i, map i ≫ R'.premises i = R.premises i ≫ finitePowerMap formula i.val
  conclusion : ∀ i, map i ≫ R'.conclusion i = R.conclusion i ≫ formula

namespace Translation

def id (R : RulePresentation F N) : Translation R R where
  formula := 𝟙 F
  map _ := 𝟙 _
  premises i := by simp
  conclusion i := by simp

def comp {H : D} {R : RulePresentation F N} {R' : RulePresentation G N}
    {R'' : RulePresentation H N} (τ : Translation R R') (σ : Translation R' R'') :
    Translation R R'' where
  formula := τ.formula ≫ σ.formula
  map i := τ.map i ≫ σ.map i
  premises i := by
    rw [Category.assoc, σ.premises, ← Category.assoc, τ.premises,
      Category.assoc, ← finitePowerMap_comp]
  conclusion i := by
    rw [Category.assoc, σ.conclusion, ← Category.assoc, τ.conclusion, Category.assoc]

variable {R : RulePresentation F N} {R' : RulePresentation G N}
variable (τ : Translation R R')

def mapRule {Q : Over F} {Q' : Over G} (f : Q.left ⟶ Q'.left)
    (hf : f ≫ Q'.hom = Q.hom ≫ τ.formula) (i : Fin (N + 1)) :
    R.ruleObject Q i ⟶ R'.ruleObject Q' i :=
  pullback.lift (pullback.fst _ _ ≫ τ.map i)
    (pullback.snd _ _ ≫ finitePowerMap f i.val) (by
      simp only [Category.assoc, τ.premises]
      rw [← Category.assoc, pullback.condition, Category.assoc,
        ← finitePowerMap_comp, ← hf, finitePowerMap_comp])

@[simp, reassoc (attr := simp)] theorem mapRule_fst
    {Q : Over F} {Q' : Over G} (f : Q.left ⟶ Q'.left)
    (hf : f ≫ Q'.hom = Q.hom ≫ τ.formula) (i : Fin (N + 1)) :
    τ.mapRule f hf i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.map i := by
  simp [mapRule]

@[simp, reassoc (attr := simp)] theorem mapRule_snd
    {Q : Over F} {Q' : Over G} (f : Q.left ⟶ Q'.left)
    (hf : f ≫ Q'.hom = Q.hom ≫ τ.formula) (i : Fin (N + 1)) :
    τ.mapRule f hf i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap f i.val := by
  simp [mapRule]

@[reassoc] theorem mapRule_conclusion
    {Q : Over F} {Q' : Over G} (f : Q.left ⟶ Q'.left)
    (hf : f ≫ Q'.hom = Q.hom ≫ τ.formula) (i : Fin (N + 1)) :
    τ.mapRule f hf i ≫ R'.ruleConclusion Q' i =
      R.ruleConclusion Q i ≫ τ.formula := by
  simp only [ruleConclusion, mapRule_fst_assoc, τ.conclusion, Category.assoc]

theorem mapRule_precomp {Q Q₁ : Over F} {Q' : Over G} (h : Q ⟶ Q₁)
    (f : Q₁.left ⟶ Q'.left) (hf : f ≫ Q'.hom = Q₁.hom ≫ τ.formula)
    (i : Fin (N + 1)) :
    R.ruleMap h i ≫ τ.mapRule f hf i =
      τ.mapRule (h.left ≫ f)
        (by rw [Category.assoc, hf, ← Category.assoc, Over.w h]) i := by
  apply pullback.hom_ext <;> simp [finitePowerMap_comp, Category.assoc]

theorem mapRule_comp {H : D} {R'' : RulePresentation H N} (σ : Translation R' R'')
    {Q : Over F} {Q' : Over G} {Q'' : Over H}
    (f : Q.left ⟶ Q'.left) (hf : f ≫ Q'.hom = Q.hom ≫ τ.formula)
    (g : Q'.left ⟶ Q''.left) (hg : g ≫ Q''.hom = Q'.hom ≫ σ.formula)
    (i : Fin (N + 1)) :
    (τ.comp σ).mapRule (f ≫ g)
        (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]; rfl) i =
      τ.mapRule f hf i ≫ σ.mapRule g hg i := by
  apply pullback.hom_ext <;> simp [comp, finitePowerMap_comp, Category.assoc]

theorem mapRule_id (Q : Over F) (i : Fin (N + 1)) :
    (id R).mapRule (𝟙 Q.left) (by simp [id]) i = 𝟙 (R.ruleObject Q i) := by
  apply pullback.hom_ext <;> simp [id]

def reindex (Q : Over G) : Over F := Over.mk (pullback.snd Q.hom τ.formula)

variable [HasFiniteCoproducts D]

def step (Q : Endofunctor.Algebra R'.inference) (i : Fin (N + 1)) :
    R.ruleObject (τ.reindex Q.a) i ⟶ Q.a.left :=
  τ.mapRule (pullback.fst Q.a.hom τ.formula) pullback.condition i ≫
    Sigma.ι (R'.ruleObject Q.a) i ≫ Q.str.left

@[reassoc] theorem step_conclusion
    (Q : Endofunctor.Algebra R'.inference) (i : Fin (N + 1)) :
    τ.step Q i ≫ Q.a.hom = R.ruleConclusion (τ.reindex Q.a) i ≫ τ.formula := by
  have h := Over.w Q.str
  change Q.str.left ≫ Q.a.hom = Sigma.desc (R'.ruleConclusion Q.a) at h
  simp only [step, Category.assoc, h, Sigma.ι_comp_desc]
  exact τ.mapRule_conclusion _ _ i

/-- The algebra on the pullback includes the formula coordinate; it does
not identify premises with the conclusion of their parent. -/
def reindexAlgebra (Q : Endofunctor.Algebra R'.inference) :
    Endofunctor.Algebra R.inference where
  a := τ.reindex Q.a
  str := Over.homMk
    (Sigma.desc (fun i => pullback.lift (τ.step Q i)
      (R.ruleConclusion (τ.reindex Q.a) i) (τ.step_conclusion Q i))) (by
        change Sigma.desc _ ≫ pullback.snd Q.a.hom τ.formula = Sigma.desc _
        apply Sigma.hom_ext
        intro i
        simp)

/-- Inverse image along a rule translation preserves closure under the
source inference rules. The algebra on the inverse image is constructed
from the rule equations. -/
theorem closed_pullback {B : D} (m : B ⟶ G) (hm : ClosedUnder R'.inference m) :
    ClosedUnder R.inference (pullback.snd m τ.formula) := by
  obtain ⟨α⟩ := hm
  let Q : Endofunctor.Algebra R'.inference := ⟨Over.mk m, α⟩
  exact ⟨(τ.reindexAlgebra Q).str⟩

@[reassoc] theorem reindexAlgebra_str_fst
    (Q : Endofunctor.Algebra R'.inference) :
    (τ.reindexAlgebra Q).str.left ≫ pullback.fst Q.a.hom τ.formula =
      Limits.Sigma.map (τ.mapRule (pullback.fst Q.a.hom τ.formula)
        pullback.condition) ≫ Q.str.left := by
  apply Sigma.hom_ext
  intro i
  simp [reindexAlgebra, step]

def fold (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) : P.a.left ⟶ Q.a.left :=
  (hP.to (τ.reindexAlgebra Q)).f.left ≫ pullback.fst Q.a.hom τ.formula

@[reassoc] theorem fold_conclusion
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    τ.fold P hP Q ≫ Q.a.hom = P.a.hom ≫ τ.formula := by
  have h := Over.w (hP.to (τ.reindexAlgebra Q)).f
  change (hP.to (τ.reindexAlgebra Q)).f.left ≫
    pullback.snd Q.a.hom τ.formula = P.a.hom at h
  unfold fold
  rw [Category.assoc, pullback.condition, ← Category.assoc, h]

theorem fold_constructor
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    P.str.left ≫ τ.fold P hP Q =
      Limits.Sigma.map (τ.mapRule (τ.fold P hP Q) (τ.fold_conclusion P hP Q)) ≫
        Q.str.left := by
  let m := hP.to (τ.reindexAlgebra Q)
  have h := congrArg Over.Hom.left m.h
  change Limits.Sigma.map (R.ruleMap m.f) ≫ (τ.reindexAlgebra Q).str.left =
    P.str.left ≫ m.f.left at h
  change P.str.left ≫ (m.f.left ≫ pullback.fst Q.a.hom τ.formula) = _
  rw [← Category.assoc, ← h, Category.assoc, reindexAlgebra_str_fst,
    ← Category.assoc, Limits.Sigma.map_comp_map]
  congr 2
  funext i
  exact τ.mapRule_precomp m.f _ _ i

/-- A constructor-preserving morphism lifts to a morphism into the
pullback algebra. Its formula coordinate is the source conclusion. -/
def liftAlgebraHom
    (P : Endofunctor.Algebra R.inference) (Q : Endofunctor.Algebra R'.inference)
    (f : P.a.left ⟶ Q.a.left) (hf : f ≫ Q.a.hom = P.a.hom ≫ τ.formula)
    (hc : P.str.left ≫ f = Limits.Sigma.map (τ.mapRule f hf) ≫ Q.str.left) :
    P ⟶ τ.reindexAlgebra Q := by
  let lifted : P.a ⟶ τ.reindex Q.a :=
    Over.homMk (pullback.lift f P.a.hom hf) (by simp [reindex])
  have hm : (fun i => R.ruleMap lifted i ≫
      τ.mapRule (pullback.fst Q.a.hom τ.formula) pullback.condition i) =
      τ.mapRule f hf := by
    funext i
    apply pullback.hom_ext <;> simp [lifted, ← finitePowerMap_comp, Category.assoc]
  refine ⟨lifted, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (Limits.Sigma.map (R.ruleMap lifted) ≫ (τ.reindexAlgebra Q).str.left) ≫
        pullback.fst Q.a.hom τ.formula =
      (P.str.left ≫ lifted.left) ≫ pullback.fst Q.a.hom τ.formula
    rw [Category.assoc, reindexAlgebra_str_fst, ← Category.assoc,
      Limits.Sigma.map_comp_map, hm, ← hc]
    simp [lifted]
  · exact (Over.w (R.inference.map lifted ≫ (τ.reindexAlgebra Q).str)).trans
      (Over.w (P.str ≫ lifted)).symm

theorem fold_unique
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference)
    (f : P.a.left ⟶ Q.a.left) (hf : f ≫ Q.a.hom = P.a.hom ≫ τ.formula)
    (hc : P.str.left ≫ f = Limits.Sigma.map (τ.mapRule f hf) ≫ Q.str.left) :
    f = τ.fold P hP Q := by
  have h := hP.hom_ext (τ.liftAlgebraHom P Q f hf hc) (hP.to (τ.reindexAlgebra Q))
  have h' := congrArg (fun k : P ⟶ τ.reindexAlgebra Q =>
    k.f.left ≫ pullback.fst Q.a.hom τ.formula) h
  simpa [liftAlgebraHom, fold] using h'

theorem fold_comp {H : D} {R'' : RulePresentation H N} (σ : Translation R' R'')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) (hQ : IsInitial Q)
    (Q' : Endofunctor.Algebra R''.inference) :
    (τ.comp σ).fold P hP Q' = τ.fold P hP Q ≫ σ.fold Q hQ Q' := by
  symm
  apply (τ.comp σ).fold_unique P hP Q' _
    (by rw [Category.assoc, σ.fold_conclusion, ← Category.assoc,
      τ.fold_conclusion, Category.assoc]; rfl)
  rw [← Category.assoc, τ.fold_constructor, Category.assoc, σ.fold_constructor,
    ← Category.assoc, Limits.Sigma.map_comp_map]
  congr 2
  funext i
  exact (τ.mapRule_comp σ _ (τ.fold_conclusion P hP Q)
    _ (σ.fold_conclusion Q hQ Q') i).symm

theorem fold_id (P : Endofunctor.Algebra R.inference) (hP : IsInitial P) :
    (id R).fold P hP P = 𝟙 P.a.left := by
  symm
  apply (id R).fold_unique P hP P _ (by simp [id])
  have hm : Limits.Sigma.map ((id R).mapRule (𝟙 P.a.left) (by simp [id])) =
      𝟙 (∐ (R.ruleObject P.a)) := by
    apply Sigma.hom_ext
    intro i
    simp [mapRule_id]
  rw [hm, Category.comp_id, Category.id_comp]

theorem image_le (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    imageSubobject (P.a.hom ≫ τ.formula) ≤ imageSubobject Q.a.hom := by
  rw [← τ.fold_conclusion P hP Q]
  exact imageSubobject_comp_le _ _

/-- The formula translation restricts to sentence conclusions whenever
the sentence morphisms commute with it. -/
def sentenceMap {S S' : D} (sentence : S ⟶ F) (sentence' : S' ⟶ G)
    (s : S ⟶ S') (hs : sentence ≫ τ.formula = s ≫ sentence')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    pullback P.a.hom sentence ⟶ pullback Q.a.hom sentence' :=
  pullback.map _ _ _ _ (τ.fold P hP Q) s τ.formula
    (τ.fold_conclusion P hP Q).symm hs

@[reassoc] theorem sentenceMap_conclusion {S S' : D}
    (sentence : S ⟶ F) (sentence' : S' ⟶ G)
    (s : S ⟶ S') (hs : sentence ≫ τ.formula = s ≫ sentence')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    τ.sentenceMap sentence sentence' s hs P hP Q ≫ pullback.snd Q.a.hom sentence' =
      pullback.snd P.a.hom sentence ≫ s := by
  simp [sentenceMap]

theorem sentenceImage_le {S S' : D}
    (sentence : S ⟶ F) (sentence' : S' ⟶ G)
    (s : S ⟶ S') (hs : sentence ≫ τ.formula = s ≫ sentence')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R'.inference) :
    imageSubobject (pullback.snd P.a.hom sentence ≫ s) ≤
      imageSubobject (pullback.snd Q.a.hom sentence') := by
  rw [← τ.sentenceMap_conclusion sentence sentence' s hs P hP Q]
  exact imageSubobject_comp_le _ _

end Translation
end CategoricalEssentialIncompleteness.V46.RulePresentation
