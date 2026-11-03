/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46RegularImage
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The inference endofunctor of a finite typed rule presentation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D]

omit [Regular D] in
/-- A monic conclusion inclusion admits at most one closure structure. -/
theorem closed_structure_unique {F : D} (H : Over F ⥤ Over F) {T : D} (m : T ⟶ F)
    [Mono m] (α β : H.obj (Over.mk m) ⟶ Over.mk m) : α = β := by
  apply Over.OverMorphism.ext
  apply (cancel_mono m).mp
  exact (Over.w α).trans (Over.w β).symm

/-- Finite powers use `X^0 = 1`, `X^1 = X`, and
`X^(n+2) = X^(n+1) × X`. -/
def finitePower (X : D) : ℕ → D
  | 0 => ⊤_ D
  | 1 => X
  | n + 2 => finitePower X (n + 1) ⨯ X

def finitePowerMap {X Y : D} (f : X ⟶ Y) : (n : ℕ) → finitePower X n ⟶ finitePower Y n
  | 0 => 𝟙 _
  | 1 => f
  | n + 2 => prod.map (finitePowerMap f (n + 1)) f

@[simp] theorem finitePowerMap_id (X : D) (n : ℕ) :
    finitePowerMap (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [finitePowerMap, ih, prod.map_id_id]
      rfl

@[simp] theorem finitePowerMap_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    finitePowerMap (f ≫ g) n = finitePowerMap f n ≫ finitePowerMap g n := by
  induction n with
  | zero => simp [finitePowerMap]
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [finitePowerMap, ih, prod.map_map]

theorem prod_map_regularEpi {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsRegularEpi f] [IsRegularEpi g] : IsRegularEpi (prod.map f g) := by
  have hleft : IsRegularEpi (prod.map f (𝟙 Y)) := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id f Y)
    change IsRegularEpi f
    infer_instance
  have hright : IsRegularEpi (prod.map (𝟙 X') g) := by
    have h : IsRegularEpi (prod.map g (𝟙 X')) := by
      apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback
        (IsPullback.of_prod_fst_with_id g X')
      change IsRegularEpi g
      infer_instance
    have heq : prod.map (𝟙 X') g =
        (prod.braiding X' Y).hom ≫ prod.map g (𝟙 X') ≫
          (prod.braiding Y' X').hom := by
      apply prod.hom_ext <;> simp
    rw [heq]
    infer_instance
  have heq : prod.map f g = prod.map f (𝟙 Y) ≫ prod.map (𝟙 X') g := by
    apply prod.hom_ext <;> simp
  rw [heq]
  infer_instance

theorem finitePowerMap_regularEpi {X Y : D} (f : X ⟶ Y) [IsRegularEpi f] (n : ℕ) :
    IsRegularEpi (finitePowerMap f n) := by
  induction n with
  | zero => dsimp [finitePowerMap]; infer_instance
  | succ n ih =>
    cases n with
    | zero => change IsRegularEpi f; infer_instance
    | succ n => exact prod_map_regularEpi (finitePowerMap f (n + 1)) f

/-- Coproducts preserve regular epimorphisms in a regular category. -/
theorem sigma_map_regularEpi {I : Type} {X Y : I → D}
    [HasCoproduct X] [HasCoproduct Y] (e : ∀ i, X i ⟶ Y i)
    (he : ∀ i, IsRegularEpi (e i)) : IsRegularEpi (Limits.Sigma.map e) := by
  let : ∀ i, IsRegularEpi (e i) := he
  have : Epi (Limits.Sigma.map e) := inferInstance
  have : StrongEpi (Limits.Sigma.map e) := by
    apply StrongEpi.mk'
    intro U V m hm u v sq
    let component (i : I) : CommSq (Sigma.ι X i ≫ u) (e i) m (Sigma.ι Y i ≫ v) :=
      ⟨by simpa using congrArg (fun k => Sigma.ι X i ≫ k) sq.w⟩
    refine CommSq.HasLift.mk' ⟨Sigma.desc (fun i => (component i).lift), ?_, ?_⟩
    · apply Sigma.hom_ext
      intro i
      simp [CommSq.fac_left]
    · apply Sigma.hom_ext
      intro i
      simp [CommSq.fac_right]
  infer_instance

/-- A finite collection of typed rules, with exactly `i.val` ordered
premises in its `i`th component. -/
structure RulePresentation (F : D) (N : ℕ) where
  instances : Fin (N + 1) → D
  premises : ∀ i, instances i ⟶ finitePower F i.val
  conclusion : ∀ i, instances i ⟶ F

namespace RulePresentation

variable {F : D} {N : ℕ} (R : RulePresentation F N)

/-- A map of rule instances preserves their ordered premises and conclusions. -/
structure Hom (R R' : RulePresentation F N) where
  map : ∀ i, R.instances i ⟶ R'.instances i
  premises : ∀ i, map i ≫ R'.premises i = R.premises i
  conclusion : ∀ i, map i ≫ R'.conclusion i = R.conclusion i

def ruleObject (Q : Over F) (i : Fin (N + 1)) : D :=
  pullback (R.premises i) (finitePowerMap Q.hom i.val)

def ruleConclusion (Q : Over F) (i : Fin (N + 1)) : R.ruleObject Q i ⟶ F :=
  pullback.fst _ _ ≫ R.conclusion i

def ruleMap {Q Q' : Over F} (h : Q ⟶ Q') (i : Fin (N + 1)) :
    R.ruleObject Q i ⟶ R.ruleObject Q' i :=
  pullback.map _ _ _ _ (𝟙 _) (finitePowerMap h.left i.val) (𝟙 _)
    (by simp) (by rw [Category.comp_id, ← finitePowerMap_comp, Over.w h])

/-- With no premises, every rule instance is available independently
of the conclusion subobject. -/
def nullaryRule (Q : Over F) : R.instances 0 ⟶ R.ruleObject Q 0 :=
  pullback.lift (𝟙 _) (R.premises 0) (by simp [finitePowerMap])

@[simp, reassoc (attr := simp)] theorem nullaryRule_fst (Q : Over F) :
    R.nullaryRule Q ≫ pullback.fst _ _ = 𝟙 _ := by
  simp [nullaryRule]

@[simp, reassoc (attr := simp)] theorem ruleMap_fst {Q Q' : Over F} (h : Q ⟶ Q') (i : Fin (N + 1)) :
    R.ruleMap h i ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [ruleMap]

@[simp, reassoc (attr := simp)] theorem ruleMap_snd {Q Q' : Over F} (h : Q ⟶ Q') (i : Fin (N + 1)) :
    R.ruleMap h i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap h.left i.val := by
  simp [ruleMap]

@[simp] theorem ruleMap_id (Q : Over F) (i : Fin (N + 1)) :
    R.ruleMap (𝟙 Q) i = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

@[simp] theorem ruleMap_comp {Q Q' Q'' : Over F} (h : Q ⟶ Q') (k : Q' ⟶ Q'')
    (i : Fin (N + 1)) : R.ruleMap (h ≫ k) i = R.ruleMap h i ≫ R.ruleMap k i := by
  apply pullback.hom_ext <;> simp [finitePowerMap_comp, Category.assoc]

/-- Each rule component sends a morphism of conclusion objects to a
pullback of its morphism on premise tuples. -/
theorem ruleMap_isPullback {Q Q' : Over F} (h : Q ⟶ Q') (i : Fin (N + 1)) :
    IsPullback (R.ruleMap h i) (pullback.snd _ _)
      (pullback.snd _ _) (finitePowerMap h.left i.val) := by
  refine IsPullback.mk' (R.ruleMap_snd h i) ?_ ?_
  · intro Z u v h₀ h₁
    apply pullback.hom_ext
    · have h' := congrArg (fun k => k ≫ pullback.fst
        (R.premises i) (finitePowerMap Q'.hom i.val)) h₀
      simpa using h'
    · exact h₁
  · intro Z a b hab
    have hw : (a ≫ pullback.fst (R.premises i) (finitePowerMap Q'.hom i.val)) ≫
        R.premises i = b ≫ finitePowerMap Q.hom i.val := by
      calc
        _ = (a ≫ pullback.snd _ _) ≫ finitePowerMap Q'.hom i.val := by
          simp only [Category.assoc, pullback.condition]
        _ = _ := by rw [hab, Category.assoc, ← finitePowerMap_comp, Over.w h]
    refine ⟨pullback.lift (a ≫ pullback.fst _ _) b hw, ?_, by simp⟩
    apply pullback.hom_ext <;> simp [← hab]

theorem ruleMap_regularEpi {Q Q' : Over F} (h : Q ⟶ Q')
    [IsRegularEpi h.left] (i : Fin (N + 1)) : IsRegularEpi (R.ruleMap h i) := by
  have := finitePowerMap_regularEpi h.left i.val
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback
    (R.ruleMap_isPullback h i).flip
  change IsRegularEpi (finitePowerMap h.left i.val)
  infer_instance

section Coproduct

variable [HasFiniteCoproducts D]

def inference : Over F ⥤ Over F where
  obj Q := Over.mk (Sigma.desc (R.ruleConclusion Q))
  map {Q Q'} h := Over.homMk (Limits.Sigma.map (R.ruleMap h)) (by
    apply Sigma.hom_ext
    intro i
    simp [ruleConclusion])
  map_id Q := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    simp
  map_comp h k := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    simp

/-- The pullback-and-coproduct rule endofunctor preserves the regular
epimorphisms needed to descend the initial derivation algebra. -/
theorem inference_preservesRegularEpis :
    PreservesUnderlyingRegularEpis R.inference := by
  intro Q Q' h hh
  have := hh
  change IsRegularEpi (Limits.Sigma.map (R.ruleMap h))
  exact sigma_map_regularEpi (R.ruleMap h) (fun i => R.ruleMap_regularEpi h i)

/-- Every closed subobject contains the conclusions of all nullary
rule instances, including the axioms. -/
theorem closed_contains_nullary {T : D} (m : T ⟶ F)
    (α : R.inference.obj (Over.mk m) ⟶ Over.mk m) :
    ∃ a : R.instances 0 ⟶ T, a ≫ m = R.conclusion 0 := by
  refine ⟨R.nullaryRule (Over.mk m) ≫ Sigma.ι (R.ruleObject (Over.mk m)) 0 ≫ α.left, ?_⟩
  have hα : α.left ≫ m = Sigma.desc (R.ruleConclusion (Over.mk m)) := Over.w α
  rw [Category.assoc, Category.assoc, hα]
  simp [ruleConclusion, nullaryRule]

/-- Theorem A.5 for the typed finitary inference endofunctor. -/
theorem least_theorem_subobject (A : Endofunctor.Algebra R.inference)
    (hA : IsInitial A) :
    ClosedUnder R.inference (image.ι A.a.hom) ∧
      ∀ {U : D} (m : U ⟶ F) [Mono m], ClosedUnder R.inference m →
        ∃ w : image A.a.hom ⟶ U, w ≫ m = image.ι A.a.hom :=
  least_closed_image R.inference A R.inference_preservesRegularEpis hA

namespace Hom

variable {R R' : RulePresentation F N} (ι : Hom R R')

def mapRule (Q : Over F) (i : Fin (N + 1)) : R.ruleObject Q i ⟶ R'.ruleObject Q i :=
  pullback.map _ _ _ _ (ι.map i) (𝟙 _) (𝟙 _)
    (by simpa using (ι.premises i).symm) (by simp)

omit [HasFiniteCoproducts D] in
@[simp, reassoc (attr := simp)] theorem mapRule_fst (Q : Over F) (i : Fin (N + 1)) :
    ι.mapRule Q i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ι.map i := by
  simp [mapRule]

omit [HasFiniteCoproducts D] in
@[simp, reassoc (attr := simp)] theorem mapRule_snd (Q : Over F) (i : Fin (N + 1)) :
    ι.mapRule Q i ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [mapRule]

omit [HasFiniteCoproducts D] in
theorem mapRule_natural {Q Q' : Over F} (h : Q ⟶ Q') (i : Fin (N + 1)) :
    R.ruleMap h i ≫ ι.mapRule Q' i = ι.mapRule Q i ≫ R'.ruleMap h i := by
  apply pullback.hom_ext <;> simp

/-- A map of typed rules induces a natural transformation of the
inference endofunctors. -/
def inferenceTransformation : R.inference ⟶ R'.inference where
  app Q := Over.homMk (Limits.Sigma.map (ι.mapRule Q)) (by
    change Limits.Sigma.map (ι.mapRule Q) ≫ Sigma.desc (R'.ruleConclusion Q) =
      Sigma.desc (R.ruleConclusion Q)
    apply Sigma.hom_ext
    intro i
    simp [ruleConclusion, ι.conclusion])
  naturality {Q Q'} h := by
    apply Over.OverMorphism.ext
    change Limits.Sigma.map (R.ruleMap h) ≫ Limits.Sigma.map (ι.mapRule Q') =
      Limits.Sigma.map (ι.mapRule Q) ≫ Limits.Sigma.map (R'.ruleMap h)
    rw [Limits.Sigma.map_comp_map, Limits.Sigma.map_comp_map]
    congr 1
    funext i
    exact ι.mapRule_natural h i

end Hom

end Coproduct

end RulePresentation

end CategoricalEssentialIncompleteness.V46
