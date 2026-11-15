/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46Inference
public import CategoricalEssentialIncompleteness.V46RegularSlices
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Finite premise tuples in a parameter slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceFinitePowers
variable {D : Type u} [Category.{v} D] [Regular D] {P : D}
local instance : Regular (Over P) := RegularSlices.regular P

/-- Forget a tuple's common parameter, retaining every ordered coordinate. -/
def comparison (F : Over P) : (n : ℕ) → (finitePower F n).left ⟶ finitePower F.left n
  | 0 => terminal.from _
  | 1 => 𝟙 _
  | n + 2 => prod.lift
      ((prod.fst : finitePower F (n + 1) ⨯ F ⟶ _).left ≫ comparison F (n + 1))
      (prod.snd : finitePower F (n + 1) ⨯ F ⟶ F).left

theorem naturality {F G : Over P} (q : F ⟶ G) (n : ℕ) :
    (finitePowerMap q n).left ≫ comparison G n =
      comparison F n ≫ finitePowerMap q.left n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => simp [comparison, finitePowerMap]
    | succ n =>
      apply prod.hom_ext
      · simp only [comparison, finitePowerMap, Category.assoc, prod.lift_fst, prod.map_fst]
        have h := congrArg Over.Hom.left
          (prod.map_fst (finitePowerMap q (n + 1)) q)
        simp only [Over.comp_left] at h
        rw [← Category.assoc, h, Category.assoc, ih]
        simp only [← Category.assoc, prod.lift_fst]
      · simp only [comparison, finitePowerMap, Category.assoc, prod.lift_snd, prod.map_snd]
        rw [← Category.assoc, prod.lift_snd]
        exact congrArg Over.Hom.left (prod.map_snd (finitePowerMap q (n + 1)) q)

theorem hom_ext {X F : Over P} (n : ℕ) (f g : X ⟶ finitePower F n)
    (h : f.left ≫ comparison F n = g.left ≫ comparison F n) : f = g := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => apply Over.OverMorphism.ext; simpa only [comparison, Category.comp_id] using h
    | succ n =>
      apply prod.hom_ext
      · apply ih
        have hh := congrArg (fun t => t ≫ prod.fst) h
        simpa only [comparison, Category.assoc, prod.lift_fst, Over.comp_left] using hh
      · apply Over.OverMorphism.ext
        have hh := congrArg (fun t => t ≫ prod.snd) h
        simpa only [comparison, Category.assoc, prod.lift_snd, Over.comp_left] using hh

def liftOne {X F G : Over P} (q : F ⟶ G) (f : X.left ⟶ F.left) (k : X ⟶ G)
    (h : f ≫ q.left = k.left) : X ⟶ F :=
  Over.homMk f (by rw [← Over.w q, ← Category.assoc, h, Over.w k])

theorem left_condition {X F G : Over P} (q : F ⟶ G) (n : ℕ)
    (f : X.left ⟶ finitePower F.left (n + 2)) (k : X ⟶ finitePower G (n + 2))
    (h : f ≫ finitePowerMap q.left (n + 2) = k.left ≫ comparison G (n + 2)) :
    (f ≫ prod.fst) ≫ finitePowerMap q.left (n + 1) =
      (k ≫ prod.fst).left ≫ comparison G (n + 1) := by
  have hh := congrArg (fun t => t ≫ prod.fst) h
  simpa only [finitePowerMap, Category.assoc, prod.map_fst, comparison,
    prod.lift_fst, Over.comp_left] using hh

theorem right_condition {X F G : Over P} (q : F ⟶ G) (n : ℕ)
    (f : X.left ⟶ finitePower F.left (n + 2)) (k : X ⟶ finitePower G (n + 2))
    (h : f ≫ finitePowerMap q.left (n + 2) = k.left ≫ comparison G (n + 2)) :
    (f ≫ prod.snd) ≫ q.left = (k ≫ prod.snd).left := by
  have hh := congrArg (fun t => t ≫ prod.snd) h
  simpa only [finitePowerMap, Category.assoc, prod.map_snd, comparison,
    prod.lift_snd, Over.comp_left] using hh

/-- Matching conclusion labels force all child parameters to agree.
This constructs the relative tuple from an ordinary matching tuple. -/
def lift {X F G : Over P} (q : F ⟶ G) : (n : ℕ) →
    (f : X.left ⟶ finitePower F.left n) → (k : X ⟶ finitePower G n) →
    (h : f ≫ finitePowerMap q.left n = k.left ≫ comparison G n) → X ⟶ finitePower F n
  | 0, _, _, _ => terminal.from X
  | 1, f, k, h => liftOne q f k (by simpa only [finitePowerMap, comparison, Category.comp_id] using h)
  | n + 2, f, k, h => prod.lift
      (lift q (n + 1) (f ≫ prod.fst) (k ≫ prod.fst) (left_condition q n f k h))
      (liftOne q (f ≫ prod.snd) (k ≫ prod.snd) (right_condition q n f k h))

theorem lift_value {X F G : Over P} (q : F ⟶ G) (n : ℕ)
    (f : X.left ⟶ finitePower F.left n) (k : X ⟶ finitePower G n)
    (h : f ≫ finitePowerMap q.left n = k.left ≫ comparison G n) :
    (lift q n f k h).left ≫ comparison F n = f := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => exact Category.comp_id _
    | succ n =>
      apply prod.hom_ext
      · simp only [lift, comparison, Category.assoc, prod.lift_fst]
        have hh := congrArg Over.Hom.left (prod.lift_fst
          (lift q (n + 1) (f ≫ prod.fst) (k ≫ prod.fst) (left_condition q n f k h))
          (liftOne q (f ≫ prod.snd) (k ≫ prod.snd) (right_condition q n f k h)))
        simp only [Over.comp_left] at hh
        rw [← Category.assoc, hh]
        exact ih _ _ _
      · simp only [lift, comparison, Category.assoc, prod.lift_snd]
        exact congrArg Over.Hom.left (prod.lift_snd _ _)

theorem lift_map {X F G : Over P} (q : F ⟶ G) (n : ℕ)
    (f : X.left ⟶ finitePower F.left n) (k : X ⟶ finitePower G n)
    (h : f ≫ finitePowerMap q.left n = k.left ≫ comparison G n) :
    lift q n f k h ≫ finitePowerMap q n = k := by
  apply hom_ext n
  change ((lift q n f k h).left ≫ (finitePowerMap q n).left) ≫ comparison G n = _
  rw [Category.assoc, naturality, ← Category.assoc, lift_value, h]

end CategoricalEssentialIncompleteness.V46.SliceFinitePowers
