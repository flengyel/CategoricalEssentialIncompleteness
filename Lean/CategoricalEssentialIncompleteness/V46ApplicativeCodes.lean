/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TuringObjectRecognition

/-! # Codes for morphisms on the finite powers of a Turing object

In Cockett and Hofstra, Definition 4.2, a code is a total point. Iterated application
must be total up to the penultimate argument. At arity zero the code is applied to itself.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open CategoryTheory PCategoryStruct PCategory RecursionCategory RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (terminal : ∀ X : C, X ⟶ Z)

/-- The power with one distinguished last factor. Its exponent is one more than the index. -/
def positivePower (A : C) : ℕ → C
  | 0 => A
  | n + 1 => nearProd (positivePower A n) A

/-- Iterated application of a code point to the coordinates of a nonempty tuple. -/
def applyPositive (p : Z ⟶ A) : (n : ℕ) → positivePower A n ⟶ A
  | 0 => partialPairing (terminal A ≫ p) (𝟙 A) ≫ app
  | n + 1 => nearProd_map (applyPositive p n) (𝟙 A) ≫ app

def power (Z A : C) : ℕ → C
  | 0 => Z
  | n + 1 => positivePower A n

/-- A code satisfies the equality of partial morphisms and the prefix-totality
condition of Cockett and Hofstra, Definition 4.2(i). -/
def Codes (p : Z ⟶ A) : (n : ℕ) → (power Z A n ⟶ A) → Prop
  | 0, f => isTotal p ∧ p ≫ diag A ≫ app = f
  | 1, f => isTotal p ∧ applyPositive app terminal p 0 = f
  | n + 2, f => isTotal p ∧ isTotal (applyPositive app terminal p n) ∧
      applyPositive app terminal p (n + 1) = f

private theorem code_partial_point (h : IsTuringMorphism app) (f : Z ⟶ A) :
    ∃ p : Z ⟶ A, isTotal p ∧ p ≫ diag A ≫ app = f := by
  obtain ⟨p, hp, eqn⟩ := h Z (p0 Z A ≫ f)
  refine ⟨p, hp, ?_⟩
  have e := congrArg (fun k => partialPairing (𝟙 Z) p ≫ k) eqn
  simp only [← Category.assoc, partialPairing_comp_nearProd_map, Category.id_comp,
    Category.comp_id, p0_partialPairing_of_isTotal _ hp] at e
  have d : p ≫ diag A = partialPairing p p := by
    rw [← partialPairing_id_id, comp_partialPairing, Category.comp_id]
  simpa only [← Category.assoc, d] using e

private theorem code_unary (h : IsTuringMorphism app)
    (ht : isTotal (terminal A)) (f : A ⟶ A) :
    ∃ p : Z ⟶ A, isTotal p ∧ applyPositive app terminal p 0 = f := by
  obtain ⟨p, hp, eqn⟩ := h Z (p1 Z A ≫ f)
  refine ⟨p, hp, ?_⟩
  have e := congrArg (fun k => partialPairing (terminal A) (𝟙 A) ≫ k) eqn
  simpa only [applyPositive, positivePower, ← Category.assoc, partialPairing_comp_nearProd_map,
    Category.comp_id, p1_partialPairing_of_isTotal _ ht, Category.id_comp] using e

private theorem code_positive (h : IsTuringMorphism app)
    (ht : isTotal (terminal A)) (n : ℕ) (f : positivePower A n ⟶ A) :
    ∃ p : Z ⟶ A, isTotal p ∧ applyPositive app terminal p n = f ∧
      ∀ k, n = k + 1 → isTotal (applyPositive app terminal p k) := by
  induction n with
  | zero =>
    obtain ⟨p, hp, eqn⟩ := code_unary app terminal h ht f
    exact ⟨p, hp, eqn, fun k he => Nat.noConfusion he⟩
  | succ n ih =>
    obtain ⟨g, hg, curry⟩ := h (positivePower A n) f
    obtain ⟨p, hp, eqn, _⟩ := ih g
    refine ⟨p, hp, ?_, ?_⟩
    · simpa only [applyPositive, positivePower, eqn] using curry
    · intro k hk
      cases Nat.succ.inj hk
      simpa only [eqn] using hg

/-- For a Turing application every morphism from a finite power into A has a total
point as code, with its full domain and totality through the penultimate argument. -/
theorem exists_code (h : IsTuringMorphism app) (ht : isTotal (terminal A))
    (n : ℕ) (f : power Z A n ⟶ A) : ∃ p : Z ⟶ A, Codes app terminal p n f := by
  cases n with
  | zero => exact code_partial_point app h f
  | succ n =>
    obtain ⟨p, hp, eqn, hprefix⟩ := code_positive app terminal h ht n f
    cases n with
    | zero => exact ⟨p, hp, eqn⟩
    | succ k => exact ⟨p, hp, hprefix k rfl, eqn⟩

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
