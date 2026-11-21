/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Restriction
public import Mathlib.Computability.RE
public import Mathlib.Data.Set.Finite.Basic

/-!
# The numerical restriction category

Objects are infinite recursive subsets of `ℕ`. A morphism is a partial recursive
function on `ℕ` whose domain is contained in the source and whose values belong to the
target. Equality is equality of partial functions. Composition is diagrammatic.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness

/-- Partial identity on a support, with no decidability assumption. -/
def supportIdentity (A : Set ℕ) (n : ℕ) : Part ℕ :=
  Part.assert (n ∈ A) fun _ ↦ Part.some n

@[simp] theorem mem_supportIdentity (A : Set ℕ) (n m : ℕ) :
    m ∈ supportIdentity A n ↔ n ∈ A ∧ m = n := by
  simp [supportIdentity]

@[simp] theorem supportIdentity_dom (A : Set ℕ) (n : ℕ) :
    (supportIdentity A n).Dom ↔ n ∈ A := by
  simp [Part.dom_iff_mem]

theorem supportIdentity_partrec (A : Set ℕ) (hA : REPred (· ∈ A)) :
    Partrec (supportIdentity A) := by
  exact (hA.map Computable.fst.to₂).of_eq fun n ↦
    Part.ext fun m ↦ by simp [supportIdentity, eq_comm]

/-- The object class of the manuscript's numerical category. -/
structure Numerical where
  carrier : Set ℕ
  recursive : ComputablePred (· ∈ carrier)
  infinite : carrier.Infinite

namespace Numerical

/-- The distinguished numerical object. -/
def nat : Numerical where
  carrier := Set.univ
  recursive := by
    classical
    exact Computable.computablePred (by simpa using (Computable.const true :
      Computable fun _ : ℕ ↦ true))
  infinite := Set.infinite_univ

/-- Canonical extensional partial maps between numerical objects. -/
@[ext] structure Hom (X Y : Numerical) where
  val : ℕ → Part ℕ
  computable : Partrec val
  source : ∀ {n m}, m ∈ val n → n ∈ X.carrier
  target : ∀ {n m}, m ∈ val n → m ∈ Y.carrier

def identity (X : Numerical) : Hom X X where
  val := supportIdentity X.carrier
  computable := supportIdentity_partrec _ X.recursive.to_re
  source := by simp only [mem_supportIdentity]; exact fun h ↦ h.1
  target := by
    intro n m h
    rcases (mem_supportIdentity _ _ _).mp h with ⟨hn, rfl⟩
    exact hn

def compose {X Y Z : Numerical} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  val n := (f.val n).bind g.val
  computable := f.computable.bind (g.computable.comp Computable.snd).to₂
  source := by
    intro n m h
    obtain ⟨k, hk, _⟩ := Part.mem_bind_iff.mp h
    exact f.source hk
  target := by
    intro n m h
    obtain ⟨k, _, hk⟩ := Part.mem_bind_iff.mp h
    exact g.target hk

instance numericalCategory : Category Numerical where
  Hom := Hom
  id := identity
  comp := compose
  id_comp f := by
    apply Hom.ext
    funext n
    apply Part.ext
    intro m
    change m ∈ (supportIdentity _ n).bind f.val ↔ m ∈ f.val n
    rw [Part.mem_bind_iff]
    simp only [mem_supportIdentity]
    constructor
    · rintro ⟨k, ⟨_, rfl⟩, h⟩; exact h
    · intro h; exact ⟨n, ⟨f.source h, rfl⟩, h⟩
  comp_id f := by
    apply Hom.ext
    funext n
    apply Part.ext
    intro m
    change m ∈ (f.val n).bind (supportIdentity _) ↔ m ∈ f.val n
    rw [Part.mem_bind_iff]
    simp only [mem_supportIdentity]
    constructor
    · rintro ⟨k, h, _, rfl⟩; exact h
    · intro h; exact ⟨m, h, f.target h, rfl⟩
  assoc f g h := by
    apply Hom.ext
    funext n
    exact Part.bind_assoc (f.val n) g.val h.val

@[simp] theorem id_val (X : Numerical) (n : ℕ) :
    (𝟙 X : X ⟶ X).val n = supportIdentity X.carrier n := rfl

@[simp] theorem comp_val {X Y Z : Numerical} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (f ≫ g).val n = (f.val n).bind g.val := rfl

/-- Restriction is partial identity on the domain of a morphism. -/
def restrict {X Y : Numerical} (f : X ⟶ Y) : X ⟶ X where
  val := supportIdentity {n | (f.val n).Dom}
  computable := supportIdentity_partrec _ f.computable.dom_re
  source := by
    intro n m h
    obtain ⟨hn, _⟩ := (mem_supportIdentity _ _ _).mp h
    exact f.source (Part.get_mem hn)
  target := by
    intro n m h
    obtain ⟨hn, rfl⟩ := (mem_supportIdentity _ _ _).mp h
    exact f.source (Part.get_mem hn)

@[simp] theorem mem_restrict {X Y : Numerical} (f : X ⟶ Y) (n m : ℕ) :
    m ∈ (restrict f).val n ↔ (f.val n).Dom ∧ m = n := mem_supportIdentity _ _ _

instance numericalRestriction : RestrictionCategory Numerical where
  rst := restrict
  rst_comp_self f := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [comp_val, Part.mem_bind_iff, mem_restrict]
    constructor
    · rintro ⟨k, ⟨_, rfl⟩, h⟩; exact h
    · intro h; exact ⟨n, ⟨h.fst, rfl⟩, h⟩
  rst_comm f g := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [comp_val, Part.mem_bind_iff, mem_restrict]
    constructor <;> rintro ⟨k, ⟨hf, rfl⟩, hg, rfl⟩ <;>
      exact ⟨_, ⟨hg, rfl⟩, hf, rfl⟩
  rst_comp_rst f g := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [comp_val, mem_restrict, Part.dom_iff_mem, Part.mem_bind_iff]
    constructor
    · rintro ⟨⟨k, x, ⟨hf, rfl⟩, hg⟩, rfl⟩
      exact ⟨_, ⟨hf, rfl⟩, ⟨k, hg⟩, rfl⟩
    · rintro ⟨k, ⟨hf, rfl⟩, ⟨x, hg⟩, rfl⟩
      exact ⟨⟨x, _, ⟨hf, rfl⟩, hg⟩, rfl⟩
  rst_comp f g := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [comp_val, Part.mem_bind_iff, mem_restrict, Part.dom_iff_mem]
    constructor
    · rintro ⟨k, ⟨⟨x, y, hy, hx⟩, rfl⟩, hm⟩
      have heq := Part.mem_unique hy hm
      subst y
      exact ⟨m, hm, ⟨x, hx⟩, rfl⟩
    · rintro ⟨k, hk, ⟨x, hx⟩, rfl⟩
      exact ⟨n, ⟨⟨x, _, hk, hx⟩, rfl⟩, hk⟩

/-- Totality in the restriction category means defined at every source element. -/
theorem total_iff {X Y : Numerical} (f : X ⟶ Y) :
    RestrictionCategory.isTotal f ↔ ∀ n ∈ X.carrier, (f.val n).Dom := by
  constructor
  · intro h n hn
    have hm : n ∈ (restrict f).val n := by
      rw [show restrict f = 𝟙 X from h]
      exact (mem_supportIdentity _ _ _).mpr ⟨hn, rfl⟩
    exact (mem_restrict _ _ _).mp hm |>.1
  · intro h
    apply Hom.ext; funext n; apply Part.ext; intro m
    change m ∈ (restrict f).val n ↔ m ∈ supportIdentity X.carrier n
    rw [mem_restrict, mem_supportIdentity]
    constructor
    · rintro ⟨hd, rfl⟩; exact ⟨f.source (Part.get_mem hd), rfl⟩
    · rintro ⟨hn, rfl⟩; exact ⟨h _ hn, rfl⟩

instance {X Y : Numerical} : Zero (X ⟶ Y) where
  zero := ⟨fun _ ↦ Part.none, Partrec.none,
    fun h ↦ (Part.notMem_none _ h).elim, fun h ↦ (Part.notMem_none _ h).elim⟩

@[simp] theorem zero_val {X Y : Numerical} (n : ℕ) :
    (0 : X ⟶ Y).val n = Part.none := rfl

instance numericalZeroMorphisms : Limits.HasZeroMorphisms Numerical where
  zero_comp := by
    intro X Y Z f
    apply Hom.ext; funext n; exact Part.bind_none f.val
  comp_zero := by
    intro X Y Z f
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp

theorem restrict_zero (X Y : Numerical) :
    RestrictionCategory.rst (0 : X ⟶ Y) = 0 := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  change m ∈ (restrict (0 : X ⟶ Y)).val n ↔ m ∈ Part.none
  simp

theorem nat_nontrivial : (𝟙 nat : nat ⟶ nat) ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : nat ⟶ nat ↦ f.val 0) h
  have hm : 0 ∈ (𝟙 nat : nat ⟶ nat).val 0 :=
    (mem_supportIdentity _ _ _).mpr ⟨Set.mem_univ _, rfl⟩
  rw [h0] at hm
  exact Part.notMem_none _ hm

end Numerical
end CategoricalEssentialIncompleteness
