/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ClassicalRealization
import CategoricalEssentialIncompleteness.RestrictionSplitting

/-! # Computably enumerable carriers in the restriction splitting of `Rec` -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

open PartialFunctions

def ceObject (A : Set ℕ) (hA : REPred (· ∈ A)) : SplitObject Rec := ⟨U, supportIdem A hA⟩

def supportedArrow {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : ℕ → Part ℕ) (hf : Partrec f)
    (hs : ∀ x y, y ∈ f x → x ∈ A) (ht : ∀ x y, y ∈ f x → y ∈ B) :
    ceObject A hA ⟶ ceObject B hB where
  hom := omegaArrow f hf
  source := by
    apply J.map_injective
    rw [J.map_comp]
    apply PFun.ext
    intro x y
    change y ∈ (supportIdentity A x).bind f ↔ y ∈ f x
    rw [Part.mem_bind_iff]
    constructor
    · rintro ⟨z, hz, hy⟩
      obtain ⟨_, he⟩ := (mem_supportIdentity A x z).mp hz
      subst z
      exact hy
    · intro hy
      exact ⟨x, (mem_supportIdentity A x x).mpr ⟨hs x y hy, rfl⟩, hy⟩
  target := by
    apply J.map_injective
    rw [J.map_comp]
    apply PFun.ext
    intro x y
    change y ∈ (f x).bind (supportIdentity B) ↔ y ∈ f x
    rw [Part.mem_bind_iff]
    constructor
    · rintro ⟨z, hz, hy⟩
      obtain ⟨_, he⟩ := (mem_supportIdentity B z y).mp hy
      subst y
      exact hz
    · intro hy
      exact ⟨y, hy, (mem_supportIdentity B y y).mpr ⟨ht x y hy, rfl⟩⟩

def restrictedFunction (A : Set ℕ) (f : ℕ → ℕ) (x : ℕ) : Part ℕ :=
  (supportIdentity A x).map f

theorem restrictedFunction_partrec {A : Set ℕ} (hA : REPred (· ∈ A))
    {f : ℕ → ℕ} (hf : Computable f) : Partrec (restrictedFunction A f) :=
  (supportIdentity_partrec A hA).map (hf.comp Computable.snd).to₂

@[simp] theorem mem_restrictedFunction (A : Set ℕ) (f : ℕ → ℕ) (x y : ℕ) :
    y ∈ restrictedFunction A f x ↔ x ∈ A ∧ y = f x := by
  simp only [restrictedFunction, Part.mem_map_iff, mem_supportIdentity]
  aesop

def totalArrow {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : ℕ → ℕ) (hf : Computable f) (ht : ∀ x ∈ A, f x ∈ B) :
    ceObject A hA ⟶ ceObject B hB :=
  supportedArrow hA hB (restrictedFunction A f) (restrictedFunction_partrec hA hf)
    (fun x y h => ((mem_restrictedFunction A f x y).mp h).1)
    (fun x y h => by
      obtain ⟨hx, he⟩ := (mem_restrictedFunction A f x y).mp h
      exact he ▸ ht x hx)

theorem totalArrow_isTotal {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : ℕ → ℕ) (hf : Computable f) (ht : ∀ x ∈ A, f x ∈ B) :
    isTotal (totalArrow hA hB f hf ht) := by
  apply SplitObject.Hom.ext
  apply J.map_injective
  change J.map (rst (omegaArrow (restrictedFunction A f)
    (restrictedFunction_partrec hA hf))) = supportIdentity A
  rw [J_rst]
  apply PFun.ext
  intro x y
  rw [mem_rst]
  change (∃ z, z ∈ restrictedFunction A f x) ∧ y = x ↔ y ∈ supportIdentity A x
  rw [mem_supportIdentity]
  simp only [mem_restrictedFunction, exists_eq_right]

def parameterObject : SplitObject Rec := (splittingInclusion (C := Rec)).obj U

def totalFromU {B : Set ℕ} (hB : REPred (· ∈ B))
    (f : ℕ → ℕ) (hf : Computable f) (ht : ∀ x, f x ∈ B) : parameterObject ⟶ ceObject B hB where
  hom := omegaArrow (fun x => Part.some (f x)) hf.partrec
  source := Category.id_comp _
  target := by
    apply J.map_injective
    rw [J.map_comp]
    apply PFun.ext
    intro x y
    change y ∈ (Part.some (f x)).bind (supportIdentity B) ↔ y ∈ Part.some (f x)
    rw [Part.bind_some, Part.mem_some_iff]
    exact (mem_supportIdentity B (f x) y).trans (and_iff_right (ht x))

theorem totalFromU_isTotal {B : Set ℕ} (hB : REPred (· ∈ B))
    (f : ℕ → ℕ) (hf : Computable f) (ht : ∀ x, f x ∈ B) :
    isTotal (totalFromU hB f hf ht) := by
  apply SplitObject.Hom.ext
  apply J.map_injective
  change J.map (rst (omegaArrow (fun x => Part.some (f x)) hf.partrec)) = 𝟙 _
  rw [J_rst]
  apply PFun.ext
  intro x y
  rw [mem_rst, mem_id]
  exact and_iff_right ⟨f x, Part.mem_some (f x)⟩

/-- Supports of restriction idempotents on numerical split carriers. -/
def splitSupport {d : Idem U} (a : Idem (⟨U, d⟩ : SplitObject Rec)) : Set ℕ :=
  support (inclusionRangeFunctor.mapIdem (SplitObject.baseIdem a))

theorem splitSupport_injective {d : Idem U} :
    Function.Injective (splitSupport (d := d)) := by
  intro a b h
  apply SplitObject.baseIdem_injective
  apply Idem.ext
  apply J.map_injective
  exact congrArg Idem.hom (support_injective h)

theorem splitSupport_le_iff {d : Idem U} (a b : Idem (⟨U, d⟩ : SplitObject Rec)) :
    a ≤ b ↔ splitSupport a ⊆ splitSupport b := by
  rw [SplitObject.le_iff_base]
  constructor
  · intro h
    exact (le_iff_support _ _).mp (inclusionRangeFunctor.map_mono h)
  · intro h
    apply Idem.le_def.mpr
    apply J.map_injective
    rw [J.map_comp]
    exact Idem.le_def.mp ((le_iff_support _ _).mpr h)

@[simp] theorem splitSupport_inf {d : Idem U} (a b : Idem (⟨U, d⟩ : SplitObject Rec)) :
    splitSupport (a ⊓ b) = splitSupport a ∩ splitSupport b := by
  exact congrArg support (inclusionRangeFunctor.map_inf (SplitObject.baseIdem a)
    (SplitObject.baseIdem b)) |>.trans (support_inf _ _)

@[simp] theorem splitSupport_sup {d : Idem U} (a b : Idem (⟨U, d⟩ : SplitObject Rec)) :
    splitSupport (a ⊔ b) = splitSupport a ∪ splitSupport b := by
  exact congrArg support (inclusionRangeFunctor.map_sup (SplitObject.baseIdem a)
    (SplitObject.baseIdem b)) |>.trans (support_sup _ _)

@[simp] theorem splitSupport_bot {d : Idem U} :
    splitSupport (⊥ : Idem (⟨U, d⟩ : SplitObject Rec)) = ∅ := by
  change support (inclusionRangeFunctor.mapIdem (⊥ : Idem U)) = ∅
  rw [RangeFunctor.map_bot, support_bot]

@[simp] theorem splitSupport_top (d : Idem U) :
    splitSupport (⊤ : Idem (⟨U, d⟩ : SplitObject Rec)) = support (inclusionRangeFunctor.mapIdem d) := rfl

theorem splitSupport_pull {d e : Idem U}
    (f : (⟨U, d⟩ : SplitObject Rec) ⟶ (⟨U, e⟩ : SplitObject Rec))
    (a : Idem (⟨U, e⟩ : SplitObject Rec)) :
    splitSupport (Idem.pull f a) = {x | ∃ y, y ∈ J.map f.hom x ∧ y ∈ splitSupport a} := by
  change support (inclusionRangeFunctor.mapIdem (Idem.pull f.hom (SplitObject.baseIdem a))) = _
  rw [RangeFunctor.map_pull, support_pull]
  rfl

@[simp] theorem splitSupport_relative {A B : Set ℕ} (hA : REPred (· ∈ A))
    (hB : REPred (· ∈ B)) (h : A ⊆ B) :
    splitSupport (SplitObject.relativeIdem (supportIdem A hA) (supportIdem_le hA hB h)) = A := by
  change support (inclusionRangeFunctor.mapIdem (supportIdem A hA)) = A
  rw [supportIdem_image, support_setIdem]

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
