/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalRecursion
import CategoricalEssentialIncompleteness.NumericalDomains
import CategoricalEssentialIncompleteness.PartialFunctions
import Foundation.Vorspiel.Computability

/-! # Ranges and joins in the classical numerical recursion category -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (zero_comp comp_zero)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalRecursion

open Numerical

/- The restriction induced by the numerical products is the existing
domain restriction (`Numerical.inducedRestriction_eq`). -/
attribute [instance 2000] Numerical.numericalRestriction

def oldDomain {X : Numerical} (a : Idem X) : Numerical.Domain X := ⟨a.hom, a.restriction⟩
def ofOldDomain {X : Numerical} (a : Numerical.Domain X) : Idem X := ⟨a.hom, a.isDomain⟩

def domainOrderIso (X : Numerical) : Idem X ≃o Numerical.Domain X where
  toFun := oldDomain
  invFun := ofOldDomain
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := (Numerical.Domain.le_iff _ _).trans Idem.le_def.symm

instance : RestrictionZero Numerical := ⟨Numerical.restrict_zero⟩

instance : BinaryJoins Numerical where
  join a b := ofOldDomain (oldDomain a ⊔ oldDomain b)
  le_left a b := (domainOrderIso _).symm.monotone
    (show oldDomain a ≤ oldDomain a ⊔ oldDomain b from le_sup_left)
  le_right a b := (domainOrderIso _).symm.monotone
    (show oldDomain b ≤ oldDomain a ⊔ oldDomain b from le_sup_right)
  least a b c ha hb := (domainOrderIso _).symm.monotone
    (sup_le ((domainOrderIso _).monotone ha) ((domainOrderIso _).monotone hb))

def support {X : Numerical} (a : Idem X) : Set ℕ := (oldDomain a).support

@[simp] theorem support_inf {X : Numerical} (a b : Idem X) :
    support (a ⊓ b) = support a ∩ support b := by
  exact congrArg Numerical.Domain.support ((domainOrderIso X).map_inf a b) |>.trans
    (Numerical.Domain.support_inf _ _)

@[simp] theorem support_sup {X : Numerical} (a b : Idem X) :
    support (a ⊔ b) = support a ∪ support b :=
  Numerical.Domain.support_sup (oldDomain a) (oldDomain b)

@[simp] theorem support_bot {X : Numerical} : support (⊥ : Idem X) = ∅ := by
  ext n
  change (Part.none : Part ℕ).Dom ↔ False
  rfl

@[simp] theorem support_top (X : Numerical) : support (⊤ : Idem X) = X.carrier :=
  Numerical.Domain.support_top X

theorem support_injective {X : Numerical} : Function.Injective (support (X := X)) :=
  fun _ _ h => (domainOrderIso X).injective (Numerical.Domain.support_injective X h)

theorem mem_idem {X : Numerical} (a : Idem X) (x y : ℕ) :
    y ∈ a.hom.val x ↔ x ∈ support a ∧ y = x := (oldDomain a).mem_iff x y

theorem support_le_iff {X : Numerical} (a b : Idem X) :
    a ≤ b ↔ support a ⊆ support b := (domainOrderIso X).map_rel_iff.symm

theorem partrec_graph_enumerable {f : ℕ → Part ℕ} (hf : Partrec f) :
    REPred (fun p : ℕ × ℕ => p.1 ∈ f p.2) := by
  have he : REPred (fun p : (ℕ × ℕ) × ℕ => p.2 = p.1.1) :=
    (Primrec.eq.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).computablePred.to_re
  have hk := ((hf.comp Computable.snd).bind he.to₂).dom_re
  apply hk.of_eq
  intro p
  rw [Part.bind_dom]
  change (∃ h : (f p.2).Dom, ∃ _ : (f p.2).get h = p.1, True) ↔ p.1 ∈ f p.2
  constructor
  · rintro ⟨h, he, _⟩
    exact he ▸ Part.get_mem h
  · intro h
    exact ⟨h.1, h.2, trivial⟩

theorem image_enumerable {X Y : Numerical} (f : X ⟶ Y) :
    REPred (fun y => ∃ x, y ∈ f.val x) := (partrec_graph_enumerable f.computable).projection

def range {X Y : Numerical} (f : X ⟶ Y) : Idem Y :=
  ofOldDomain (Numerical.domainOfSupport
    ⟨{y | ∃ x, y ∈ f.val x}, image_enumerable f, fun _ h => by
      obtain ⟨x, hx⟩ := h; exact f.target hx⟩)

@[simp] theorem mem_range {X Y : Numerical} (f : X ⟶ Y) (y z : ℕ) :
    z ∈ (range f).hom.val y ↔ (∃ x, y ∈ f.val x) ∧ z = y := mem_supportIdentity _ _ _

instance : Ranges Numerical where
  range := range
  receives f := by
    apply Numerical.Hom.ext
    funext x
    apply Part.ext
    intro y
    simp only [Numerical.comp_val, Part.mem_bind_iff, mem_range]
    constructor
    · rintro ⟨z, hz, _, rfl⟩; exact hz
    · intro h; exact ⟨y, h, ⟨x, h⟩, rfl⟩
  agreement f g h he := by
    have hagree (y : ℕ) (hy : ∃ x, y ∈ f.val x) : g.val y = h.val y := by
      obtain ⟨x, hx⟩ := hy
      have hf : f.val x = Part.some y := Part.eq_some_iff.mpr hx
      have hh := congrArg (fun k => k.val x) he
      simpa only [Numerical.comp_val, hf, Part.bind_some] using hh
    apply Numerical.Hom.ext
    funext y
    apply Part.ext
    intro z
    simp only [Numerical.comp_val, Part.mem_bind_iff, mem_range]
    constructor
    · rintro ⟨w, ⟨hw, he⟩, hz⟩
      subst w
      exact ⟨y, ⟨hw, rfl⟩, hagree y hw ▸ hz⟩
    · rintro ⟨w, ⟨hw, he⟩, hz⟩
      subst w
      exact ⟨y, ⟨hw, rfl⟩, (hagree y hw).symm ▸ hz⟩

theorem support_pull {X Y : Numerical} (f : X ⟶ Y) (a : Idem Y) :
    support (Idem.pull f a) = {x | ∃ y, y ∈ f.val x ∧ y ∈ support a} := by
  ext x
  change ((Numerical.restrict (f ≫ a.hom)).val x).Dom ↔ _
  simp only [Numerical.mem_restrict, Part.dom_iff_mem, Numerical.comp_val,
    Part.mem_bind_iff, mem_idem, Set.mem_setOf_eq]
  aesop

instance : JoinInverse Numerical where
  pull_sup f a b := by
    apply support_injective
    ext x
    simp only [support_pull, support_sup, Set.mem_union, Set.mem_setOf_eq]
    aesop

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalRecursion
