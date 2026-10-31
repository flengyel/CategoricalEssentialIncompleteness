/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleRestrictedPCategory

/-! # Oracle-c.e. subdomains have finite joins and exact inverse images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}
attribute [instance 2000] nativeRestriction

def support {X : Restricted S} (a : Idem X) : Set (carrier S X) := {x | (a.hom.val x).Dom}

theorem support_re {X : Restricted S} (a : Idem X) : FiniteOracleRE S (· ∈ support a) := a.hom.domain

theorem mem_idem {X : Restricted S} (a : Idem X) (x y : carrier S X) :
    y ∈ a.hom.val x ↔ x ∈ support a ∧ y=x := PartialFunctions.mem_idem (toPfnIdem a) x y

theorem le_iff_pfn {X : Restricted S} (a b : Idem X) :
    a ≤ b ↔ toPfnIdem a ≤ toPfnIdem b := by
  constructor
  · intro h
    exact congrArg Arrow.val h
  · intro h
    exact Arrow.ext h

theorem support_le_iff {X : Restricted S} (a b : Idem X) :
    a ≤ b ↔ support a ⊆ support b :=
  (le_iff_pfn a b).trans (PartialFunctions.le_iff_support (toPfnIdem a) (toPfnIdem b))

@[simp] theorem toPfnIdem_setIdem (X : Restricted S) (A : Set (carrier S X))
    (hA : FiniteOracleRE S (· ∈ A)) : toPfnIdem (setIdem X A hA)=PartialFunctions.setIdem A := rfl

@[simp] theorem support_setIdem (X : Restricted S) (A : Set (carrier S X))
    (hA : FiniteOracleRE S (· ∈ A)) : support (setIdem X A hA)=A := by
  change PartialFunctions.support (toPfnIdem (setIdem X A hA))=A
  rw [toPfnIdem_setIdem,PartialFunctions.support_setIdem]

instance : BinaryJoins (Restricted S) where
  join a b := setIdem _ (support a ∪ support b) ((support_re a).or (support_re b))
  le_left a b := (support_le_iff _ _).mpr (by
    rw [support_setIdem]; exact Set.subset_union_left)
  le_right a b := (support_le_iff _ _).mpr (by
    rw [support_setIdem]; exact Set.subset_union_right)
  least a b c ha hb := (support_le_iff _ _).mpr (by
    rw [support_setIdem]
    exact Set.union_subset ((support_le_iff _ _).mp ha) ((support_le_iff _ _).mp hb))

@[simp] theorem toPfnIdem_sup {X : Restricted S} (a b : Idem X) :
    toPfnIdem (a ⊔ b)=toPfnIdem a ⊔ toPfnIdem b := by
  apply Idem.ext
  apply PFun.ext
  intro x y
  change y ∈ (identityOn X (support a ∪ support b) ((support_re a).or (support_re b))).val x ↔
    y ∈ (toPfnIdem a ⊔ toPfnIdem b).hom x
  rw [mem_identityOn,PartialFunctions.mem_idem,PartialFunctions.support_sup]
  rfl

@[simp] theorem toPfnIdem_inf {X : Restricted S} (a b : Idem X) :
    toPfnIdem (a ⊓ b)=toPfnIdem a ⊓ toPfnIdem b := rfl

@[simp] theorem toPfnIdem_top {X : Restricted S} :
    toPfnIdem (⊤ : Idem X)=⊤ := rfl

@[simp] theorem toPfnIdem_bot {X : Restricted S} :
    toPfnIdem (⊥ : Idem X)=⊥ := rfl

@[simp] theorem toPfnIdem_pull {X Y : Restricted S} (f : X ⟶ Y) (a : Idem Y) :
    toPfnIdem (Idem.pull f a)=Idem.pull f.val (toPfnIdem a) := rfl

instance : JoinInverse (Restricted S) where
  pull_sup f a b := by
    apply toPfnIdem_injective
    rw [toPfnIdem_pull,toPfnIdem_sup,JoinInverse.pull_sup,toPfnIdem_sup,
      toPfnIdem_pull,toPfnIdem_pull]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
