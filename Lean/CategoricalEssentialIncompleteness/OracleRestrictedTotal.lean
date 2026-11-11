/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedPCategory

/-! # Exactly the ordinary total recursive functions are total source arrows -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}
attribute [instance 2000] nativeRestriction

theorem total_iff {X Y : Restricted S} (f : X ⟶ Y) :
    isTotal f ↔ ∀ x,(f.val x).Dom := by
  constructor
  · intro ht x
    have h : x ∈ (rst f).val x := by
      rw [show rst f=𝟙 X from ht]
      exact Part.mem_some x
    exact ((mem_identityOn X {x | (f.val x).Dom} f.domain x x).mp h).1
  · intro ht
    apply hom_ext_mem
    intro x y
    change y ∈ (identityOn X {x | (f.val x).Dom} f.domain).val x ↔ y ∈ (Part.some x)
    rw [mem_identityOn]
    change (f.val x).Dom ∧ y=x ↔ y ∈ Part.some x
    simp only [ht x,true_and,Part.mem_some_iff]

theorem totalFromFunction_total {X Y : Restricted S}
    (f : carrier S X → carrier S Y) (hf : Computable f) : isTotal (totalFromFunction f hf) :=
  (total_iff _).mpr (fun x => Part.some_dom (f x))

theorem total_val_partrec {X Y : Restricted S} (f : X ⟶ Y) (ht : isTotal f) : Partrec f.val := by
  obtain ⟨f₀,hf,he⟩ := f.extension
  apply hf.of_eq
  intro x
  apply Part.ext
  intro y
  simpa only [(total_iff f).mp ht x,true_and] using (he.mem_iff x y).symm

def totalValue {X Y : Restricted S} (f : X ⟶ Y) (ht : isTotal f) (x : carrier S X) : carrier S Y :=
  (f.val x).get ((total_iff f).mp ht x)

theorem totalValue_computable {X Y : Restricted S} (f : X ⟶ Y) (ht : isTotal f) :
    Computable (totalValue f ht) :=
  (total_val_partrec f ht).of_eq_tot (fun _ => Part.get_mem _)

/-- This uses an ordinary partial recursive extension and totality on the
entire formal carrier. No computability of the oracle is assumed. -/
theorem total_iff_ordinary_total {X Y : Restricted S} (f : X ⟶ Y) :
    isTotal f ↔ ∃ g : carrier S X → carrier S Y,Computable g ∧
      f.val=fun x => Part.some (g x) := by
  constructor
  · intro ht
    exact ⟨totalValue f ht,totalValue_computable f ht,
      funext (fun _ => Part.eq_some_iff.mpr (Part.get_mem _))⟩
  · rintro ⟨g,hg,he⟩
    apply (total_iff f).mpr
    intro x
    rw [he]
    exact Part.some_dom (g x)

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
