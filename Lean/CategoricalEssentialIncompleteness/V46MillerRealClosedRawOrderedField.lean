/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedRawStructure
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.RelClasses

/-! # Constructing the ordered field from the literal finite matrices

The selected inverse uses only the actual existential inverse matrix.
All primitive field operations and strict order retain the interpretation's
original values. No field or order instance is supplied as a premise.
-/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
universe u
variable {K : Type u} (M : Interpretation K) (hM : MatricesValid M)

def inverseValue (x : K) : K := by
  classical
  exact if hx : x=zeroValue M then zeroValue M
    else Classical.choose ((matrix_consequences M hM).inverse_exists x hx)

/-- A field on the original carrier, built from the original sixteen
matrix consequences using the pinned minimal-axiom constructor. -/
@[instance_reducible] def fieldStructure : Field K := by
  let h := matrix_consequences M hM
  letI : Zero K := ⟨zeroValue M⟩
  letI : One K := ⟨oneValue M⟩
  letI : Add K := ⟨addValue M⟩
  letI : Mul K := ⟨mulValue M⟩
  letI : Neg K := ⟨negValue M⟩
  letI : Inv K := ⟨inverseValue M hM⟩
  exact Field.ofMinimalAxioms K h.add_assoc
    (fun x => (h.add_comm _ _).trans (h.add_zero x))
    (fun x => (h.add_comm _ _).trans (h.add_neg x))
    h.mul_assoc h.mul_comm
    (fun x => (h.mul_comm _ _).trans (h.mul_one x))
    (fun x hx => by
      change mulValue M x (inverseValue M hM x)=oneValue M
      change x≠zeroValue M at hx
      unfold inverseValue
      split
      · rename_i he
        exact False.elim (hx he)
      · exact Classical.choose_spec (h.inverse_exists x hx))
    (by change inverseValue M hM (zeroValue M)=zeroValue M; simp [inverseValue])
    h.distrib ⟨zeroValue M,oneValue M,h.zero_ne_one⟩

/-- The actual interpreted relation is strict, transitive and total,
so the pinned strict-total-order constructor yields its linear order. -/
@[instance_reducible] def linearOrderStructure : LinearOrder K := by
  let h := matrix_consequences M hM
  letI : IsStrictTotalOrder K (ltValue M) := {
    irrefl := h.irrefl
    trans := fun x y z hxy hyz => h.trans x y z ⟨hxy,hyz⟩
    trichotomous := fun x y hxy hyx => by
      rcases h.trichotomy x y with hx | he | hy
      · exact False.elim (hxy hx)
      · exact he
      · exact False.elim (hyx hy) }
  letI : DecidableRel (ltValue M) := fun _ _ => Classical.propDecidable _
  exact linearOrderOfSTO (ltValue M)

/-- These operation equalities are definitional for the constructed field. -/
theorem field_operations :
    letI : Field K := fieldStructure M hM
    (0 : K)=zeroValue M ∧ (1 : K)=oneValue M ∧
      (∀ x y : K,x+y=addValue M x y) ∧
      (∀ x y : K,x*y=mulValue M x y) ∧ (∀ x : K,-x=negValue M x) := by
  exact ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

theorem lt_comparison :
    letI : LinearOrder K := linearOrderStructure M hM
    ∀ x y : K,x<y ↔ ltValue M x y := by
  intro x y
  rfl

theorem le_comparison :
    letI : LinearOrder K := linearOrderStructure M hM
    ∀ x y : K,x≤y ↔ x=y ∨ ltValue M x y := by
  intro x y
  rfl

/-- The literal add-order and positive-product matrices supply all
compatibility laws of the constructed ordered field. -/
theorem strictOrderedRing :
    letI : Field K := fieldStructure M hM
    letI : LinearOrder K := linearOrderStructure M hM
    IsStrictOrderedRing K := by
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let h := matrix_consequences M hM
  let : IsOrderedAddMonoid K := {
    add_le_add_left := fun x y hxy z => by
      change x=y ∨ ltValue M x y at hxy
      change addValue M x z=addValue M y z ∨
        ltValue M (addValue M x z) (addValue M y z)
      rcases hxy with rfl | hxy
      · exact Or.inl rfl
      · exact Or.inr (h.add_lt_right x y z hxy) }
  let : ZeroLEOneClass K := ⟨Or.inr h.zero_lt_one⟩
  exact IsStrictOrderedRing.of_mul_pos (fun x y hx hy => h.mul_pos x y ⟨hx,hy⟩)

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
