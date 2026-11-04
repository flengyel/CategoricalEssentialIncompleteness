/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalListLaws

/-! # Internal equality calculations for categorical list deletion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

/-- An implication between generalized truth values follows from its
restriction to the true fiber of the antecedent. -/
theorem boolean_le_of_true {X : D} (p q : X ⟶ Two D)
    (h : Two.fiberι p true ≫ q = Two.constant (Two.Fiber p true) true) : p ≤ q := by
  apply inf_eq_left.mp
  apply Two.hom_ext p
  · simp only [Two.inf_def, Two.comp_binary, Two.fiberι_comp]
    exact bot_inf_eq _
  · simp only [Two.inf_def, Two.comp_binary, Two.fiberι_comp, h, Two.binary_constant]
    rfl

namespace DecidableVariables

variable {V : D} (E : DecidableVariables V)

/-- Two names equal to the same name are equal. This is an inequality
of internal truth values, proved on a truth-value fiber. -/
theorem test_common_source {X : D} (x y z : X ⟶ V) :
    (prod.lift x y ≫ E.test) ⊓ (prod.lift x z ≫ E.test) ≤
      prod.lift y z ≫ E.test := by
  let a := prod.lift x y ≫ E.test
  let b := prod.lift x z ≫ E.test
  let p := a ⊓ b
  let k := Two.fiberι p true
  apply boolean_le_of_true p (prod.lift y z ≫ E.test)
  have hp : (k ≫ a) ⊓ (k ≫ b) = ⊤ := by
    change Two.binary Bool.and (k ≫ a) (k ≫ b) = Two.constant _ true
    have hp' : k ≫ Two.binary Bool.and a b = Two.constant _ true :=
      Two.fiberι_comp p true
    exact (Two.comp_binary k Bool.and a b).symm.trans hp'
  have ha : k ≫ a = Two.constant (Two.Fiber p true) true := (inf_eq_top_iff.mp hp).1
  have hb : k ≫ b = Two.constant (Two.Fiber p true) true := (inf_eq_top_iff.mp hp).2
  have hxy : k ≫ x = k ≫ y := (E.test_true_iff _ _).mp (by
    simpa only [a, prod.comp_lift_assoc] using ha)
  have hxz : k ≫ x = k ≫ z := (E.test_true_iff _ _).mp (by
    simpa only [b, prod.comp_lift_assoc] using hb)
  have hyz := (E.test_true_iff (k ≫ y) (k ≫ z)).mpr (hxy.symm.trans hxz)
  simpa only [prod.comp_lift_assoc] using hyz

/-- Distinct names cannot both equal a third name, internally over
an arbitrary source object. -/
theorem test_disjoint_of_false {X : D} (x y z : X ⟶ V)
    (h : prod.lift y z ≫ E.test = Two.constant X false) :
    Disjoint (prod.lift x y ≫ E.test) (prod.lift x z ≫ E.test) := by
  have ht := E.test_common_source x y z
  rw [h] at ht
  exact disjoint_iff_inf_le.mpr ht

/-- The Boolean recurrence for membership after deletion. The branch
test compares the deleted name `y` with the current head `z`. -/
theorem deletion_boolean_step {X : D} (x y z : X ⟶ V) (m : X ⟶ Two D) :
    Two.branch (prod.lift y z ≫ E.test)
      (Two.binary Bool.or (prod.lift x z ≫ E.test)
        (Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ E.test)) m))
      (Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ E.test)) m) =
      Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ E.test))
        (Two.binary Bool.or (prod.lift x z ≫ E.test) m) := by
  let a := prod.lift x y ≫ E.test
  let b := prod.lift x z ≫ E.test
  let c := prod.lift y z ≫ E.test
  change Two.branch c (b ⊔ (aᶜ ⊓ m)) (aᶜ ⊓ m) = aᶜ ⊓ (b ⊔ m)
  apply Two.hom_ext c
  · let k := Two.fiberι c false
    have hc : prod.lift (k ≫ y) (k ≫ z) ≫ E.test =
        Two.constant (Two.Fiber c false) false := by
      simpa only [c, prod.comp_lift_assoc] using Two.fiberι_comp c false
    have hd : Disjoint (k ≫ a) (k ≫ b) := by
      simpa only [a, b, prod.comp_lift_assoc] using
        E.test_disjoint_of_false (k ≫ x) (k ≫ y) (k ≫ z) hc
    have hb : (k ≫ a)ᶜ ⊓ (k ≫ b) = k ≫ b := inf_eq_right.mpr hd.le_compl_left
    rw [Two.fiberι_branch]
    simp only [Bool.false_eq_true, ↓reduceIte, Two.sup_def, Two.inf_def,
      Two.compl_def, Two.comp_binary, Two.comp_unary]
    change (k ≫ b) ⊔ ((k ≫ a)ᶜ ⊓ (k ≫ m)) =
      (k ≫ a)ᶜ ⊓ ((k ≫ b) ⊔ (k ≫ m))
    rw [inf_sup_left, hb]
  · let k := Two.fiberι c true
    have hc : prod.lift (k ≫ y) (k ≫ z) ≫ E.test =
        Two.constant (Two.Fiber c true) true := by
      simpa only [c, prod.comp_lift_assoc] using Two.fiberι_comp c true
    have hyz : k ≫ y = k ≫ z := (E.test_true_iff _ _).mp hc
    have hb : k ≫ b = k ≫ a := by
      simp only [a, b, prod.comp_lift_assoc]
      rw [hyz]
    rw [Two.fiberι_branch]
    simp only [↓reduceIte, Two.sup_def, Two.inf_def, Two.compl_def,
      Two.comp_binary, Two.comp_unary]
    change (k ≫ a)ᶜ ⊓ (k ≫ m) = (k ≫ a)ᶜ ⊓ ((k ≫ b) ⊔ (k ≫ m))
    rw [hb]
    simp only [inf_sup_left, compl_inf_self, bot_sup_eq]

end DecidableVariables

end CategoricalEssentialIncompleteness.V46
