/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitution

/-! # Boolean identities used by the Hilbert schemes -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

theorem implication_self {W : D} (a : W ⟶ Two D) :
    Two.binary implies a a = Two.constant W true :=
  Two.check₁ (fun _ a => Two.binary implies a a) (fun W _ => Two.constant W true)
    (by intros; simp) (by intros; simp)
    (by intro W a; cases a <;> simp [implies]) W a

theorem implication_true_left {W : D} (a : W ⟶ Two D) :
    Two.binary implies (Two.constant W true) a = a :=
  Two.check₁ (fun W a => Two.binary implies (Two.constant W true) a) (fun _ a => a)
    (by intros; simp) (by intros; rfl)
    (by intro W a; cases a <;> simp [implies]) W a

theorem implication_one {W : D} (a b : W ⟶ Two D) :
    Two.binary implies a (Two.binary implies b a) = Two.constant W true :=
  Two.check₂ (fun _ a b => Two.binary implies a (Two.binary implies b a))
    (fun W _ _ => Two.constant W true) (by intros; simp) (by intros; simp)
    (by intro W a b; cases a <;> cases b <;> simp [implies]) W a b

theorem implication_two {W : D} (a b c : W ⟶ Two D) :
    Two.binary implies (Two.binary implies a (Two.binary implies b c))
      (Two.binary implies (Two.binary implies a b) (Two.binary implies a c)) =
        Two.constant W true :=
  Two.check₃
    (fun _ a b c => Two.binary implies (Two.binary implies a (Two.binary implies b c))
      (Two.binary implies (Two.binary implies a b) (Two.binary implies a c)))
    (fun W _ _ _ => Two.constant W true) (by intros; simp) (by intros; simp)
    (by intro W a b c; cases a <;> cases b <;> cases c <;> simp [implies]) W a b c

theorem implication_three {W : D} (a b : W ⟶ Two D) :
    Two.binary implies (Two.binary implies (Two.unary Bool.not b) (Two.unary Bool.not a))
      (Two.binary implies a b) = Two.constant W true :=
  Two.check₂
    (fun _ a b => Two.binary implies
      (Two.binary implies (Two.unary Bool.not b) (Two.unary Bool.not a))
      (Two.binary implies a b))
    (fun W _ _ => Two.constant W true) (by intros; simp) (by intros; simp)
    (by intro W a b; cases a <;> cases b <;> simp [implies]) W a b

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
