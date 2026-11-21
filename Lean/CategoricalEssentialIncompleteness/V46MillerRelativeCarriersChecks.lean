/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRelativeCarriers


/-! # The literal p-c.e.-carrier presentation of Split(Rec^p) -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.RelativeCarriers
attribute [instance 2000] Uniform.nativeRestriction

example (p : Bits) : Object p ≌ SplitObject (Uniform.RelativeObject p) := splitEquivalence p
example (p : Bits) : PreservesRestriction (splitEquivalence p).functor := splitEquivalence_restriction p
example (p : Bits) : PreservesRestriction (splitEquivalence p).inverse := splitEquivalence_inverse_restriction p

example (p : Bits) (A : Object p) : (carrier A).support=A.val := rfl
example {p : Bits} (A : Object p) : support (⊤ : Idem A)=A.val := support_top A
example {p : Bits} (A : Object p) : support (⊥ : Idem A)=∅ := support_bot A

example {p : Bits} (A B : Object p) (f : ℕ → Part ℕ) :
    (∃ g : A ⟶ B,val g=f) ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p)) f ∧
      (∀ x y,y∈f x → x∈A.val) ∧ (∀ x y,y∈f x → y∈B.val) := morphism_iff A B f

example {p : Bits} {A B : Object p} (f : A ⟶ B) :
    isTotal f ↔ ∀ x∈A.val,(val f x).Dom := total_iff f

example (p : Bits) {A B : Object p} (f : A ⟶ B) :
    ((splitEquivalence p).functor.map f).hom.val=val f := splitEquivalence_value p f

example (p : Bits) : WideSubcategory (isTotal (C := Object p)) ≌
    WideSubcategory (isTotal (C := SplitObject (Uniform.RelativeObject p))) := totalEquivalence p

end CategoricalEssentialIncompleteness.V46.Miller.RelativeCarriers
