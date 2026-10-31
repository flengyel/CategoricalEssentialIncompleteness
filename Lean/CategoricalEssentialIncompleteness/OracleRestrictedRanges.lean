/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleRestrictedCategory
import CategoricalEssentialIncompleteness.OracleCodedDomains

/-! # Restrictions, zeros and actual image ranges in the oracle-domain category -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}

def ofPartrec {X Y : Restricted S} (f : carrier S X → Part (carrier S Y)) (hf : Partrec f) : X ⟶ Y :=
  ⟨f,FiniteOracleRE.of_re hf.dom_re,⟨f,hf,fun _ _ h => h⟩⟩

def totalFromFunction {X Y : Restricted S} (f : carrier S X → carrier S Y) (hf : Computable f) : X ⟶ Y :=
  ofPartrec (fun x => Part.some (f x)) hf.partrec

def identityOn (X : Restricted S) (A : Set (carrier S X)) (hA : FiniteOracleRE S (· ∈ A)) : X ⟶ X :=
  ⟨PartialFunctions.partialIdentity (PartialFun.of (carrier S X)) A,
    hA.of_eq (fun x => by
      rw [Part.dom_iff_mem]
      constructor
      · intro hx
        exact ⟨x,(PartialFunctions.mem_identity A x x).mpr ⟨hx,rfl⟩⟩
      · rintro ⟨y,hy⟩
        exact ((PartialFunctions.mem_identity A x y).mp hy).1),
    ⟨Part.some,Partrec.some,by
      intro x y hy
      exact Part.mem_some_iff.mpr ((PartialFunctions.mem_identity A x y).mp hy).2⟩⟩

theorem mem_identityOn (X : Restricted S) (A : Set (carrier S X)) (hA : FiniteOracleRE S (· ∈ A))
    (x y : carrier S X) : y ∈ (identityOn X A hA).val x ↔ x ∈ A ∧ y=x :=
  PartialFunctions.mem_identity A x y

def restriction {X Y : Restricted S} (f : X ⟶ Y) : X ⟶ X :=
  identityOn X {x | (f.val x).Dom} f.domain

instance nativeRestriction : RestrictionCategory (Restricted S) where
  rst := restriction
  rst_comp_self f := Arrow.ext (rst_comp_self (C := PartialFunctions.Pfn) f.val)
  rst_comm f g := Arrow.ext (rst_comm (C := PartialFunctions.Pfn) f.val g.val)
  rst_comp_rst f g := Arrow.ext (rst_comp_rst (C := PartialFunctions.Pfn) f.val g.val)
  rst_comp f g := Arrow.ext (rst_comp (C := PartialFunctions.Pfn) f.val g.val)

@[simp] theorem restriction_val {X Y : Restricted S} (f : X ⟶ Y) :
    (rst f).val=rst (C := PartialFunctions.Pfn) f.val := rfl

instance : HasZeroMorphisms (Restricted S) where
  zero X Y := ⟨ofPartrec (fun _ => Part.none) Partrec.none⟩
  comp_zero := by
    intro X Y f Z
    exact Arrow.ext (comp_zero (C := PartialFunctions.Pfn))
  zero_comp := by
    intro X Y Z f
    exact Arrow.ext (zero_comp (C := PartialFunctions.Pfn))

instance : RestrictionZero (Restricted S) where
  restrict_zero X Y := Arrow.ext (RestrictionZero.restrict_zero
    ((inclusion S).obj X) ((inclusion S).obj Y))

def toPfnIdem {X : Restricted S} (a : Idem X) : Idem ((inclusion S).obj X) :=
  ⟨a.hom.val,congrArg Arrow.val a.restriction⟩

theorem toPfnIdem_injective {X : Restricted S} : Function.Injective (toPfnIdem (X := X)) := by
  intro a b h
  exact Idem.ext (Arrow.ext (congrArg Idem.hom h))

def setIdem (X : Restricted S) (A : Set (carrier S X)) (hA : FiniteOracleRE S (· ∈ A)) : Idem X :=
  ⟨identityOn X A hA,Arrow.ext (PartialFunctions.setIdem A).restriction⟩

def image {X Y : Restricted S} (f : X ⟶ Y) : Set (carrier S Y) := {y | ∃ x,y ∈ f.val x}

theorem image_enumerable {X Y : Restricted S} (f : X ⟶ Y) : FiniteOracleRE S (· ∈ image f) := by
  obtain ⟨f₀,hf,he⟩ := f.extension
  have hg := (f.domain.comp Computable.fst).and (FiniteOracleRE.of_re (partrecGraph hf))
  have hs := hg.comp (Computable.pair Computable.snd Computable.fst)
  exact hs.projection.of_eq (fun y => by
    change (∃ x,(f.val x).Dom ∧ y ∈ f₀ x) ↔ ∃ x,y ∈ f.val x
    exact exists_congr (fun x => (he.mem_iff x y).symm))

instance : Ranges (Restricted S) where
  range f := setIdem _ (image f) (image_enumerable f)
  receives f := Arrow.ext (Ranges.receives (C := PartialFunctions.Pfn) f.val)
  agreement f g h he := Arrow.ext
    (Ranges.agreement (C := PartialFunctions.Pfn) f.val g.val h.val (congrArg Arrow.val he))

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
