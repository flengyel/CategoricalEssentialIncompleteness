/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PartialFunctions
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Families of sets and partial functions -/

@[expose] public section

universe u w

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctionFamilies

open PartialFunctions

abbrev Family (I : Type w) := I → Pfn.{u}

variable {I : Type w}

instance : RestrictionCategory (Family.{u} I) where
  rst f i := rst (f i)
  rst_comp_self f := funext fun i => rst_comp_self (f i)
  rst_comm f g := funext fun i => rst_comm (f i) (g i)
  rst_comp_rst f g := funext fun i => rst_comp_rst (f i) (g i)
  rst_comp f g := funext fun i => rst_comp (f i) (g i)

instance : HasZeroMorphisms (Family.{u} I) where
  zero _ _ := ⟨fun _ => 0⟩
  comp_zero := by
    intro X Y f Z
    exact funext fun i => (show f i ≫ (0 : Y i ⟶ Z i) = 0 from comp_zero)
  zero_comp := by
    intro X Y Z f
    exact funext fun i => (show (0 : X i ⟶ Y i) ≫ f i = 0 from zero_comp)

instance : RestrictionZero (Family.{u} I) where
  restrict_zero X Y := funext fun i =>
    (show rst (0 : X i ⟶ Y i) = 0 from RestrictionZero.restrict_zero (X i) (Y i))

def component {X : Family.{u} I} (a : Idem X) (i : I) : Idem (X i) :=
  ⟨a.hom i, congrFun a.restriction i⟩

def assemble {X : Family.{u} I} (a : ∀ i, Idem (X i)) : Idem X :=
  ⟨fun i => (a i).hom, funext fun i => (a i).restriction⟩

@[simp] theorem component_assemble {X : Family.{u} I} (a : ∀ i, Idem (X i)) (i : I) :
    component (assemble a) i = a i := rfl

theorem component_ext {X : Family.{u} I} {a b : Idem X}
    (h : ∀ i, component a i = component b i) : a = b :=
  Idem.ext (funext fun i => congrArg Idem.hom (h i))

theorem le_iff_component {X : Family.{u} I} (a b : Idem X) :
    a ≤ b ↔ ∀ i, component a i ≤ component b i := by
  change (a.hom ≫ b.hom = a.hom) ↔ ∀ i, a.hom i ≫ b.hom i = a.hom i
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

@[simp] theorem component_inf {X : Family.{u} I} (a b : Idem X) (i : I) :
    component (a ⊓ b) i = component a i ⊓ component b i := rfl
@[simp] theorem component_top {X : Family.{u} I} (i : I) :
    component (⊤ : Idem X) i = ⊤ := rfl
@[simp] theorem component_bot {X : Family.{u} I} (i : I) :
    component (⊥ : Idem X) i = ⊥ := rfl
@[simp] theorem component_pull {X Y : Family.{u} I} (f : X ⟶ Y) (a : Idem Y) (i : I) :
    component (Idem.pull f a) i = Idem.pull (f i) (component a i) := rfl

instance : Ranges (Family.{u} I) where
  range f := assemble fun i => Ranges.range (f i)
  receives f := funext fun i => Ranges.receives (f i)
  agreement f g h he := funext fun i => Ranges.agreement (f i) (g i) (h i) (congrFun he i)

instance : BinaryJoins (Family.{u} I) where
  join a b := assemble fun i => component a i ⊔ component b i
  le_left a b := (le_iff_component _ _).mpr fun _ => le_sup_left
  le_right a b := (le_iff_component _ _).mpr fun _ => le_sup_right
  least a b c ha hb := (le_iff_component _ _).mpr fun i =>
    sup_le ((le_iff_component _ _).mp ha i) ((le_iff_component _ _).mp hb i)

@[simp] theorem component_sup {X : Family.{u} I} (a b : Idem X) (i : I) :
    component (a ⊔ b) i = component a i ⊔ component b i := rfl

instance : JoinInverse (Family.{u} I) where
  pull_sup f a b := component_ext fun i => JoinInverse.pull_sup (f i) (component a i) (component b i)

instance : CoprodStruct (Family.{u} I) where
  coprod X Y i := coprod (X i) (Y i)
  coprod_map f g i := coprod_map (f i) (g i)
  codiag X i := codiag (X i)
  i0 X Y i := i0 (X i) (Y i)
  i1 X Y i := i1 (X i) (Y i)

instance : CategoryTheory.HasCoproducts (Family.{u} I) where
  coprod_id X Y := funext fun i => coprod_id (X i) (Y i)
  coprod_comp f g h k := funext fun i => coprod_comp (f i) (g i) (h i) (k i)
  i0_codiag X := funext fun i => i0_codiag (X i)
  i1_codiag X := funext fun i => i1_codiag (X i)
  i0_i1_codiag X Y := funext fun i => i0_i1_codiag (X i) (Y i)
  codiag_nat f := funext fun i => codiag_nat (f i)
  i0_nat f := funext fun i => i0_nat (f i)
  i0_nat_right f := funext fun i => i0_nat_right (f i)
  i1_nat f := funext fun i => i1_nat (f i)
  i1_nat_left f := funext fun i => i1_nat_left (f i)

instance : Splits (Family.{u} I) where
  splitting a := by
    choose Z m r ht hm hr using fun i => Splits.splitting (component a i)
    exact ⟨Z, m, r, funext ht, funext hm, funext hr⟩

instance : WeakChoice (Family.{u} I) where
  section_exists f _ := ⟨fun i => chosenSection (f i),
    ⟨funext fun i => (chosenSection_isSection (f i)).comp,
      funext fun i => (chosenSection_isSection (f i)).receives⟩⟩

/-- The support is a subset of the disjoint union of all coordinate sets. -/
def support {X : Family.{u} I} (a : Idem X) : Set (Σ i, X i) :=
  {x | x.2 ∈ PartialFunctions.support (component a x.1)}

def setIdem {X : Family.{u} I} (s : Set (Σ i, X i)) : Idem X :=
  assemble fun i => PartialFunctions.setIdem {x | ⟨i, x⟩ ∈ s}

@[simp] theorem support_setIdem {X : Family.{u} I} (s : Set (Σ i, X i)) :
    support (setIdem s) = s := by
  ext x
  change x.2 ∈ PartialFunctions.support (PartialFunctions.setIdem _) ↔ _
  rw [PartialFunctions.support_setIdem]
  rfl

theorem support_injective {X : Family.{u} I} : Function.Injective (support (X := X)) := by
  intro a b h
  apply component_ext
  intro i
  apply PartialFunctions.support_injective
  ext x
  exact Iff.of_eq (congrArg (fun s => (⟨i, x⟩ : Σ i, X i) ∈ s) h)

@[simp] theorem support_sup {X : Family.{u} I} (a b : Idem X) :
    support (a ⊔ b) = support a ∪ support b := by
  ext x
  change x.2 ∈ PartialFunctions.support (component a x.1 ⊔ component b x.1) ↔ _
  rw [PartialFunctions.support_sup]
  rfl

@[simp] theorem support_inf {X : Family.{u} I} (a b : Idem X) :
    support (a ⊓ b) = support a ∩ support b := by
  ext x
  change x.2 ∈ PartialFunctions.support (component a x.1 ⊓ component b x.1) ↔ _
  rw [PartialFunctions.support_inf]
  rfl

@[simp] theorem support_bot {X : Family.{u} I} : support (⊥ : Idem X) = ∅ := by
  ext x
  change x.2 ∈ PartialFunctions.support (⊥ : Idem _) ↔ False
  rw [PartialFunctions.support_bot]
  rfl

theorem singleton_connected {X : Family.{u} I} (x : Σ i, X i) : Connected (setIdem {x}) := by
  intro b c he hd
  classical
  by_cases hb : b = ⊥
  · exact Or.inl hb
  right
  apply support_injective
  rw [support_bot]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb' : (support b).Nonempty := Set.nonempty_iff_ne_empty.mpr (by
    intro hempty; apply hb; apply support_injective; rw [support_bot, hempty])
  obtain ⟨y, hy⟩ := hb'
  have he' := congrArg support he
  rw [support_setIdem, support_sup] at he'
  have hyx : y = x := by
    have h : y ∈ ({x} : Set (Σ i, X i)) := by rw [he']; exact Or.inl hy
    exact h
  have hzx : z = x := by
    have h : z ∈ ({x} : Set (Σ i, X i)) := by rw [he']; exact Or.inr hz
    exact h
  have hd' := congrArg support hd
  rw [support_inf, support_bot] at hd'
  have hmem : x ∈ support b ∩ support c := ⟨hyx ▸ hy, hzx ▸ hz⟩
  rw [hd'] at hmem
  exact hmem

instance : LocallyConnected (Family.{u} I) where
  hom_ext f g h := by
    funext i x
    let a := setIdem ({⟨i, x⟩} : Set (Σ i, _))
    have he := congrFun (congrFun (h a (singleton_connected ⟨i, x⟩)) i) x
    change (PartialFunctions.partialIdentity _ {y | (⟨i, y⟩ : Σ i, _) = ⟨i, x⟩} x).bind (f i) =
      (PartialFunctions.partialIdentity _ {y | (⟨i, y⟩ : Σ i, _) = ⟨i, x⟩} x).bind (g i) at he
    have hx : PartialFunctions.partialIdentity _ {y | (⟨i, y⟩ : Σ i, _) = ⟨i, x⟩} x = Part.some x :=
      Part.eq_some_iff.mpr ((mem_identity _ x x).mpr ⟨rfl, rfl⟩)
    simpa only [hx, Part.bind_some] using he

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctionFamilies
