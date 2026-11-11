/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCarrierIdempotents
public import CategoricalEssentialIncompleteness.V46MillerTotalEquivalence
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction

/-! # The literal p-c.e.-carrier presentation of Split(Rec^p)

An object is a subset of N with an actual p-relative partial-identity
certificate. The morphisms reuse the existing supported partial arrows;
their characterization below proves that these are exactly all supported
p-relative partial functions, including their undefined inputs.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.RelativeCarriers
attribute [instance 2000] Uniform.nativeRestriction

def oracle (p : Bits) : Set (ℕ → Part ℕ) :=
  OracleComputation.oracleSet (OracleRelative.oracleSupport p)

def Object (p : Bits) := {A : Set ℕ // Nat.RecursiveIn (oracle p) (Total.supportIdentity A)}

def carrier {p : Bits} (A : Object p) : Total.Carrier (Uniform.Family.singleton p) :=
  ⟨A.val,(CarrierIdempotents.singleton_enumerable_iff_recursive_identity p A.val).mpr A.property⟩

def objectOfCarrier (p : Bits) (A : Total.Carrier (Uniform.Family.singleton p)) : Object p :=
  ⟨A.support,(CarrierIdempotents.singleton_enumerable_iff_recursive_identity p A.support).mp A.enumerable⟩

theorem carrier_objectOfCarrier (p : Bits) (A : Total.Carrier (Uniform.Family.singleton p)) :
    carrier (objectOfCarrier p A)=A := rfl

theorem objectOfCarrier_carrier {p : Bits} (A : Object p) : objectOfCarrier p (carrier A)=A := rfl

instance (p : Bits) : Category (Object p) where
  Hom A B := carrier A ⟶ carrier B
  id A := 𝟙 (carrier A)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

instance (p : Bits) : RestrictionCategory (Object p) where
  rst f := rst (C := Total.Carrier (Uniform.Family.singleton p)) f
  rst_comp_self f := rst_comp_self (C := Total.Carrier (Uniform.Family.singleton p)) f
  rst_comm f g := rst_comm (C := Total.Carrier (Uniform.Family.singleton p)) f g
  rst_comp_rst f g := rst_comp_rst (C := Total.Carrier (Uniform.Family.singleton p)) f g
  rst_comp f g := rst_comp (C := Total.Carrier (Uniform.Family.singleton p)) f g

instance (p : Bits) : Limits.HasZeroMorphisms (Object p) where
  zero A B := inferInstanceAs (Zero (carrier A ⟶ carrier B))
  comp_zero := by intros; exact Limits.comp_zero (C := Total.Carrier (Uniform.Family.singleton p))
  zero_comp := by intros; exact Limits.zero_comp (C := Total.Carrier (Uniform.Family.singleton p))

instance (p : Bits) : RestrictionZero (Object p) where
  restrict_zero A B := RestrictionZero.restrict_zero (carrier A) (carrier B)

def toCarrier (p : Bits) : Object p ⥤ Total.Carrier (Uniform.Family.singleton p) where
  obj := carrier
  map f := f

def fromCarrier (p : Bits) : Total.Carrier (Uniform.Family.singleton p) ⥤ Object p where
  obj := objectOfCarrier p
  map f := f

instance (p : Bits) : (toCarrier p).Full where
  map_surjective f := ⟨f,rfl⟩
instance (p : Bits) : (toCarrier p).Faithful where
  map_injective h := h

/-- Only the proof attached to the same numerical support changes. -/
def carrierEquivalence (p : Bits) : Object p ≌ Total.Carrier (Uniform.Family.singleton p) where
  functor := toCarrier p
  inverse := fromCarrier p
  unitIso := NatIso.ofComponents (fun A => Iso.refl A) (by
    intro A B f
    change f ≫ 𝟙 B=𝟙 A ≫ f
    rw [Category.comp_id,Category.id_comp])
  counitIso := NatIso.ofComponents (fun A => Iso.refl A) (by
    intro A B f
    change f ≫ 𝟙 B=𝟙 A ≫ f
    rw [Category.comp_id,Category.id_comp])
  functor_unitIso_comp A := by
    change (𝟙 (carrier A)) ≫ 𝟙 (carrier A)=𝟙 (carrier A)
    exact Category.id_comp _

theorem toCarrier_restriction (p : Bits) : PreservesRestriction (toCarrier p) := fun _ => rfl
theorem fromCarrier_restriction (p : Bits) : PreservesRestriction (fromCarrier p) := fun _ => rfl

def val {p : Bits} {A B : Object p} (f : A ⟶ B) : ℕ → Part ℕ := Total.val f

theorem val_injective {p : Bits} {A B : Object p} : Function.Injective (val (A := A) (B := B)) :=
  Total.val_injective

theorem val_id {p : Bits} (A : Object p) : val (𝟙 A)=Total.supportIdentity A.val := rfl
theorem val_comp {p : Bits} {A B C : Object p} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    val (f ≫ g) n=(val f n).bind (val g) := rfl
theorem val_zero {p : Bits} (A B : Object p) : val (0 : A ⟶ B)=fun _ => Part.none := rfl
theorem val_restriction {p : Bits} {A B : Object p} (f : A ⟶ B) :
    val (rst f)=rst (C := PartialFunctions.Pfn) (val f) := rfl

private theorem encodeFunction_nat (f : ℕ → Part ℕ) : Uniform.encodeFunction .nat .nat f=f := by
  funext n
  change (f n).map (fun y => y)=f n
  exact Part.map_id' (fun _ => rfl) (f n)

theorem represented_iff_recursive (p : Bits) (f : ℕ → Part ℕ) :
    Uniform.Represented (Uniform.Family.singleton p) .nat .nat f ↔ Nat.RecursiveIn (oracle p) f := by
  constructor
  · intro h
    exact ((Uniform.singleton_represented_iff_recursiveIn p .nat .nat f).mp h).of_eq
      (fun n => congrFun (encodeFunction_nat f) n)
  · intro h
    apply (Uniform.singleton_represented_iff_recursiveIn p .nat .nat f).mpr
    exact h.of_eq (fun n => (congrFun (encodeFunction_nat f) n).symm)

theorem val_recursive {p : Bits} {A B : Object p} (f : A ⟶ B) :
    Nat.RecursiveIn (oracle p) (val f) :=
  (represented_iff_recursive p (val f)).mp (Total.val_represented f)

theorem val_source {p : Bits} {A B : Object p} (f : A ⟶ B) (x y : ℕ) (hy : y∈val f x) :
    x∈A.val := Total.val_source f x y hy

theorem val_target {p : Bits} {A B : Object p} (f : A ⟶ B) (x y : ℕ) (hy : y∈val f x) :
    y∈B.val := Total.val_target f x y hy

/-- Every supported p-relative partial function is a morphism, without
an ordinary value extension or any condition of totality on its carrier. -/
def arrow {p : Bits} {A B : Object p} (f : ℕ → Part ℕ) (hf : Nat.RecursiveIn (oracle p) f)
    (hs : ∀ x y,y∈f x → x∈A.val) (ht : ∀ x y,y∈f x → y∈B.val) : A ⟶ B :=
  Total.arrow f ((represented_iff_recursive p f).mpr hf) hs ht

theorem val_arrow {p : Bits} {A B : Object p} (f : ℕ → Part ℕ) (hf : Nat.RecursiveIn (oracle p) f)
    (hs : ∀ x y,y∈f x → x∈A.val) (ht : ∀ x y,y∈f x → y∈B.val) :
    val (arrow f hf hs ht)=f := rfl

theorem morphism_iff {p : Bits} (A B : Object p) (f : ℕ → Part ℕ) :
    (∃ g : A ⟶ B,val g=f) ↔ Nat.RecursiveIn (oracle p) f ∧
      (∀ x y,y∈f x → x∈A.val) ∧ (∀ x y,y∈f x → y∈B.val) := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨val_recursive g,val_source g,val_target g⟩
  · rintro ⟨hf,hs,ht⟩
    exact ⟨arrow f hf hs ht,rfl⟩

theorem total_iff {p : Bits} {A B : Object p} (f : A ⟶ B) :
    isTotal f ↔ ∀ x∈A.val,(val f x).Dom := Total.total_iff f

/-- This target is the full fixed-oracle Rec^p from the proved graph
comparison. The all-representation J is not assumed full. -/
def splitEquivalence (p : Bits) : Object p ≌ SplitObject (Uniform.RelativeObject p) :=
  (carrierEquivalence p).trans (Total.carrierEquivalence (P := Uniform.Family.singleton p))

theorem splitEquivalence_object (p : Bits) (A : Object p) :
    (splitEquivalence p).functor.obj A=
      (⟨Uniform.N (Uniform.Family.singleton p),
        Uniform.setIdem _ A.val (carrier A).enumerable⟩ : SplitObject (Uniform.RelativeObject p)) := rfl

theorem splitEquivalence_value (p : Bits) {A B : Object p} (f : A ⟶ B) :
    ((splitEquivalence p).functor.map f).hom.val=val f := rfl

theorem splitEquivalence_restriction (p : Bits) : PreservesRestriction (splitEquivalence p).functor :=
  fun _ => rfl

theorem splitEquivalence_inverse_restriction (p : Bits) : PreservesRestriction (splitEquivalence p).inverse :=
  fun f => LocalConnectedness.V46.equivalence_inverse_preserves (splitEquivalence p)
    (splitEquivalence_restriction p) f

def toCarrierIdem {p : Bits} {A : Object p} (c : Idem A) : Idem (carrier A) := ⟨c.hom,c.restriction⟩
def support {p : Bits} {A : Object p} (c : Idem A) : Set ℕ := Total.support (toCarrierIdem c)

theorem support_top {p : Bits} (A : Object p) : support (⊤ : Idem A)=A.val := Total.support_top (carrier A)
theorem support_bot {p : Bits} (A : Object p) : support (⊥ : Idem A)=∅ := Total.support_bot (carrier A)

theorem support_recursive {p : Bits} {A : Object p} (c : Idem A) :
    Nat.RecursiveIn (oracle p) (Total.supportIdentity (support c)) :=
  (CarrierIdempotents.singleton_enumerable_iff_recursive_identity p _).mp
    (Total.support_re (toCarrierIdem c))

/-- Total morphisms in the literal p-c.e. presentation give precisely the
total category of the actual restriction splitting. -/
def totalEquivalence (p : Bits) :
    WideSubcategory (isTotal (C := Object p)) ≌
      WideSubcategory (isTotal (C := SplitObject (Uniform.RelativeObject p))) :=
  PreservesRestriction.totalEquivalence (F := (splitEquivalence p).functor)
    (splitEquivalence_restriction p)

end CategoricalEssentialIncompleteness.V46.Miller.RelativeCarriers
