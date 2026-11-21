/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerUniformComputations
public import CategoricalEssentialIncompleteness.PartialFunctions

/-! # The representation-independent Miller category

Objects retain their formal numerical product and coproduct expressions. A morphism
has one oracle index for all representations, with equality of its entire partial
graph; there is no ordinary value-extension field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleComputation (Ty)

structure Object (_z : Family) where
  type : Ty

abbrev PointObject (z : Point) := Object (Family.ofPoint z)

abbrev carrier (z : Family) (X : Object z) := X.type.carrier

instance (z : Family) (X : Object z) : Primcodable (carrier z X) := X.type.primcodable

@[ext] structure Arrow (z : Family) (X Y : Ty) where
  val : X.carrier → Part Y.carrier
  represented : Represented z X Y val

namespace Arrow
variable {z : Family}

def identity (X : Ty) : Arrow z X X :=
  ⟨Part.some,Represented.of_partrec Partrec.some⟩

def compose {X Y Z : Ty} (f : Arrow z X Y) (g : Arrow z Y Z) : Arrow z X Z :=
  ⟨fun x => (f.val x).bind g.val,Represented.comp f.represented g.represented⟩
end Arrow

variable {z : Family}

instance : Category (Object z) where
  Hom X Y := Arrow z X.type Y.type
  id X := Arrow.identity X.type
  comp := Arrow.compose
  id_comp f := Arrow.ext (funext (fun x => Part.bind_some x f.val))
  comp_id f := Arrow.ext (funext (fun x => Part.bind_some_right (f.val x)))
  assoc f g h := Arrow.ext (funext (fun x => Part.bind_assoc (f.val x) g.val h.val))

@[simp] theorem comp_val {X Y Z : Object z} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = fun x => (f.val x).bind g.val := rfl

@[simp] theorem id_val (X : Object z) : (𝟙 X : X ⟶ X).val = Part.some := rfl

def inclusion (z : Family) : Object z ⥤ PartialFunctions.Pfn where
  obj X := PartialFun.of (carrier z X)
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance (z : Family) : (inclusion z).Faithful where
  map_injective h := Arrow.ext h

theorem hom_ext_mem {X Y : Object z} {f g : X ⟶ Y}
    (h : ∀ x y,y ∈ f.val x ↔ y ∈ g.val x) : f = g :=
  Arrow.ext (funext (fun x => Part.ext (h x)))

theorem graph_enumerable {X Y : Object z} (f : X ⟶ Y) :
    Enumerable z (fun a : carrier z X × carrier z Y => a.2 ∈ f.val a.1) :=
  (represented_iff_graph_enumerable z X.type Y.type f.val).mp f.represented

def ofPartrec {X Y : Object z} (f : carrier z X → Part (carrier z Y)) (hf : Partrec f) : X ⟶ Y :=
  ⟨f,Represented.of_partrec hf⟩

def totalFromFunction {X Y : Object z} (f : carrier z X → carrier z Y) (hf : Computable f) : X ⟶ Y :=
  ofPartrec (fun x => Part.some (f x)) hf.partrec

def identityOn (X : Object z) (A : Set (carrier z X)) (hA : Enumerable z (· ∈ A)) : X ⟶ X :=
  ⟨PartialFunctions.partialIdentity (PartialFun.of (carrier z X)) A,
    (Represented.identityOn X.type A hA).of_eq (fun x => by
      apply Part.ext
      intro y
      simp only [Part.mem_assert_iff,Part.mem_some_iff,exists_prop]
      exact (PartialFunctions.mem_identity A x y).symm)⟩

theorem mem_identityOn (X : Object z) (A : Set (carrier z X)) (hA : Enumerable z (· ∈ A)) (x y : carrier z X) :
    y ∈ (identityOn X A hA).val x ↔ x ∈ A ∧ y = x := by
  exact PartialFunctions.mem_identity A x y

def restriction {X Y : Object z} (f : X ⟶ Y) : X ⟶ X :=
  identityOn X {x | (f.val x).Dom} f.represented.domain

instance nativeRestriction : RestrictionCategory (Object z) where
  rst := restriction
  rst_comp_self f := Arrow.ext (rst_comp_self (C := PartialFunctions.Pfn) f.val)
  rst_comm f g := Arrow.ext (rst_comm (C := PartialFunctions.Pfn) f.val g.val)
  rst_comp_rst f g := Arrow.ext (rst_comp_rst (C := PartialFunctions.Pfn) f.val g.val)
  rst_comp f g := Arrow.ext (rst_comp (C := PartialFunctions.Pfn) f.val g.val)

attribute [instance 2000] nativeRestriction

@[simp] theorem restriction_val {X Y : Object z} (f : X ⟶ Y) :
    (rst f).val = rst (C := PartialFunctions.Pfn) f.val := rfl

instance : HasZeroMorphisms (Object z) where
  zero X Y := ⟨ofPartrec (fun _ => Part.none) Partrec.none⟩
  comp_zero := by intro X Y f Z; exact Arrow.ext (comp_zero (C := PartialFunctions.Pfn))
  zero_comp := by intro X Y Z f; exact Arrow.ext (zero_comp (C := PartialFunctions.Pfn))

@[simp] theorem zero_val (X Y : Object z) : (0 : X ⟶ Y).val = fun _ => Part.none := rfl

instance : RestrictionZero (Object z) where
  restrict_zero X Y := Arrow.ext
    (RestrictionZero.restrict_zero ((inclusion z).obj X) ((inclusion z).obj Y))

def toPfnIdem {X : Object z} (a : Idem X) : Idem ((inclusion z).obj X) :=
  ⟨a.hom.val,congrArg Arrow.val a.restriction⟩

theorem toPfnIdem_injective {X : Object z} : Function.Injective (toPfnIdem (X := X)) := by
  intro a b h
  exact Idem.ext (Arrow.ext (congrArg Idem.hom h))

def setIdem (X : Object z) (A : Set (carrier z X)) (hA : Enumerable z (· ∈ A)) : Idem X :=
  ⟨identityOn X A hA,Arrow.ext (PartialFunctions.setIdem A).restriction⟩

def image {X Y : Object z} (f : X ⟶ Y) : Set (carrier z Y) := {y | ∃ x,y ∈ f.val x}

theorem image_enumerable {X Y : Object z} (f : X ⟶ Y) : Enumerable z (· ∈ image f) :=
  f.represented.image

instance : Ranges (Object z) where
  range f := setIdem _ (image f) (image_enumerable f)
  receives f := Arrow.ext (Ranges.receives (C := PartialFunctions.Pfn) f.val)
  agreement f g h he := Arrow.ext
    (Ranges.agreement (C := PartialFunctions.Pfn) f.val g.val h.val (congrArg Arrow.val he))

theorem mem_range {X Y : Object z} (f : X ⟶ Y) (x y : carrier z Y) :
    y ∈ (Ranges.range f).hom.val x ↔ (∃ a,x ∈ f.val a) ∧ y = x :=
  mem_identityOn Y (image f) (image_enumerable f) x y

theorem total_iff {X Y : Object z} (f : X ⟶ Y) :
    isTotal f ↔ ∀ x,(f.val x).Dom := by
  constructor
  · intro h x
    have hx : x ∈ (rst f).val x := by rw [h]; exact Part.mem_some x
    exact ((mem_identityOn X _ f.represented.domain x x).mp hx).1
  · intro h
    apply hom_ext_mem
    intro x y
    change y ∈ (identityOn X _ f.represented.domain).val x ↔ y ∈ Part.some x
    rw [mem_identityOn]
    change ((f.val x).Dom ∧ y=x) ↔ y ∈ Part.some x
    simp only [h x,true_and,Part.mem_some_iff]

theorem totalFromFunction_total {X Y : Object z}
    (f : carrier z X → carrier z Y) (hf : Computable f) : isTotal (totalFromFunction f hf) :=
  (total_iff _).mpr (fun x => Part.some_dom (f x))

def N (z : Family) : Object z := ⟨.nat⟩

/-- The codings are the original recursive bijections of the formal
object expressions, not choices depending on a representation. -/
def codeIso (X : Object z) : X ≅ N z where
  hom := totalFromFunction X.type.toNat X.type.toNat_computable
  inv := totalFromFunction X.type.fromNat X.type.fromNat_computable
  hom_inv_id := by
    apply Arrow.ext
    funext x
    change (Part.some (X.type.toNat x)).bind
      (fun n => Part.some (X.type.fromNat n)) = Part.some x
    simp only [Part.bind_some,X.type.from_toNat]
  inv_hom_id := by
    apply Arrow.ext
    funext n
    change (Part.some (X.type.fromNat n)).bind
      (fun x => Part.some (X.type.toNat x)) = Part.some n
    simp only [Part.bind_some,X.type.to_fromNat]

instance isotype : RecursionCategory.Isotype (Object z) where
  iso X Y := ⟨codeIso X ≪≫ (codeIso Y).symm⟩

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
