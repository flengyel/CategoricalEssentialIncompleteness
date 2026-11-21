/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.BooleanPresentations

/-!
# Characteristic morphisms of complementary subobjects

In a regular extensive category, complementary subobjects give a coproduct
decomposition and hence a characteristic morphism to `1 + 1`. Conversely, the fibers
of every morphism to `1 + 1` form such a decomposition. No subobject classifier for
arbitrary subobjects is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

/-- The object of two truth values, before equipping it with Boolean operations. -/
abbrev Two (C : Type u) [Category.{v} C] [HasTerminal C] [HasBinaryCoproducts C] : C :=
  (⊤_ C) ⨿ (⊤_ C)

namespace Two

/-- The lower and upper inclusions, indexed by ordinary Boolean values. -/
def point : Bool → (⊤_ C ⟶ Two C)
  | false => coprod.inl
  | true => coprod.inr

/-- A constant truth value on an arbitrary object. -/
def constant (X : C) (b : Bool) : X ⟶ Two C := terminal.from X ≫ point b

@[simp, reassoc]
theorem comp_constant {X Y : C} (f : X ⟶ Y) (b : Bool) :
    f ≫ constant Y b = constant X b := by simp [constant]

/-- The chosen object of the fiber over a truth value. -/
abbrev Fiber {X : C} (f : X ⟶ Two C) (b : Bool) : C := equalizer f (constant X b)

/-- Inclusion of a truth-value fiber. -/
abbrev fiberι {X : C} (f : X ⟶ Two C) (b : Bool) : Fiber f b ⟶ X :=
  equalizer.ι f (constant X b)

@[simp, reassoc]
theorem fiberι_comp {X : C} (f : X ⟶ Two C) (b : Bool) :
    fiberι f b ≫ f = constant (Fiber f b) b := by
  rw [fiberι, equalizer.condition, comp_constant]

set_option backward.isDefEq.respectTransparency false in
/-- Extensivity decomposes an arbitrary morphism to `1 + 1` into its two fibers. -/
def fibersIsColimit {X : C} (f : X ⟶ Two C) :
    IsColimit (BinaryCofan.mk (fiberι f false) (fiberι f true)) := by
  have h := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ C) (⊤_ C)))
    (BinaryCofan.mk (fiberι f false) (fiberι f true))
  exact ((h
    (terminal.from _) (terminal.from _) f
    (by simp [constant, point]) (by simp [constant, point])).mpr
      ⟨PresentationLemmas.bound_isPullback f (point false),
        PresentationLemmas.bound_isPullback f (point true)⟩).some

/-- Equality of morphisms can be checked on both truth-value fibers. -/
theorem hom_ext {X Y : C} (f : X ⟶ Two C) {g h : X ⟶ Y}
    (h₀ : fiberι f false ≫ g = fiberι f false ≫ h)
    (h₁ : fiberι f true ≫ g = fiberι f true ≫ h) : g = h :=
  BinaryCofan.IsColimit.hom_ext (fibersIsColimit f) h₀ h₁

end Two

/-- Two complementary subobjects. Distributivity of the entire subobject lattice
is not required to specify a particular complement. -/
structure SubobjectPartition (X : C) where
  positive : Subobject X
  negative : Subobject X
  complementary : IsCompl positive negative

namespace SubobjectPartition

variable {X : C} (p : SubobjectPartition X)

/-- The copairing of the negative and positive inclusions. -/
def cover : (p.negative : C) ⨿ (p.positive : C) ⟶ X :=
  coprod.desc p.negative.arrow p.positive.arrow

instance cover_mono : Mono p.cover :=
  (PresentationLemmas.mono_copair_iff _ _).mpr (by
    simpa using p.complementary.symm.inf_eq_bot)

instance cover_regularEpi : IsRegularEpi p.cover :=
  (PresentationLemmas.image_eq_top_iff_regularEpi _).mp (by
    rw [cover, PresentationLemmas.image_copair, imageSubobject_mono,
      imageSubobject_mono, Subobject.mk_arrow, Subobject.mk_arrow]
    exact p.complementary.symm.sup_eq_top)

instance cover_isIso : IsIso p.cover :=
  isIso_of_regularEpi_of_mono _ (IsRegularEpi.getStruct _)

/-- Complementary subobjects exhibit their ambient object as their coproduct. -/
def isColimit : IsColimit (BinaryCofan.mk p.negative.arrow p.positive.arrow) :=
  (coprodIsCoprod (p.negative : C) (p.positive : C)).ofIsoColimit
    (BinaryCofan.ext (asIso p.cover) (by simp [cover]) (by simp [cover]))

/-- The characteristic morphism of the positive subobject, taking the negative subobject
to the lower truth value. -/
def characteristic : X ⟶ Two C :=
  BinaryCofan.IsColimit.desc p.isColimit (Two.constant _ false) (Two.constant _ true)

@[simp, reassoc]
theorem negative_characteristic : p.negative.arrow ≫ p.characteristic =
    Two.constant _ false :=
  BinaryCofan.IsColimit.inl_desc p.isColimit _ _

@[simp, reassoc]
theorem positive_characteristic : p.positive.arrow ≫ p.characteristic =
    Two.constant _ true :=
  BinaryCofan.IsColimit.inr_desc p.isColimit _ _

set_option backward.isDefEq.respectTransparency false in
theorem characteristic_isPullback :
    IsPullback p.negative.arrow (terminal.from _) p.characteristic (Two.point false) ∧
    IsPullback p.positive.arrow (terminal.from _) p.characteristic (Two.point true) := by
  have h := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ C) (⊤_ C)))
    (BinaryCofan.mk p.negative.arrow p.positive.arrow)
  exact (h
    (terminal.from _) (terminal.from _) p.characteristic
    (by simp [Two.constant, Two.point]) (by simp [Two.constant, Two.point])).mp ⟨p.isColimit⟩

/-- The lower fiber of the constructed characteristic morphism is the negative subobject. -/
theorem characteristic_negative : boundFiber p.characteristic (Two.point false) = p.negative := by
  rw [PresentationLemmas.boundFiber_eq_pullback,
    Subobject.pullback_obj_mk p.characteristic_isPullback.1.flip, Subobject.mk_arrow]

/-- The upper fiber of the constructed characteristic morphism is the positive subobject. -/
theorem characteristic_positive : boundFiber p.characteristic (Two.point true) = p.positive := by
  rw [PresentationLemmas.boundFiber_eq_pullback,
    Subobject.pullback_obj_mk p.characteristic_isPullback.2.flip, Subobject.mk_arrow]

/-- The characteristic morphism is uniquely specified by its values on the two subobjects. -/
theorem characteristic_unique (f : X ⟶ Two C)
    (hn : p.negative.arrow ≫ f = Two.constant _ false)
    (hp : p.positive.arrow ≫ f = Two.constant _ true) : f = p.characteristic :=
  BinaryCofan.IsColimit.hom_ext p.isColimit
    (hn.trans p.negative_characteristic.symm) (hp.trans p.positive_characteristic.symm)

omit [FinitaryExtensive C] in
/-- The fiber of a morphism carries its stated constant value. -/
theorem boundFiber_arrow_comp {B : C} (f : X ⟶ B) (b : ⊤_ C ⟶ B) :
    (boundFiber f b).arrow ≫ f = terminal.from _ ≫ b := by
  simpa only [boundFiber, ← Category.assoc, terminal.comp_from] using
    equalizerSubobject_arrow_comp f (terminal.from X ≫ b)

/-- The two fibers uniquely determine a characteristic morphism. -/
theorem characteristic_unique_of_fibers (f : X ⟶ Two C)
    (hn : boundFiber f (Two.point false) = p.negative)
    (hp : boundFiber f (Two.point true) = p.positive) : f = p.characteristic := by
  apply p.characteristic_unique f
  · have h := boundFiber_arrow_comp f (Two.point false)
    rw [hn] at h
    exact h
  · have h := boundFiber_arrow_comp f (Two.point true)
    rw [hp] at h
    exact h

end SubobjectPartition

omit [FinitaryExtensive C] in
/-- Postcomposition with a monomorphism does not change a corresponding bound fiber. -/
theorem boundFiber_mono_postcomp {X B B' : C} (f : X ⟶ B) (m : B ⟶ B') [Mono m]
    (b : ⊤_ C ⟶ B) : boundFiber (f ≫ m) (b ≫ m) = boundFiber f b := by
  apply le_antisymm
  · have h : equalizer.ι (f ≫ m) (terminal.from X ≫ (b ≫ m)) ≫ f =
        equalizer.ι (f ≫ m) (terminal.from X ≫ (b ≫ m)) ≫ (terminal.from X ≫ b) := by
      apply (cancel_mono m).mp
      simpa only [Category.assoc] using
        equalizer.condition (f ≫ m) (terminal.from X ≫ (b ≫ m))
    exact Subobject.mk_le_mk_of_comm (equalizer.lift _ h) (equalizer.lift_ι _ h)
  · exact boundFiber_le_postcomp f m b (b ≫ m) rfl

end CategoricalEssentialIncompleteness
