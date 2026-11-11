/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.InternalCartesian
public import PCats.Restriction

/-!
# Restriction hom-objects and their finite-limit subobjects

The restriction equations are equations at every generalized element. They
induce an instance of the existing `RestrictionCategory` API at each parameter.
The domain object is the fixed-point equalizer of restriction; the total-arrow
object is its pullback along the identity. Their generalized points are proved
to be exactly the restriction idempotents and total arrows, respectively.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

/-- Enriched category and restriction equations on the given hom-objects.
The pairing operations in `H` are not assumed to be categorical products here. -/
structure EnrichedRestriction {V : Type u} [Category.{v} V] [HasFiniteLimits V]
    {O : Type w} (H : InternalHom V O) where
  restriction : ∀ X Y, H.hom X Y ⟶ H.hom X X
  assoc : ∀ {T X Y Z W} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z)
    (h : T ⟶ H.hom Z W), H.comp (H.comp f g) h = H.comp f (H.comp g h)
  id_comp : ∀ {T X Y} (f : T ⟶ H.hom X Y), H.comp (H.identity X) f = f
  comp_id : ∀ {T X Y} (f : T ⟶ H.hom X Y), H.comp f (H.identity Y) = f
  rst_comp_self : ∀ {T X Y} (f : T ⟶ H.hom X Y),
    H.comp (f ≫ restriction X Y) f = f
  rst_comm : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (f ≫ restriction X Y) (g ≫ restriction X Z) =
      H.comp (g ≫ restriction X Z) (f ≫ restriction X Y)
  rst_comp_rst : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (f ≫ restriction X Y) g ≫ restriction X Z =
      H.comp (f ≫ restriction X Y) (g ≫ restriction X Z)
  rst_comp : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z),
    H.comp (H.comp f g ≫ restriction X Z) f = H.comp f (g ≫ restriction Y Z)

namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H)

/-- The objects of the category whose arrows have parameter `T`. -/
structure Parameterized (R : EnrichedRestriction H) (T : V) where
  obj : O

instance parameterizedCategory (T : V) : Category (R.Parameterized T) where
  Hom X Y := T ⟶ H.hom X.obj Y.obj
  id X := H.identity X.obj
  comp f g := H.comp f g
  id_comp := R.id_comp
  comp_id := R.comp_id
  assoc := R.assoc

def restrict {T : V} {X Y : O} (f : T ⟶ H.hom X Y) : T ⟶ H.hom X X :=
  f ≫ R.restriction X Y

instance parameterizedRestriction (T : V) : RestrictionCategory (R.Parameterized T) where
  rst := R.restrict
  rst_comp_self := R.rst_comp_self
  rst_comm := R.rst_comm
  rst_comp_rst := R.rst_comp_rst
  rst_comp := R.rst_comp

@[simp] theorem restrict_identity {T : V} (X : O) :
    R.restrict (H.identity (T := T) X) = H.identity X :=
  RestrictionCategory.rst_id (C := R.Parameterized T) ⟨X⟩

/-- Restriction takes values in its own fixed points, derived from R3. -/
@[simp] theorem restrict_restrict {T : V} {X Y : O} (f : T ⟶ H.hom X Y) :
    R.restrict (R.restrict f) = R.restrict f := by
  have h := R.rst_comp_rst f (H.identity X)
  change R.restrict (H.comp (R.restrict f) (H.identity X)) =
    H.comp (R.restrict f) (R.restrict (H.identity X)) at h
  rw [R.comp_id, R.restrict_identity, R.comp_id] at h
  exact h

@[simp] theorem precomp_restrict {T T' : V} (k : T' ⟶ T) {X Y : O}
    (f : T ⟶ H.hom X Y) : k ≫ R.restrict f = R.restrict (k ≫ f) :=
  (Category.assoc _ _ _).symm

theorem restrict_comp_of_total {T : V} {X Y Z : O}
    (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z)
    (hg : R.restrict g = H.identity Y) : R.restrict (H.comp f g) = R.restrict f :=
  RestrictionCategory.rst_comp_of_isTotal (C := R.Parameterized T)
    (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) f hg

theorem total_comp {T : V} {X Y Z : O} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z)
    (hf : R.restrict f = H.identity X) (hg : R.restrict g = H.identity Y) :
    R.restrict (H.comp f g) = H.identity X := (R.restrict_comp_of_total f g hg).trans hf

/-- The manuscript's equalizer `E_X`. -/
abbrev domainObject (X : O) : V := equalizer (R.restriction X X) (𝟙 (H.hom X X))
def domainι (X : O) : R.domainObject X ⟶ H.hom X X := equalizer.ι _ _

instance domainι_mono (X : O) : Mono (R.domainι X) := by
  dsimp [domainι]; infer_instance

@[simp] theorem domain_condition {T : V} {X : O} (e : T ⟶ R.domainObject X) :
    R.restrict (e ≫ R.domainι X) = e ≫ R.domainι X := by
  simp only [restrict, domainι, Category.assoc, equalizer.condition, Category.comp_id]

def domainLift {T : V} {X : O} (e : T ⟶ H.hom X X) (he : R.restrict e = e) :
    T ⟶ R.domainObject X := equalizer.lift e (by simpa [restrict] using he)

@[simp, reassoc] theorem domainLift_ι {T : V} {X : O}
    (e : T ⟶ H.hom X X) (he : R.restrict e = e) :
    R.domainLift e he ≫ R.domainι X = e := by simp [domainLift, domainι]

/-- Generalized points of `E_X` are precisely the restriction idempotents. -/
def domainPointsEquiv (T : V) (X : O) :
    (T ⟶ R.domainObject X) ≃ {e : T ⟶ H.hom X X // R.restrict e = e} where
  toFun e := ⟨e ≫ R.domainι X, R.domain_condition e⟩
  invFun e := R.domainLift e.val e.property
  left_inv e := by apply (cancel_mono (R.domainι X)).mp; simp
  right_inv e := by apply Subtype.ext; simp

/-- The manuscript's pullback `T(X,Y)`. -/
abbrev totalObject (X Y : O) : V := pullback (R.restriction X Y) (H.unit X)
def totalι (X Y : O) : R.totalObject X Y ⟶ H.hom X Y := pullback.fst _ _

/-- A global point is monic because its source is terminal. -/
instance unit_mono (X : O) : Mono (H.unit X) where
  right_cancellation f g _ := terminalIsTerminal.hom_ext f g

instance totalι_mono (X Y : O) : Mono (R.totalι X Y) := by
  dsimp [totalι]; infer_instance

@[simp] theorem total_condition {T : V} {X Y : O} (f : T ⟶ R.totalObject X Y) :
    R.restrict (f ≫ R.totalι X Y) = H.identity X := by
  rw [restrict, totalι, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ H.unit X) (terminalIsTerminal.hom_ext _ _)

def totalLift {T : V} {X Y : O} (f : T ⟶ H.hom X Y)
    (hf : R.restrict f = H.identity X) : T ⟶ R.totalObject X Y :=
  pullback.lift f (terminal.from T) hf

@[simp, reassoc] theorem totalLift_ι {T : V} {X Y : O}
    (f : T ⟶ H.hom X Y) (hf : R.restrict f = H.identity X) :
    R.totalLift f hf ≫ R.totalι X Y = f := by simp [totalLift, totalι]

/-- Generalized points of the totality pullback are precisely total arrows. -/
def totalPointsEquiv (T : V) (X Y : O) :
    (T ⟶ R.totalObject X Y) ≃ {f : T ⟶ H.hom X Y // R.restrict f = H.identity X} where
  toFun f := ⟨f ≫ R.totalι X Y, R.total_condition f⟩
  invFun f := R.totalLift f.val f.property
  left_inv f := by apply (cancel_mono (R.totalι X Y)).mp; simp
  right_inv f := by apply Subtype.ext; simp

end EnrichedRestriction
end CategoricalEssentialIncompleteness
