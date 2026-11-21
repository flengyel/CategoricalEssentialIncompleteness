/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.CharacteristicArrows

/-!
# The internal Boolean algebra on `1 + 1`

Operations are morphisms, constructed by the universal coproduct decompositions. Their
identities are checked after restriction to truth-value fibers, not merely at global
points.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness
namespace Two

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

/-- A morphism obtained by choosing between two morphisms on the two fibers of `f`. -/
def branch {X Y : C} (f : X ⟶ Two C) (g₀ g₁ : X ⟶ Y) : X ⟶ Y :=
  BinaryCofan.IsColimit.desc (fibersIsColimit f)
    (fiberι f false ≫ g₀) (fiberι f true ≫ g₁)

theorem fiberι_branch {X Y : C} (f : X ⟶ Two C) (g₀ g₁ : X ⟶ Y) (b : Bool) :
    fiberι f b ≫ branch f g₀ g₁ = fiberι f b ≫ (if b then g₁ else g₀) := by
  cases b
  · exact BinaryCofan.IsColimit.inl_desc (fibersIsColimit f) _ _
  · exact BinaryCofan.IsColimit.inr_desc (fibersIsColimit f) _ _

/-- The branch equation holds for every morphism landing in a specified fiber. -/
theorem comp_branch {X Y Z : C} (f : X ⟶ Two C) (g₀ g₁ : X ⟶ Y)
    (k : Z ⟶ X) (b : Bool) (hk : k ≫ f = constant Z b) :
    k ≫ branch f g₀ g₁ = k ≫ (if b then g₁ else g₀) := by
  have he : k ≫ f = k ≫ constant X b := by simpa using hk
  let l := equalizer.lift k he
  have hl : l ≫ fiberι f b = k := equalizer.lift_ι _ _
  rw [← hl, Category.assoc, fiberι_branch, ← Category.assoc]

/-- A unary Boolean truth table represented by a morphism out of the coproduct. -/
def unary {X : C} (op : Bool → Bool) (f : X ⟶ Two C) : X ⟶ Two C :=
  f ≫ coprod.desc (point (op false)) (point (op true))

@[simp]
theorem comp_unary {X Y : C} (k : X ⟶ Y) (op : Bool → Bool) (f : Y ⟶ Two C) :
    k ≫ unary op f = unary op (k ≫ f) := by simp [unary]

@[simp]
theorem unary_constant (X : C) (op : Bool → Bool) (b : Bool) :
    unary op (constant X b) = constant X (op b) := by
  cases b <;> simp [unary, constant, point]

/-- The representing morphism of a binary Boolean truth table. -/
def binaryArrow (op : Bool → Bool → Bool) : Two C ⨯ Two C ⟶ Two C :=
  branch prod.fst (unary (op false) prod.snd) (unary (op true) prod.snd)

/-- A binary operation on generalized truth values. -/
def binary {X : C} (op : Bool → Bool → Bool) (f g : X ⟶ Two C) : X ⟶ Two C :=
  prod.lift f g ≫ binaryArrow op

@[simp]
theorem comp_binary {X Y : C} (k : X ⟶ Y) (op : Bool → Bool → Bool)
    (f g : Y ⟶ Two C) : k ≫ binary op f g = binary op (k ≫ f) (k ≫ g) := by
  simp [binary, ← Category.assoc, prod.comp_lift]

@[simp]
theorem binary_constant (X : C) (op : Bool → Bool → Bool) (a b : Bool) :
    binary op (constant X a) (constant X b) = constant X (op a b) := by
  unfold binary binaryArrow
  rw [comp_branch _ _ _ _ a (by simp)]
  cases a <;> simp

/-- Natural unary identities can be checked at the two constant truth values. -/
theorem check₁ {B : C} (F G : ∀ X : C, (X ⟶ Two C) → (X ⟶ B))
    (hF : ∀ {X Y : C} (k : X ⟶ Y) f, k ≫ F Y f = F X (k ≫ f))
    (hG : ∀ {X Y : C} (k : X ⟶ Y) f, k ≫ G Y f = G X (k ≫ f))
    (h : ∀ (X : C) (b : Bool), F X (constant X b) = G X (constant X b))
    (X : C) (f : X ⟶ Two C) : F X f = G X f := by
  apply hom_ext f <;> simp only [hF, hG, fiberι_comp] <;> apply h

/-- Natural binary identities can be checked at the four constant pairs. -/
theorem check₂ {B : C} (F G : ∀ X : C, (X ⟶ Two C) → (X ⟶ Two C) → (X ⟶ B))
    (hF : ∀ {X Y : C} (k : X ⟶ Y) f g, k ≫ F Y f g = F X (k ≫ f) (k ≫ g))
    (hG : ∀ {X Y : C} (k : X ⟶ Y) f g, k ≫ G Y f g = G X (k ≫ f) (k ≫ g))
    (h : ∀ (X : C) (a b : Bool), F X (constant X a) (constant X b) =
      G X (constant X a) (constant X b))
    (X : C) (f g : X ⟶ Two C) : F X f g = G X f g := by
  suffices hs : ∀ a : Bool, fiberι f a ≫ F X f g = fiberι f a ≫ G X f g from
    hom_ext f (hs false) (hs true)
  intro a
  simp only [hF, hG, fiberι_comp]
  apply hom_ext (fiberι f a ≫ g) <;>
    simp only [hF, hG, comp_constant, fiberι_comp] <;> apply h

/-- Natural ternary identities can be checked at the eight constant triples. -/
theorem check₃ {B : C}
    (F G : ∀ X : C, (X ⟶ Two C) → (X ⟶ Two C) → (X ⟶ Two C) → (X ⟶ B))
    (hF : ∀ {X Y : C} (k : X ⟶ Y) f g h,
      k ≫ F Y f g h = F X (k ≫ f) (k ≫ g) (k ≫ h))
    (hG : ∀ {X Y : C} (k : X ⟶ Y) f g h,
      k ≫ G Y f g h = G X (k ≫ f) (k ≫ g) (k ≫ h))
    (ht : ∀ (X : C) (a b c : Bool),
      F X (constant X a) (constant X b) (constant X c) =
      G X (constant X a) (constant X b) (constant X c))
    (X : C) (f g h : X ⟶ Two C) : F X f g h = G X f g h := by
  suffices hs : ∀ a : Bool, fiberι f a ≫ F X f g h = fiberι f a ≫ G X f g h from
    hom_ext f (hs false) (hs true)
  intro a
  simp only [hF, hG, fiberι_comp]
  exact check₂ (fun X g h ↦ F X (constant X a) g h)
    (fun X g h ↦ G X (constant X a) g h)
    (by intros; simp only [hF, comp_constant])
    (by intros; simp only [hG, comp_constant]) (fun X b c ↦ ht X a b c) _ _ _

theorem binary_comm (op : Bool → Bool → Bool) (hc : ∀ a b, op a b = op b a)
    {X : C} (f g : X ⟶ Two C) : binary op f g = binary op g f :=
  check₂ (fun _ f g ↦ binary op f g) (fun _ f g ↦ binary op g f)
    (by intros; simp) (by intros; simp) (by intros; simp [hc]) X f g

theorem binary_assoc (op : Bool → Bool → Bool)
    (ha : ∀ a b c, op (op a b) c = op a (op b c))
    {X : C} (f g h : X ⟶ Two C) :
    binary op (binary op f g) h = binary op f (binary op g h) :=
  check₃ (fun _ f g h ↦ binary op (binary op f g) h)
    (fun _ f g h ↦ binary op f (binary op g h))
    (by intros; simp) (by intros; simp) (by intros; simp [ha]) X f g h

local instance {X : C} : Max (X ⟶ Two C) := ⟨binary Bool.or⟩
local instance {X : C} : Min (X ⟶ Two C) := ⟨binary Bool.and⟩

/-- The lattice on generalized truth values, constructed from the Boolean truth tables. -/
@[instance_reducible]
def homLattice (X : C) : Lattice (X ⟶ Two C) :=
  Lattice.mk'
    (binary_comm Bool.or (by decide)) (binary_assoc Bool.or (by decide))
    (binary_comm Bool.and (by decide)) (binary_assoc Bool.and (by decide))
    (check₂ (fun _ f g ↦ binary Bool.or f (binary Bool.and f g)) (fun _ f _ ↦ f)
      (by intros; simp) (by intros; rfl)
      (by intro X a b; cases a <;> cases b <;> simp) X)
    (check₂ (fun _ f g ↦ binary Bool.and f (binary Bool.or f g)) (fun _ f _ ↦ f)
      (by intros; simp) (by intros; rfl)
      (by intro X a b; cases a <;> cases b <;> simp) X)

/-- Distributivity follows from its eight constant instances. -/
@[instance_reducible]
def homDistribLattice (X : C) : DistribLattice (X ⟶ Two C) := by
  letI := homLattice X
  exact { (inferInstance : Lattice (X ⟶ Two C)) with
    le_sup_inf := fun f g h ↦ (check₃
      (fun _ f g h ↦ binary Bool.and (binary Bool.or f g) (binary Bool.or f h))
      (fun _ f g h ↦ binary Bool.or f (binary Bool.and g h))
      (by intros; simp) (by intros; simp)
      (by intro X a b c; cases a <;> cases b <;> cases c <;> simp) X f g h).le }

theorem inf_neg {X : C} (f : X ⟶ Two C) :
    binary Bool.and f (unary Bool.not f) = constant X false :=
  check₁ (fun _ f ↦ binary Bool.and f (unary Bool.not f)) (fun X _ ↦ constant X false)
    (by intros; simp) (by intros; simp) (by intro X b; cases b <;> simp) X f

theorem sup_neg {X : C} (f : X ⟶ Two C) :
    binary Bool.or f (unary Bool.not f) = constant X true :=
  check₁ (fun _ f ↦ binary Bool.or f (unary Bool.not f)) (fun X _ ↦ constant X true)
    (by intros; simp) (by intros; simp) (by intro X b; cases b <;> simp) X f

/-- The Boolean algebra of all generalized truth values on `X`. -/
instance homBooleanAlgebra (X : C) : BooleanAlgebra (X ⟶ Two C) := by
  letI := homDistribLattice X
  exact { (inferInstance : DistribLattice (X ⟶ Two C)) with
    compl := unary Bool.not
    top := constant X true
    bot := constant X false
    inf_compl_le_bot := fun f ↦ (inf_neg f).le
    top_le_sup_compl := fun f ↦ (sup_neg f).ge
    le_top := fun f ↦ check₁ (fun X f ↦ binary Bool.or f (constant X true))
      (fun X _ ↦ constant X true) (by intros; simp) (by intros; simp)
      (by intro X b; cases b <;> simp) X f
    bot_le := fun f ↦ check₁ (fun X f ↦ binary Bool.or (constant X false) f)
      (fun _ f ↦ f) (by intros; simp) (by intros; rfl)
      (by intro X b; cases b <;> simp) X f }

@[simp] theorem sup_def {X : C} (f g : X ⟶ Two C) : f ⊔ g = binary Bool.or f g := rfl
@[simp] theorem inf_def {X : C} (f g : X ⟶ Two C) : f ⊓ g = binary Bool.and f g := rfl
@[simp] theorem compl_def {X : C} (f : X ⟶ Two C) : fᶜ = unary Bool.not f := rfl
@[simp] theorem bot_def (X : C) : (⊥ : X ⟶ Two C) = constant X false := rfl
@[simp] theorem top_def (X : C) : (⊤ : X ⟶ Two C) = constant X true := rfl

end Two

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

/-- The canonical internal Boolean algebra on the coproduct of two terminal objects. -/
def twoBooleanObject : BooleanObject C where
  obj := Two C
  algebra := Two.homBooleanAlgebra
  precomp f :=
    { toFun := fun g ↦ f ≫ g
      map_sup' := by intros; exact Two.comp_binary _ _ _ _
      map_inf' := by intros; exact Two.comp_binary _ _ _ _
      map_top' := Two.comp_constant _ _
      map_bot' := Two.comp_constant _ _ }
  precomp_apply _ _ := rfl

@[simp]
theorem twoBooleanObject_bot :
    (⊥ : ⊤_ C ⟶ (twoBooleanObject (C := C)).obj) = Two.point false := by
  change Two.constant _ false = _
  rw [Two.constant, terminalIsTerminal.hom_ext (terminal.from _) (𝟙 _), Category.id_comp]

@[simp]
theorem twoBooleanObject_top :
    (⊤ : ⊤_ C ⟶ (twoBooleanObject (C := C)).obj) = Two.point true := by
  change Two.constant _ true = _
  rw [Two.constant, terminalIsTerminal.hom_ext (terminal.from _) (𝟙 _), Category.id_comp]

@[simp]
theorem twoBooleanObject_boundCopair :
    (twoBooleanObject (C := C)).boundCopair = 𝟙 (Two C) := by
  rw [BooleanObject.boundCopair, twoBooleanObject_bot, twoBooleanObject_top]
  change coprod.desc coprod.inl coprod.inr = 𝟙 (Two C)
  apply coprod.hom_ext <;> simp

namespace BooleanObject

variable (B : BooleanObject C)

@[simp]
theorem constant_boundCopair (X : C) (b : Bool) :
    Two.constant X b ≫ B.boundCopair = if b then ⊤ else ⊥ := by
  cases b <;> simp [Two.constant, Two.point, boundCopair, constant_bot, constant_top]

/-- The canonical morphism from `1 + 1` to an internal Boolean algebra preserves all
Boolean operations on generalized elements. -/
def boundMorphism : BooleanMorphism (twoBooleanObject (C := C)) B where
  hom := B.boundCopair
  postcomp X :=
    { toFun := fun f ↦ f ≫ B.boundCopair
      map_sup' := Two.check₂
        (fun _ f g ↦ Two.binary Bool.or f g ≫ B.boundCopair)
        (fun _ f g ↦ (f ≫ B.boundCopair) ⊔ (g ≫ B.boundCopair))
        (by intros; simp [← Category.assoc])
        (by
          intro X Y k f g
          rw [← B.precomp_apply, map_sup, B.precomp_apply, B.precomp_apply]
          simp)
        (by intro X a b; cases a <;> cases b <;> simp) X
      map_inf' := Two.check₂
        (fun _ f g ↦ Two.binary Bool.and f g ≫ B.boundCopair)
        (fun _ f g ↦ (f ≫ B.boundCopair) ⊓ (g ≫ B.boundCopair))
        (by intros; simp [← Category.assoc])
        (by
          intro X Y k f g
          rw [← B.precomp_apply, map_inf, B.precomp_apply, B.precomp_apply]
          simp)
        (by intro X a b; cases a <;> cases b <;> simp) X
      map_top' := B.constant_boundCopair X true
      map_bot' := B.constant_boundCopair X false }
  postcomp_apply _ _ := rfl

end BooleanObject

end CategoricalEssentialIncompleteness
