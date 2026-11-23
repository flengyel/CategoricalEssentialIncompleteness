/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-! # A proper subobject containing every global point (after Corollary 4.3)

For a nontrivial group, the left regular action has no fixed point. Thus all
global points of the coproduct of a singleton and the regular action factor
through the first inclusion.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoricalEssentialIncompleteness.V46.RegularActionPoints

variable (G : Type u) [Group G]

abbrev singleton := Action.ofMulAction G PUnit.{u+1}

abbrev sumAction := Action.ofMulAction G (PUnit.{u+1} ⊕ G)

def singletonIsTerminal : IsTerminal (singleton G) :=
  IsTerminal.ofUniqueHom (fun _ => ⟨↾fun _ => PUnit.unit, fun _ => rfl⟩)
    fun _ _ => Action.hom_injective
      (ConcreteCategory.hom_ext _ _ fun _ => @Subsingleton.elim PUnit _ _ _)

def inclusion : singleton G ⟶ sumAction G :=
  ⟨↾Sum.inl, fun _ => rfl⟩

def regularInclusion : Action.leftRegular G ⟶ sumAction G :=
  ⟨↾Sum.inr, fun _ => rfl⟩

/-- The sum of the underlying sets, with its componentwise action, is a coproduct in G-sets. -/
def sumIsColimit : IsColimit (BinaryCofan.mk (inclusion G) (regularInclusion G)) := by
  apply BinaryCofan.isColimitMk (inl := inclusion G) (inr := regularInclusion G)
    (fun s => ⟨↾(Sum.elim s.inl.hom s.inr.hom), fun g => by
    apply ConcreteCategory.hom_ext
    rintro (x | y)
    · exact ConcreteCategory.congr_hom (s.inl.comm g) x
    · exact ConcreteCategory.congr_hom (s.inr.comm g) y⟩)
  · intro s
    rfl
  · intro s
    rfl
  · intro s m hl hr
    apply Action.hom_injective
    apply ConcreteCategory.hom_ext
    rintro (x | y)
    · exact ConcreteCategory.congr_hom (congrArg Action.Hom.hom hl) x
    · exact ConcreteCategory.congr_hom (congrArg Action.Hom.hom hr) y

theorem inclusion_mono : Mono (inclusion G) where
  right_cancellation f g _ := (singletonIsTerminal G).hom_ext f g

theorem inclusion_not_iso : ¬ IsIso (inclusion G) := by
  intro h
  have he := congrArg (fun k : sumAction G ⟶ sumAction G => k.hom (Sum.inr (1 : G) : PUnit ⊕ G))
    (IsIso.inv_hom_id (inclusion G))
  change Sum.inl _ = Sum.inr (1 : G) at he
  cases he

/-- An equivariant map from the singleton picks a fixed point. A fixed point
in the regular summand would make every group element the identity. -/
theorem globalPoint_factors [Nontrivial G] (p : singleton G ⟶ sumAction G) :
    ∃ q : singleton G ⟶ singleton G, q ≫ inclusion G = p := by
  refine ⟨𝟙 _, ?_⟩
  rw [Category.id_comp]
  apply Action.hom_injective
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  cases hp : p.hom PUnit.unit with
  | inl x => cases x; rfl
  | inr a =>
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have he := ConcreteCategory.congr_hom (p.comm g) PUnit.unit
    change p.hom PUnit.unit = (sumAction G).ρ g (p.hom PUnit.unit) at he
    rw [hp] at he
    change (Sum.inr a : PUnit ⊕ G) = Sum.inr (g * a) at he
    have hga : g * a = 1 * a := (Sum.inr.inj he).symm.trans (one_mul a).symm
    exact (hg (mul_right_cancel hga)).elim

end CategoricalEssentialIncompleteness.V46.RegularActionPoints
