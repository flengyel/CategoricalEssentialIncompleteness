/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability
public import CategoricalEssentialIncompleteness.V46SplitSplittings
public import CategoricalEssentialIncompleteness.RestrictionCompatibility

/-! # Corollary 4.8: essential incompleteness of free signed theories -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46

namespace RestrictionSubobjects

/-- Transport the binary join of total subobjects across the subobject–domain
order isomorphism used in Corollary 4.8. -/
@[instance_reducible] def domainJoins {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
    [Regular (Tot C)] [FinitaryExtensive (Tot C)] (inverses : MonoInverses C) :
    BinaryJoins C where
  join {X} e f :=
    let φ := orderIso inverses (⟨X⟩ : Tot C)
    φ (φ.symm e ⊔ φ.symm f)
  le_left {X} e f := by
    let φ := orderIso inverses (⟨X⟩ : Tot C)
    calc
      e = φ (φ.symm e) := (φ.apply_symm_apply e).symm
      _ ≤ φ (φ.symm e ⊔ φ.symm f) := φ.monotone le_sup_left
  le_right {X} e f := by
    let φ := orderIso inverses (⟨X⟩ : Tot C)
    calc
      f = φ (φ.symm f) := (φ.apply_symm_apply f).symm
      _ ≤ φ (φ.symm e ⊔ φ.symm f) := φ.monotone le_sup_right
  least {X} e f g he hf := by
    let φ := orderIso inverses (⟨X⟩ : Tot C)
    calc
      φ (φ.symm e ⊔ φ.symm f) ≤ φ (φ.symm g) :=
        φ.monotone (sup_le (φ.symm.monotone he) (φ.symm.monotone hf))
      _ = g := φ.apply_symm_apply g

end RestrictionSubobjects

namespace SignedFirstOrder

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (RestrictionSubobjects.Tot C)] [FinitaryExtensive (RestrictionSubobjects.Tot C)]

/-- The Boolean extension gives the converse; the subobject/domain order
isomorphism identifies the two notions of inseparability. -/
theorem essential_incomplete_iff_inseparable
    (inverses : RestrictionSubobjects.MonoInverses C)
    {V X : RestrictionSubobjects.Tot C} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (consistent : (F.presentation X).Consistent (theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (theory F a b) ↔
      Inseparable (RestrictionSubobjects.domain inverses a)
        (RestrictionSubobjects.domain inverses b) :=
  (essential_incomplete_iff_subobject_inseparable F a b hab consistent).trans
    (RestrictionSubobjects.inseparable_iff inverses a b).symm

open RestrictionSubobjects RecursionCategory

/-- Corollary 4.8 in the restriction splitting of a recursion category. The
signed theory on a disjoint pair is essentially incomplete precisely when no
complementary restriction domains separate that pair. -/
theorem essential_incomplete_iff_no_domain_separator
    {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
    [HasZeroMorphisms R] [Prodominical R] [Isotype R] (_rec : PRecursionCategory R)
    [Regular (Tot (SplitObject R))] [FinitaryExtensive (Tot (SplitObject R))]
    (inverses : MonoInverses (SplitObject R)) {V X : Tot (SplitObject R)}
    (F : NullaryPresentations V) (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (consistent : (F.presentation X).Consistent (theory F a b).val) :
    letI := domainJoins inverses
    (F.presentation X).EssentiallyIncomplete (theory F a b) ↔
      ¬ ∃ c c' : Idem X.obj, Complementary c c' ∧ domain inverses a ≤ c ∧
        domain inverses b ≤ c' := by
  let _ := domainJoins inverses
  have h := essential_incomplete_iff_inseparable inverses F a b hab consistent
  refine ⟨fun ht => (h.mp ht).no_separator, fun hs => h.mpr ⟨?_, hs⟩⟩
  let φ := orderIso inverses X
  change φ a ⊓ φ b = ⊥
  rw [← φ.map_inf, hab, φ.map_bot]

end SignedFirstOrder
end CategoricalEssentialIncompleteness.V46
