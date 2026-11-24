/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderIncompleteness

/-! # Statement checks for SignedFirstOrderIncompleteness -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

open LocalConnectedness
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (RestrictionSubobjects.Tot C)] [FinitaryExtensive (RestrictionSubobjects.Tot C)]
example (inverses : RestrictionSubobjects.MonoInverses C)
    {V X : RestrictionSubobjects.Tot C} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      Inseparable (RestrictionSubobjects.domain inverses a)
        (RestrictionSubobjects.domain inverses b) :=
  SignedFirstOrder.essential_incomplete_iff_inseparable inverses F a b hab hc

#print axioms SignedFirstOrder.essential_incomplete_iff_inseparable

section TotalSubobjects

open RestrictionSubobjects

variable {S : Type u} [Category.{v} S] [RestrictionCategory S] [Splits S]
  [Regular (Tot S)] [FinitaryExtensive (Tot S)]

example {V X : Tot S} (F : NullaryPresentations V) (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (consistent : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      ¬ ∃ p n : Subobject X, IsCompl p n ∧ a ≤ p ∧ b ≤ n := by
  have h := SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F a b hab consistent
  constructor
  · rintro ht ⟨p, n, hc, ha, hb⟩
    exact (h.mp ht).2 ⟨⟨p, n, hc⟩, ha, hb⟩
  · intro hs
    apply h.mpr
    refine ⟨hab, ?_⟩
    rintro ⟨p, ha, hb⟩
    exact hs ⟨p.positive, p.negative, p.complementary, ha, hb⟩

example (inv : MonoInverses S) {V X : Tot S} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      ¬ ∃ p n : Idem X.obj,
        (p ⊓ n = orderIso inv X ⊥ ∧
          orderIso inv X ((orderIso inv X).symm p ⊔ (orderIso inv X).symm n) = ⊤) ∧
        orderIso inv X a ≤ p ∧ orderIso inv X b ≤ n :=
  SignedFirstOrder.essential_incomplete_iff_no_complementary_domains inv F a b hab hc

example [HasZeroMorphisms S] [RestrictionZero S] [BinaryJoins S] (inv : MonoInverses S)
    (X : Tot S) (p n : Idem X.obj) :
    (p ⊓ n = orderIso inv X ⊥ ∧ (domainJoins inv).join p n = ⊤) ↔ Complementary p n :=
  complementaryDomains_iff_complementary inv X p n

end TotalSubobjects

section SplitDomains

open RestrictionSubobjects RecursionCategory

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
  [HasZeroMorphisms R] [Prodominical R] [Isotype R]
  [Regular (Tot (SplitObject R))] [FinitaryExtensive (Tot (SplitObject R))]
  (inverses : MonoInverses (SplitObject R))

example {X : Tot (SplitObject R)} (e f : Idem X.obj) :
    (domainJoins inverses).join e f =
      orderIso inverses X ((orderIso inverses X).symm e ⊔ (orderIso inverses X).symm f) := rfl

example (rec : PRecursionCategory R) {V X : Tot (SplitObject R)} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (consistent : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    letI := domainJoins inverses
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      ¬ ∃ p n : Idem X.obj, Complementary p n ∧ (orderIso inverses X) a ≤ p ∧
        (orderIso inverses X) b ≤ n :=
  SignedFirstOrder.essential_incomplete_iff_no_domain_separator rec inverses F a b hab consistent

end SplitDomains

#print axioms RestrictionSubobjects.domainJoins
#print axioms RestrictionSubobjects.complementaryDomains_iff
#print axioms RestrictionSubobjects.complementaryDomains_iff_complementary
#print axioms SignedFirstOrder.essential_incomplete_iff_no_complementary_domains
#print axioms SignedFirstOrder.essential_incomplete_iff_no_domain_separator
