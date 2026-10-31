/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableLocalConnectedness
import CategoricalEssentialIncompleteness.ForkSyntaxObjects
import CategoricalEssentialIncompleteness.NumericalInseparability

/-! # From numerical domain inseparability to recursive set inseparability -/

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

section Extension
variable {C : Type} [Category C] [RestrictionCategory C]
variable [CategoryTheory.Limits.HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

theorem Inseparable.enlarge {X : C} {a b p n : Idem X} (h : Inseparable a b)
    (ha : a ≤ p) (hb : b ≤ n) (hd : p ⊓ n=⊥) : Inseparable p n := by
  refine ⟨hd,?_⟩
  rintro ⟨c,c',hc,hp,hn⟩
  exact h.no_separator ⟨c,c',hc,ha.trans hp,hb.trans hn⟩
end Extension

namespace EnumerableCarriers
open EffectiveFork (natCarrier)

def recursiveSeparator (D : Set ℕ) (hD : ComputablePred (· ∈ D)) : Idem natCarrier :=
  relativeIdem D hD.to_re (Set.subset_univ D)

theorem recursiveSeparator_support (D : Set ℕ) (hD : ComputablePred (· ∈ D)) :
    support (recursiveSeparator D hD)=D := support_relativeIdem _ _ _

theorem recursiveSeparator_complementary (D : Set ℕ) (hD : ComputablePred (· ∈ D)) :
    Complementary (recursiveSeparator D hD) (recursiveSeparator Dᶜ hD.not) := by
  constructor
  · apply support_injective
    rw [support_inf,recursiveSeparator_support,recursiveSeparator_support,support_bot]
    exact Set.inter_compl_self D
  · apply support_injective
    rw [support_sup,recursiveSeparator_support,recursiveSeparator_support,support_top]
    exact Set.union_compl_self D

theorem supports_recursivelyInseparable {a b : Idem natCarrier} (h : Inseparable a b) :
    Numerical.RecursivelyInseparable (support a) (support b) := by
  constructor
  · apply Set.disjoint_iff_inter_eq_empty.mpr
    have he := congrArg support h.disjoint
    simpa only [support_inf,support_bot] using he
  · rintro ⟨D,hD,ha,hb⟩
    apply h.no_separator
    refine ⟨recursiveSeparator D hD,recursiveSeparator Dᶜ hD.not,
      recursiveSeparator_complementary D hD,?_,?_⟩
    · rw [support_le_iff,recursiveSeparator_support]
      exact ha
    · rw [support_le_iff,recursiveSeparator_support]
      intro x hx hxd
      exact Set.disjoint_left.mp hb hxd hx

end EnumerableCarriers
end CategoricalEssentialIncompleteness.LocalConnectedness
