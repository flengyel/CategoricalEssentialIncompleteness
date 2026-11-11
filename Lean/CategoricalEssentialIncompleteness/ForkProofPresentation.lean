/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofLeaves

/-! # The categorical finite-proof presentation and its consistency -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (V natCarrier centerIdem leftIdem rightIdem)
open EnumerableCarriers (support support_re val)

theorem decode_atomCode (x : ℕ) : Formula.decode (atomCode x)=.atom x :=
  Formula.decode_encode (.atom x)

theorem decode_negCode (x : ℕ) : Formula.decode (negCode x)=.neg (Formula.decode x) := by
  change Formula.decode (3*x+1)=.neg (Formula.decode x)
  have h := Formula.decode_encode (.neg (Formula.decode x))
  simpa only [Formula.encode,Formula.encode_decode] using h

theorem support_disjoint {X : EnumerableCarriers.Carrier} {a b : Idem X}
    (h : a ⊓ b=⊥) : Disjoint (support a) (support b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hm : x ∈ support (a ⊓ b) := by
    rw [EnumerableCarriers.support_inf]
    exact ⟨hx,hy⟩
  simpa only [h,EnumerableCarriers.support_bot,Set.mem_empty_iff_false] using hm

theorem numerical_positive (a b : Idem natCarrier) :
    a ≤ Idem.pull (natArrow atomCode atomCode_computable)
      (Ranges.range (conclusionArrow (support a) (support b) (support_re a) (support_re b))) := by
  apply (EnumerableCarriers.support_le_iff _ _).mpr
  intro x hx
  rw [EnumerableCarriers.support_pull]
  refine ⟨atomCode x,(mem_natArrow _ _ _ _).mpr rfl,?_⟩
  rw [conclusion_range,decode_atomCode]
  exact ⟨.positive x,Concludes.positive hx⟩

theorem numerical_negative (a b : Idem natCarrier) :
    b ≤ Idem.pull (natArrow atomCode atomCode_computable)
      (Idem.pull (natArrow negCode negCode_computable)
        (Ranges.range (conclusionArrow (support a) (support b) (support_re a) (support_re b)))) := by
  apply (EnumerableCarriers.support_le_iff _ _).mpr
  intro x hx
  rw [EnumerableCarriers.support_pull]
  refine ⟨atomCode x,(mem_natArrow _ _ _ _).mpr rfl,?_⟩
  rw [EnumerableCarriers.support_pull]
  refine ⟨negCode (atomCode x),(mem_natArrow _ _ _ _).mpr rfl,?_⟩
  rw [conclusion_range,decode_negCode,decode_atomCode]
  exact ⟨.negative x,Concludes.negative hx⟩

theorem numerical_consistency (a b : Idem natCarrier) (hd : a ⊓ b=⊥) :
    let T := Ranges.range (conclusionArrow (support a) (support b) (support_re a) (support_re b))
    T ⊓ Idem.pull (natArrow negCode negCode_computable) T=⊥ := by
  dsimp only
  apply EnumerableCarriers.support_injective
  ext x
  rw [EnumerableCarriers.support_inf,EnumerableCarriers.support_bot,
    Set.mem_inter_iff,Set.mem_empty_iff_false]
  constructor
  · rintro ⟨hx,hy⟩
    rw [EnumerableCarriers.support_pull] at hy
    obtain ⟨y,hy,hyt⟩ := hy
    rw [(mem_natArrow _ _ x y).mp hy,conclusion_range,decode_negCode] at hyt
    exact finite_valuation_consistency (support_disjoint hd) (Formula.decode x)
      ⟨(conclusion_range _ _ _ _ x).mp hx,hyt⟩
  · exact False.elim

theorem positive_inclusion (a b : Idem V) : a ≤ Idem.pull theta (t0 a b) :=
  (EffectiveFork.idem_le_iff _ _).mpr ⟨numerical_positive _ _,
    numerical_positive _ _,numerical_positive _ _⟩

theorem negative_inclusion (a b : Idem V) :
    b ≤ Idem.pull theta (Idem.pull nu (t0 a b)) :=
  (EffectiveFork.idem_le_iff _ _).mpr ⟨numerical_negative _ _,
    numerical_negative _ _,numerical_negative _ _⟩

theorem t0_consistency (a b : Idem V) (hd : a ⊓ b=⊥) :
    t0 a b ⊓ Idem.pull nu (t0 a b)=⊥ :=
  EffectiveFork.idem_ext
    (numerical_consistency _ _ (congrArg centerIdem hd))
    (numerical_consistency _ _ (congrArg leftIdem hd))
    (numerical_consistency _ _ (congrArg rightIdem hd))

/-- The component closure conditions for a candidate theorem subfunctor. -/
structure HilbertTheory (A B : Set ℕ) (T : Set Formula) : Prop where
  logical1 : ∀ p q,H1 p q ∈ T
  logical2 : ∀ p q r,H2 p q r ∈ T
  logical3 : ∀ p q,H3 p q ∈ T
  positive : ∀ x ∈ A,Formula.atom x ∈ T
  negative : ∀ x ∈ B,Formula.neg (.atom x) ∈ T
  mp : ∀ p q,p ∈ T → Formula.imp p q ∈ T → q ∈ T

theorem theorems_hilbert (A B : Set ℕ) : HilbertTheory A B (Theorems A B) where
  logical1 p q := ⟨_,Concludes.logical1 p q⟩
  logical2 p q r := ⟨_,Concludes.logical2 p q r⟩
  logical3 p q := ⟨_,Concludes.logical3 p q⟩
  positive x hx := ⟨_,Concludes.positive hx⟩
  negative x hx := ⟨_,Concludes.negative hx⟩
  mp p q hp hq := by
    obtain ⟨t,ht⟩ := hp
    obtain ⟨u,hu⟩ := hq
    exact ⟨.mp t u,Concludes.mp ht hu⟩

def formulasOf (e : Idem natCarrier) : Set Formula := {p | p.encode ∈ support e}

theorem numerical_least (a b : Idem natCarrier) (e : Idem natCarrier)
    (he : HilbertTheory (support a) (support b) (formulasOf e)) :
    Ranges.range (conclusionArrow (support a) (support b) (support_re a) (support_re b)) ≤ e := by
  apply (EnumerableCarriers.support_le_iff _ _).mpr
  intro n hn
  have h := theorem_least he.logical1 he.logical2 he.logical3 he.positive he.negative he.mp
    ((conclusion_range _ _ _ _ n).mp hn)
  change (Formula.decode n).encode ∈ support e at h
  simpa only [Formula.encode_decode] using h

theorem t0_least (a b : Idem V) (e : Idem S)
    (h0 : HilbertTheory (support (centerIdem a)) (support (centerIdem b))
      (formulasOf (centerIdem e)))
    (h1 : HilbertTheory (support (leftIdem a)) (support (leftIdem b))
      (formulasOf (leftIdem e)))
    (h2 : HilbertTheory (support (rightIdem a)) (support (rightIdem b))
      (formulasOf (rightIdem e))) : t0 a b ≤ e :=
  (EffectiveFork.idem_le_iff _ _).mpr ⟨numerical_least _ _ _ h0,
    numerical_least _ _ _ h1,numerical_least _ _ _ h2⟩

def IsTheory (a b : Idem V) (e : Idem S) : Prop :=
  HilbertTheory (support (centerIdem a)) (support (centerIdem b)) (formulasOf (centerIdem e)) ∧
  HilbertTheory (support (leftIdem a)) (support (leftIdem b)) (formulasOf (leftIdem e)) ∧
  HilbertTheory (support (rightIdem a)) (support (rightIdem b)) (formulasOf (rightIdem e))

theorem numerical_range_theory (a b : Idem natCarrier) :
    HilbertTheory (support a) (support b)
      (formulasOf (Ranges.range (conclusionArrow (support a) (support b) (support_re a) (support_re b)))) := by
  have he : formulasOf (Ranges.range
      (conclusionArrow (support a) (support b) (support_re a) (support_re b)))=
      Theorems (support a) (support b) := by
    ext p
    change p.encode ∈ support (Ranges.range _) ↔ _
    rw [conclusion_range,Formula.decode_encode]
  rw [he]
  exact theorems_hilbert _ _

theorem t0_isTheory (a b : Idem V) : IsTheory a b (t0 a b) :=
  ⟨numerical_range_theory _ _,numerical_range_theory _ _,numerical_range_theory _ _⟩

theorem t0_isLeast (a b : Idem V) : IsLeast {e | IsTheory a b e} (t0 a b) :=
  ⟨t0_isTheory a b,fun _ he => t0_least a b _ he.1 he.2.1 he.2.2⟩

/-- The three categorical assertions of Appendix B's proof presentation. -/
theorem proof_presentation (a b : Idem V) (hd : a ⊓ b=⊥) :
    a ≤ Idem.pull theta (t0 a b) ∧ b ≤ Idem.pull theta (Idem.pull nu (t0 a b)) ∧
      t0 a b ⊓ Idem.pull nu (t0 a b)=⊥ :=
  ⟨positive_inclusion a b,negative_inclusion a b,t0_consistency a b hd⟩

/-- The full numbered proof-presentation statement, including leastness. -/
theorem fork_proof_presentation (a b : Idem V) (hd : a ⊓ b=⊥) :
    IsLeast {e | IsTheory a b e} (t0 a b) ∧
      a ≤ Idem.pull theta (t0 a b) ∧ b ≤ Idem.pull theta (Idem.pull nu (t0 a b)) ∧
        t0 a b ⊓ Idem.pull nu (t0 a b)=⊥ :=
  ⟨t0_isLeast a b,proof_presentation a b hd⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
