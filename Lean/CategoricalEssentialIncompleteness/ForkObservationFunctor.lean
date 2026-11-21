/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkObservedIncompleteness
public import CategoricalEssentialIncompleteness.RecursivePairs
public import CategoricalEssentialIncompleteness.ClassicalPairCoding

/-! # Covariant observations on the poset of consistent theory extensions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (natCarrier centerIdem leftIdem rightIdem)
open EnumerableCarriers (support val)

def MPClosed (t : Idem natCarrier) : Prop :=
  ∀ p q : Formula,p.encode ∈ support t → (Formula.imp p q).encode ∈ support t → q.encode ∈ support t

/-- Exactly the manuscript's consistent c.e. subfunctor theories extending t0. -/
abbrev Theory := {t : Idem S // categoricalTheory ≤ t ∧ t ⊓ Idem.pull nu t=⊥ ∧
  MPClosed (centerIdem t) ∧ MPClosed (leftIdem t) ∧ MPClosed (rightIdem t)}

def tuplePositive (i : Bool) (t : Idem S) : Idem ClassicalPrograms.U2 :=
  Idem.pull ClassicalPrograms.pairCodeIso.hom
    (ClassicalPrograms.supportIdem (support (observedPositive i t)) (observed_enumerable i t).1)

def tupleNegative (i : Bool) (t : Idem S) : Idem ClassicalPrograms.U2 :=
  Idem.pull ClassicalPrograms.pairCodeIso.hom
    (ClassicalPrograms.supportIdem (support (observedNegative i t)) (observed_enumerable i t).2)

def observedPair (i : Bool) (t : Theory) : RecursivePairs.Object where
  carrier := ClassicalPrograms.U2
  positive := tuplePositive i t.val
  negative := tupleNegative i t.val
  disjoint := by
    change Idem.pull _ _ ⊓ Idem.pull _ _=⊥
    rw [← Idem.pull_inf,RecursivePairs.supportIdems_disjoint _ _ _ _
      (support_disjoint (observed_disjoint i t.val t.property.2.1)),Idem.pull_bot]

def observationFunctor (i : Bool) : Theory ⥤ RecursivePairs.Object where
  obj t := observedPair i t
  map {t t'} f :=
    { map := 𝟙 ClassicalPrograms.U2
      total := rst_id _
      positive := by
        change tuplePositive i t.val ≤ Idem.pull (𝟙 ClassicalPrograms.U2) (tuplePositive i t'.val)
        rw [Idem.pull_id]
        apply Idem.pull_mono ClassicalPrograms.pairCodeIso.hom
        apply ClassicalPrograms.supportIdem_le
        exact (EnumerableCarriers.support_le_iff _ _).mp
          (observedPositive_mono i (show t.val ≤ t'.val from leOfHom f))
      negative := by
        change tupleNegative i t.val ≤ Idem.pull (𝟙 ClassicalPrograms.U2) (tupleNegative i t'.val)
        rw [Idem.pull_id]
        apply Idem.pull_mono ClassicalPrograms.pairCodeIso.hom
        apply ClassicalPrograms.supportIdem_le
        exact (EnumerableCarriers.support_le_iff _ _).mp
          (observedNegative_mono i (show t.val ≤ t'.val from leOfHom f)) }
  map_id t := by apply RecursivePairs.Hom.ext; rfl
  map_comp f g := by
    apply RecursivePairs.Hom.ext
    exact (Category.id_comp (𝟙 ClassicalPrograms.U2)).symm

/-- The theorem and refutation domains of a theory are inseparable and do not cover the
sentence object. At either endpoint their observed atomic supports are recursively
inseparable. -/
theorem coded_observation (i : Bool) (t : Theory) :
    Inseparable t.val (Idem.pull nu t.val) ∧
      Numerical.RecursivelyInseparable (support (observedPositive i t.val))
        (support (observedNegative i t.val)) ∧ t.val ⊔ Idem.pull nu t.val≠⊤ :=
  ⟨(essential_incompleteness t.val t.property.1 t.property.2.1).1,
    observed_recursivelyInseparable i t.val t.property.1 t.property.2.1,
    (essential_incompleteness t.val t.property.1 t.property.2.1).2⟩

def tuplePositiveSet (i : Bool) (t : Idem S) : Set (ℕ × ℕ) :=
  {x | Nat.pair x.1 x.2 ∈ support (observedPositive i t)}
def tupleNegativeSet (i : Bool) (t : Idem S) : Set (ℕ × ℕ) :=
  {x | Nat.pair x.1 x.2 ∈ support (observedNegative i t)}

theorem tuplePositive_mem (i : Bool) (t : Idem S) (x : ℕ × ℕ) :
    x ∈ ClassicalPrograms.J.map (tuplePositive i t).hom x ↔ x ∈ tuplePositiveSet i t :=
  ClassicalPrograms.pair_pull_support _ _ x

theorem tupleNegative_mem (i : Bool) (t : Idem S) (x : ℕ × ℕ) :
    x ∈ ClassicalPrograms.J.map (tupleNegative i t).hom x ↔ x ∈ tupleNegativeSet i t :=
  ClassicalPrograms.pair_pull_support _ _ x

theorem tuple_observed_bounds (i : Bool) (t : Idem S) (ht : categoricalTheory ≤ t) :
    {x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ support EffectiveFork.endpointPair0} ⊆ tuplePositiveSet i t ∧
      {x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ support EffectiveFork.endpointPair1} ⊆ tupleNegativeSet i t :=
  ⟨fun _ hx => (EnumerableCarriers.support_le_iff _ _).mp (observed_bounds i t ht).1 hx,
    fun _ hx => (EnumerableCarriers.support_le_iff _ _).mp (observed_bounds i t ht).2 hx⟩

theorem tuple_observations_enumerable (i : Bool) (t : Idem S) :
    REPred (· ∈ tuplePositiveSet i t) ∧ REPred (· ∈ tupleNegativeSet i t) :=
  ⟨REPred.comp Primrec₂.natPair.to_comp (observed_enumerable i t).1,
    REPred.comp Primrec₂.natPair.to_comp (observed_enumerable i t).2⟩

theorem tuple_observations_inseparable (i : Bool) (t : Theory) :
    Disjoint (tuplePositiveSet i t.val) (tupleNegativeSet i t.val) ∧
      ¬ ∃ D : Set (ℕ × ℕ),ComputablePred (· ∈ D) ∧
        tuplePositiveSet i t.val ⊆ D ∧ Disjoint D (tupleNegativeSet i t.val) := by
  classical
  have h := observed_recursivelyInseparable i t.val t.property.1 t.property.2.1
  constructor
  · exact Set.disjoint_left.mpr (fun _ hp hn => Set.disjoint_left.mp h.1 hp hn)
  · rintro ⟨D,hD,hp,hn⟩
    apply h.2
    refine ⟨{n | Nat.unpair n ∈ D},(hD.decide.comp Computable.unpair).computablePred,?_,?_⟩
    · intro n hn
      apply hp
      change Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 ∈ support (observedPositive i t.val)
      simpa only [Nat.pair_unpair] using hn
    · apply Set.disjoint_left.mpr
      intro n hnD hnN
      apply Set.disjoint_left.mp hn hnD
      change Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 ∈ support (observedNegative i t.val)
      simpa only [Nat.pair_unpair] using hnN

/-- The endpoint observations in ℕ² are inseparable by recursive predicates on ℕ². -/
theorem cosheaf_observation (i : Bool) (t : Theory) :
    Inseparable t.val (Idem.pull nu t.val) ∧
      (REPred (· ∈ tuplePositiveSet i t.val) ∧ REPred (· ∈ tupleNegativeSet i t.val)) ∧
      (Disjoint (tuplePositiveSet i t.val) (tupleNegativeSet i t.val) ∧
        ¬ ∃ D : Set (ℕ × ℕ),ComputablePred (· ∈ D) ∧ tuplePositiveSet i t.val ⊆ D ∧
          Disjoint D (tupleNegativeSet i t.val)) ∧ t.val ⊔ Idem.pull nu t.val≠⊤ :=
  ⟨(coded_observation i t).1,tuple_observations_enumerable i t.val,
    tuple_observations_inseparable i t,(coded_observation i t).2.2⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
