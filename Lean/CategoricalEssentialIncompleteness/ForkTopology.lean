/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Data.Fintype.Powerset
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.DeriveFintype

/-! # The manuscript's actual three-point space and its five opens -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

inductive Point where
  | a | b | c
  deriving DecidableEq, Fintype

instance : TopologicalSpace Point where
  IsOpen s := (Point.a ∈ s → Point.c ∈ s) ∧ (Point.b ∈ s → Point.c ∈ s)
  isOpen_univ := ⟨fun _ => Set.mem_univ _,fun _ => Set.mem_univ _⟩
  isOpen_inter s t hs ht := ⟨fun hx => ⟨hs.1 hx.1,ht.1 hx.2⟩,
    fun hx => ⟨hs.2 hx.1,ht.2 hx.2⟩⟩
  isOpen_sUnion S hS := by
    constructor
    · rintro ⟨s,hs,ha⟩
      exact ⟨s,hs,(hS s hs).1 ha⟩
    · rintro ⟨s,hs,hb⟩
      exact ⟨s,hs,(hS s hs).2 hb⟩

inductive Open where
  | empty | D | L | R | whole
  deriving DecidableEq, Fintype

namespace Open

def members : Open → Finset Point
  | empty => ∅
  | D => {.c}
  | L => {.a,.c}
  | R => {.b,.c}
  | whole => Finset.univ

instance : Membership Point Open := ⟨fun U p => p ∈ members U⟩

@[simp] theorem mem_def (p : Point) (U : Open) : p ∈ U ↔ p ∈ members U := Iff.rfl

instance (p : Point) (U : Open) : Decidable (p ∈ U) :=
  inferInstanceAs (Decidable (p ∈ members U))

instance : LE Open := ⟨fun U V => members U ⊆ members V⟩
instance : DecidableLE Open := inferInstanceAs (DecidableRel (fun U V => members U ⊆ members V))

theorem members_injective : Function.Injective members := by decide

instance : PartialOrder Open where
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm _ _ h k := members_injective (Finset.Subset.antisymm h k)

def meet : Open → Open → Open
  | empty,_ | _,empty => empty
  | whole,U | U,whole => U
  | D,_ | _,D => D
  | L,L => L
  | R,R => R
  | _,_ => D

def join : Open → Open → Open
  | whole,_ | _,whole => whole
  | empty,U | U,empty => U
  | D,U | U,D => U
  | L,L => L
  | R,R => R
  | _,_ => whole

instance : Lattice Open where
  inf := meet
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  sup := join
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : BoundedOrder Open where
  top := whole
  le_top := by decide
  bot := empty
  bot_le := by decide

theorem le_cases : ∀ U V : Open,U ≤ V ↔ U=empty ∨ V=whole ∨ U=V ∨
    (U=D ∧ (V=L ∨ V=R)) := by decide

@[simp] theorem mem_meet (p : Point) (U V : Open) : p ∈ U ⊓ V ↔ p ∈ U ∧ p ∈ V := by
  revert p U V
  decide

def toActual (U : Open) : TopologicalSpace.Opens Point :=
  ⟨{p | p ∈ U},by
    change (Point.a ∈ U → Point.c ∈ U) ∧ (Point.b ∈ U → Point.c ∈ U)
    cases U <;> simp [members]⟩

theorem toActual_injective : Function.Injective toActual := by
  intro U V h
  apply members_injective
  ext p
  exact Set.ext_iff.mp (congrArg (fun O : TopologicalSpace.Opens Point => (O : Set Point)) h) p

theorem toActual_surjective : Function.Surjective toActual := by
  intro s
  have hs : (Point.a ∈ s → Point.c ∈ s) ∧ (Point.b ∈ s → Point.c ∈ s) := s.isOpen
  by_cases hc : Point.c ∈ s
  · by_cases ha : Point.a ∈ s
    · by_cases hb : Point.b ∈ s
      · refine ⟨whole,?_⟩
        ext p
        change (p ∈ whole) ↔ p ∈ s
        cases p <;> simp [members,ha,hb,hc]
      · refine ⟨L,?_⟩
        ext p
        change (p ∈ L) ↔ p ∈ s
        cases p <;> simp [members,ha,hb,hc]
    · by_cases hb : Point.b ∈ s
      · refine ⟨R,?_⟩
        ext p
        change (p ∈ R) ↔ p ∈ s
        cases p <;> simp [members,ha,hb,hc]
      · refine ⟨D,?_⟩
        ext p
        change (p ∈ D) ↔ p ∈ s
        cases p <;> simp [members,ha,hb,hc]
  · have ha : Point.a ∉ s := fun h => hc (hs.1 h)
    have hb : Point.b ∉ s := fun h => hc (hs.2 h)
    refine ⟨empty,?_⟩
    ext p
    change (p ∈ empty) ↔ p ∈ s
    cases p <;> simp [members,ha,hb,hc]

def actualOrderIso : Open ≃o TopologicalSpace.Opens Point where
  toEquiv := Equiv.ofBijective toActual ⟨toActual_injective,toActual_surjective⟩
  map_rel_iff' := Iff.rfl

end Open
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
