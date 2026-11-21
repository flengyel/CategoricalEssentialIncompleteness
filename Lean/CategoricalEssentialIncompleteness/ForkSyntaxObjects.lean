/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkFormulaSubstitution
public import CategoricalEssentialIncompleteness.EffectiveForkFunctions

/-! # The syntax fork and its natural constructors -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (Object V natCarrier)

def natArrow (f : ℕ → ℕ) (hf : Computable f) : natCarrier ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction f hf (fun x _ => Set.mem_univ (f x))

theorem natArrow_total (f : ℕ → ℕ) (hf : Computable f) : isTotal (natArrow f hf) :=
  EnumerableCarriers.totalFromFunction_total f hf (fun x _ => Set.mem_univ (f x))

theorem mem_natArrow (f : ℕ → ℕ) (hf : Computable f) (x y : ℕ) :
    y ∈ EnumerableCarriers.val (natArrow f hf) x ↔ y=f x :=
  (EnumerableCarriers.mem_totalFromFunction f hf (fun x _ => Set.mem_univ (f x)) x y).trans
    (and_iff_right (Set.mem_univ x))

def S : Object where
  center := natCarrier
  left := natCarrier
  right := natCarrier
  leftMap := natArrow (Formula.sigma EffectiveFork.leftCoordinate)
    (Formula.sigma_computable EffectiveFork.leftCoordinate_computable)
  rightMap := natArrow (Formula.sigma EffectiveFork.rightCoordinate)
    (Formula.sigma_computable EffectiveFork.rightCoordinate_computable)
  left_total := natArrow_total _ _
  right_total := natArrow_total _ _

theorem mem_S_left (x y : ℕ) :
    y ∈ EnumerableCarriers.val S.leftMap x ↔ y=Formula.sigma EffectiveFork.leftCoordinate x :=
  mem_natArrow _ (Formula.sigma_computable EffectiveFork.leftCoordinate_computable) x y

theorem mem_S_right (x y : ℕ) :
    y ∈ EnumerableCarriers.val S.rightMap x ↔ y=Formula.sigma EffectiveFork.rightCoordinate x :=
  mem_natArrow _ (Formula.sigma_computable EffectiveFork.rightCoordinate_computable) x y

theorem sigma_encode (f : ℕ → ℕ) (p : Formula) :
    Formula.sigma f (Formula.encode p)=Formula.encode (Formula.mapAtoms f p) := by
  unfold Formula.sigma
  rw [Formula.decode_encode]

theorem sigma_atom (f : ℕ → ℕ) (x : ℕ) : Formula.sigma f (3*x)=3*f x :=
  sigma_encode f (.atom x)

theorem sigma_neg (f : ℕ → ℕ) (x : ℕ) : Formula.sigma f (3*x+1)=3*Formula.sigma f x+1 := by
  change Formula.sigma f (3*x+1)=3*Formula.encode (Formula.mapAtoms f (Formula.decode x))+1
  simpa only [Formula.encode,Formula.encode_decode,Formula.mapAtoms] using
    sigma_encode f (.neg (Formula.decode x))

theorem sigma_imp (f : ℕ → ℕ) (x : ℕ) : Formula.sigma f (3*x+2)=
    3*Nat.pair (Formula.sigma f (Nat.unpair x).1) (Formula.sigma f (Nat.unpair x).2)+2 := by
  change Formula.sigma f (3*x+2)=3*Nat.pair
    (Formula.encode (Formula.mapAtoms f (Formula.decode (Nat.unpair x).1)))
    (Formula.encode (Formula.mapAtoms f (Formula.decode (Nat.unpair x).2)))+2
  simpa only [Formula.encode,Formula.encode_decode,Formula.mapAtoms,Nat.pair_unpair] using
    sigma_encode f (.imp (Formula.decode (Nat.unpair x).1) (Formula.decode (Nat.unpair x).2))

def atomCode (x : ℕ) : ℕ := 3*x
def negCode (x : ℕ) : ℕ := 3*x+1
def impCode (x : ℕ) : ℕ := 3*x+2

theorem atomCode_computable : Computable atomCode :=
  Primrec.nat_mul.to_comp.comp (.const 3) .id
theorem negCode_computable : Computable negCode :=
  Primrec.nat_add.to_comp.comp atomCode_computable (.const 1)
theorem impCode_computable : Computable impCode :=
  Primrec.nat_add.to_comp.comp atomCode_computable (.const 2)

def theta : V ⟶ S := EffectiveFork.computedMap (X := V) (Y := S)
  atomCode atomCode atomCode atomCode_computable atomCode_computable atomCode_computable
  (fun x _ => Set.mem_univ (atomCode x)) (fun x _ => Set.mem_univ (atomCode x))
  (fun x _ => Set.mem_univ (atomCode x))
  (by
    intro x u hu
    apply (mem_S_left _ _).mpr
    rw [(EffectiveFork.mem_V_left x u).mp hu]
    exact (sigma_atom _ x).symm)
  (by
    intro x u hu
    apply (mem_S_right _ _).mpr
    rw [(EffectiveFork.mem_V_right x u).mp hu]
    exact (sigma_atom _ x).symm)

def nu : S ⟶ S := EffectiveFork.computedMap (X := S) (Y := S)
  negCode negCode negCode negCode_computable negCode_computable negCode_computable
  (fun x _ => Set.mem_univ (negCode x)) (fun x _ => Set.mem_univ (negCode x))
  (fun x _ => Set.mem_univ (negCode x))
  (by
    intro x u hu
    apply (mem_S_left _ _).mpr
    rw [(mem_S_left x u).mp hu]
    exact (sigma_neg _ x).symm)
  (by
    intro x u hu
    apply (mem_S_right _ _).mpr
    rw [(mem_S_right x u).mp hu]
    exact (sigma_neg _ x).symm)

def implication : EffectiveFork.product S S ⟶ S :=
  EffectiveFork.computedMap (X := EffectiveFork.product S S) (Y := S)
    impCode impCode impCode impCode_computable impCode_computable impCode_computable
    (fun x _ => Set.mem_univ (impCode x)) (fun x _ => Set.mem_univ (impCode x))
    (fun x _ => Set.mem_univ (impCode x))
    (by
      intro x u hu
      obtain ⟨h0,h1⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ x u).mp hu
      apply (mem_S_left _ _).mpr
      unfold impCode
      rw [sigma_imp,← (mem_S_left _ _).mp h0,← (mem_S_left _ _).mp h1,Nat.pair_unpair]
      )
    (by
      intro x u hu
      obtain ⟨h0,h1⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ x u).mp hu
      apply (mem_S_right _ _).mpr
      unfold impCode
      rw [sigma_imp,← (mem_S_right _ _).mp h0,← (mem_S_right _ _).mp h1,Nat.pair_unpair]
      )

theorem theta_total : isTotal theta := by
  apply (EffectiveFork.total_iff theta).mpr
  exact ⟨EnumerableCarriers.totalFromFunction_total atomCode atomCode_computable
      (fun x _ => Set.mem_univ (atomCode x)),
    EnumerableCarriers.totalFromFunction_total atomCode atomCode_computable
      (fun x _ => Set.mem_univ (atomCode x)),
    EnumerableCarriers.totalFromFunction_total atomCode atomCode_computable
      (fun x _ => Set.mem_univ (atomCode x))⟩

theorem nu_total : isTotal nu := by
  apply (EffectiveFork.total_iff nu).mpr
  exact ⟨EnumerableCarriers.totalFromFunction_total negCode negCode_computable
      (fun x _ => Set.mem_univ (negCode x)),
    EnumerableCarriers.totalFromFunction_total negCode negCode_computable
      (fun x _ => Set.mem_univ (negCode x)),
    EnumerableCarriers.totalFromFunction_total negCode negCode_computable
      (fun x _ => Set.mem_univ (negCode x))⟩

theorem implication_total : isTotal implication := by
  apply (EffectiveFork.total_iff implication).mpr
  exact ⟨EnumerableCarriers.totalFromFunction_total impCode impCode_computable
      (fun x _ => Set.mem_univ (impCode x)),
    EnumerableCarriers.totalFromFunction_total impCode impCode_computable
      (fun x _ => Set.mem_univ (impCode x)),
    EnumerableCarriers.totalFromFunction_total impCode impCode_computable
      (fun x _ => Set.mem_univ (impCode x))⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
