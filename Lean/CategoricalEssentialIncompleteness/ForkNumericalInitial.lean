/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkNumericalAlgebras

/-! # The recursive formula fold satisfies the constructor equations uniquely -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EnumerableCarriers (Carrier val)
open EffectiveFork (natCarrier)

theorem arrow_eq_of_shared {X Y : Carrier} {f g : X ⟶ Y}
    (h : ∀ x ∈ X.support,∃ y,y ∈ val f x ∧ y ∈ val g x) : f=g := by
  apply EnumerableCarriers.val_injective
  apply PFun.ext
  intro x y
  constructor
  · intro hy
    obtain ⟨z,hz,hzg⟩ := h x (EnumerableCarriers.val_source f x y hy)
    exact Part.mem_unique hz hy ▸ hzg
  · intro hy
    obtain ⟨z,hzf,hz⟩ := h x (EnumerableCarriers.val_source g x y hy)
    exact Part.mem_unique hz hy ▸ hzf

def binaryConstructor : EnumerableCarriers.product natCarrier natCarrier ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction impCode impCode_computable
    (fun x _ => Set.mem_univ (impCode x))

theorem mem_binaryConstructor (x y : ℕ) :
    y ∈ val binaryConstructor x ↔ y=impCode x :=
  (EnumerableCarriers.mem_totalFromFunction _ _ _ x y).trans
    (and_iff_right ⟨Set.mem_univ _,Set.mem_univ _⟩)

theorem decode_binary (x : ℕ) : Formula.decode (impCode x)=
    .imp (Formula.decode (Nat.unpair x).1) (Formula.decode (Nat.unpair x).2) := by
  have h := Formula.decode_encode (.imp (Formula.decode (Nat.unpair x).1)
    (Formula.decode (Nat.unpair x).2))
  simpa only [impCode,Formula.encode,Formula.encode_decode,Nat.pair_unpair] using h

namespace NumericalAlgebra

variable {Z : Carrier}

theorem atom_fold (A : NumericalAlgebra Z) :
    natArrow atomCode atomCode_computable ≫ A.foldArrow=A.atom := by
  apply arrow_eq_of_shared
  intro x _
  refine ⟨(A.eval (.atom x)).val,?_,A.eval_atom x⟩
  apply (EnumerableCarriers.mem_val_comp _ _ _ _).mpr
  refine ⟨atomCode x,(mem_natArrow _ _ _ _).mpr rfl,?_⟩
  exact (A.mem_foldArrow _ _).mpr (A.foldCode_encode (.atom x)).symm

theorem neg_fold (A : NumericalAlgebra Z) :
    natArrow negCode negCode_computable ≫ A.foldArrow=A.foldArrow ≫ A.neg := by
  apply arrow_eq_of_shared
  intro x _
  let p := Formula.decode x
  refine ⟨(A.eval (.neg p)).val,?_,?_⟩
  · apply (EnumerableCarriers.mem_val_comp _ _ _ _).mpr
    refine ⟨negCode x,(mem_natArrow _ _ _ _).mpr rfl,(A.mem_foldArrow _ _).mpr ?_⟩
    have h : negCode x=Formula.encode (.neg p) := by
      change 3*x+1=3*(Formula.decode x).encode+1
      rw [Formula.encode_decode]
    rw [h,A.foldCode_encode]
  · exact (EnumerableCarriers.mem_val_comp _ _ _ _).mpr
      ⟨(A.eval p).val,(A.mem_foldArrow _ _).mpr rfl,A.eval_neg p⟩

theorem imp_fold (A : NumericalAlgebra Z) :
    binaryConstructor ≫ A.foldArrow=
      EnumerableCarriers.partialProdMap A.foldArrow A.foldArrow ≫ A.imp := by
  apply arrow_eq_of_shared
  intro x _
  let p := Formula.decode (Nat.unpair x).1
  let q := Formula.decode (Nat.unpair x).2
  refine ⟨(A.eval (.imp p q)).val,?_,?_⟩
  · apply (EnumerableCarriers.mem_val_comp _ _ _ _).mpr
    refine ⟨impCode x,(mem_binaryConstructor _ _).mpr rfl,(A.mem_foldArrow _ _).mpr ?_⟩
    change (A.eval (.imp p q)).val=(A.eval (Formula.decode (impCode x))).val
    rw [decode_binary]
  · apply (EnumerableCarriers.mem_val_comp _ _ _ _).mpr
    refine ⟨Nat.pair (A.eval p).val (A.eval q).val,?_,A.eval_imp p q⟩
    apply (EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mpr
    simp only [Nat.unpair_pair]
    exact ⟨(A.mem_foldArrow _ _).mpr rfl,(A.mem_foldArrow _ _).mpr rfl⟩

theorem fold_unique (A : NumericalAlgebra Z) (h : natCarrier ⟶ Z)
    (ha : natArrow atomCode atomCode_computable ≫ h=A.atom)
    (hn : natArrow negCode negCode_computable ≫ h=h ≫ A.neg)
    (hi : binaryConstructor ≫ h=EnumerableCarriers.partialProdMap h h ≫ A.imp) :
    h=A.foldArrow := by
  have mem (p : Formula) : (A.eval p).val ∈ val h p.encode := by
    induction p with
    | atom x =>
      have hh := A.eval_atom x
      rw [← ha] at hh
      obtain ⟨z,hz,hh⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hh
      rw [(mem_natArrow _ _ _ _).mp hz] at hh
      exact hh
    | neg p ih =>
      have hh := (EnumerableCarriers.mem_val_comp h A.neg p.encode _).mpr
        ⟨(A.eval p).val,ih,A.eval_neg p⟩
      rw [← hn] at hh
      obtain ⟨z,hz,hh⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hh
      rw [(mem_natArrow _ _ _ _).mp hz] at hh
      exact hh
    | imp p q ihp ihq =>
      have hp : Nat.pair (A.eval p).val (A.eval q).val ∈
          val (EnumerableCarriers.partialProdMap h h) (Nat.pair p.encode q.encode) := by
        apply (EnumerableCarriers.mem_partialProdMap_iff h h _ _).mpr
        simpa only [Nat.unpair_pair] using And.intro ihp ihq
      have hh := (EnumerableCarriers.mem_val_comp _ A.imp _ _).mpr
        ⟨_,hp,A.eval_imp p q⟩
      rw [← hi] at hh
      obtain ⟨z,hz,hh⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hh
      rw [(mem_binaryConstructor _ _).mp hz] at hh
      exact hh
  apply arrow_eq_of_shared
  intro x _
  refine ⟨(A.eval (Formula.decode x)).val,?_,(A.mem_foldArrow _ _).mpr rfl⟩
  simpa only [Formula.encode_decode] using mem (Formula.decode x)

end NumericalAlgebra
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
