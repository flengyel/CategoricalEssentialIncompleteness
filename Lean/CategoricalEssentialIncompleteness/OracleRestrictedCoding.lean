/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedTotal

/-! # Recursive coding isomorphisms of all formal numerical types -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

def Ty.toNat : (X : Ty) → X.carrier → ℕ
  | .nat,x => x
  | .product X Y,p => Nat.pair (X.toNat p.1) (Y.toNat p.2)
  | .coproduct X Y,.inl x => 2*X.toNat x
  | .coproduct X Y,.inr y => 2*Y.toNat y+1

def Ty.fromNat : (X : Ty) → ℕ → X.carrier
  | .nat,n => n
  | .product X Y,n => (X.fromNat (Nat.unpair n).1,Y.fromNat (Nat.unpair n).2)
  | .coproduct X Y,n => if n%2=0 then .inl (X.fromNat (n/2)) else .inr (Y.fromNat (n/2))

theorem Ty.from_toNat (X : Ty) (x : X.carrier) : X.fromNat (X.toNat x)=x := by
  induction X with
  | nat => rfl
  | product X Y ihX ihY =>
    rcases x with ⟨x,y⟩
    simp only [Ty.toNat,Ty.fromNat,Nat.unpair_pair,ihX,ihY]
  | coproduct X Y ihX ihY =>
    cases x with
    | inl x => simp [Ty.toNat,Ty.fromNat,ihX]
    | inr y => simp [Ty.toNat,Ty.fromNat,Nat.add_mod,Nat.add_div,ihY]

theorem Ty.to_fromNat (X : Ty) (n : ℕ) : X.toNat (X.fromNat n)=n := by
  induction X generalizing n with
  | nat => rfl
  | product X Y ihX ihY => simp only [Ty.toNat,Ty.fromNat,ihX,ihY,Nat.pair_unpair]
  | coproduct X Y ihX ihY =>
    simp only [Ty.fromNat]
    split_ifs with h
    · simp only [Ty.toNat,ihX]
      omega
    · simp only [Ty.toNat,ihY]
      omega

theorem Ty.toNat_computable (X : Ty) : Computable X.toNat := by
  induction X with
  | nat => exact Computable.id
  | product X Y ihX ihY =>
    change Computable (fun p : X.carrier × Y.carrier => Nat.pair (X.toNat p.1) (Y.toNat p.2))
    exact Primrec₂.natPair.to_comp.comp
      (ihX.comp Computable.fst) (ihY.comp Computable.snd)
  | coproduct X Y ihX ihY =>
    have hl : Computable (fun x : X.carrier => 2*X.toNat x) :=
      Primrec.nat_mul.to_comp.comp (Computable.const 2) ihX
    have hr : Computable (fun y : Y.carrier => 2*Y.toNat y+1) :=
      Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) ihY)
        (Computable.const 1)
    apply (Computable.sumCasesOn Computable.id
      (hl.comp Computable.snd).to₂ (hr.comp Computable.snd).to₂).of_eq
    intro t
    cases t <;> rfl

theorem Ty.fromNat_computable (X : Ty) : Computable X.fromNat := by
  induction X with
  | nat => exact Computable.id
  | product X Y ihX ihY =>
    change Computable (fun n : ℕ => (X.fromNat (Nat.unpair n).1,Y.fromNat (Nat.unpair n).2))
    exact Computable.pair
      (ihX.comp (Computable.fst.comp Computable.unpair))
      (ihY.comp (Computable.snd.comp Computable.unpair))
  | coproduct X Y ihX ihY =>
    change Computable (fun n : ℕ =>
      if n%2=0 then Sum.inl (X.fromNat (n/2)) else Sum.inr (Y.fromNat (n/2)))
    have hd : Computable (fun n : ℕ => n/2) := Primrec.nat_div.to_comp.comp .id (.const 2)
    have hb : ComputablePred (fun n : ℕ => n%2=0) :=
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (.const 2)) (.const 0)).computablePred
    simpa only [Bool.cond_decide] using hb.decide.cond
      (Computable.sumInl.comp (ihX.comp hd)) (Computable.sumInr.comp (ihY.comp hd))

namespace Restricted

variable {S : Set ℕ}
attribute [instance 2000] nativeRestriction

def N (S : Set ℕ) : Restricted S := ⟨.nat⟩

def codeIso (X : Restricted S) : X ≅ N S where
  hom := totalFromFunction X.type.toNat X.type.toNat_computable
  inv := totalFromFunction X.type.fromNat X.type.fromNat_computable
  hom_inv_id := by
    apply Arrow.ext
    funext x
    change (Part.some (X.type.toNat x)).bind
      (fun n => Part.some (X.type.fromNat n))=Part.some x
    simp only [Part.bind_some,X.type.from_toNat]
  inv_hom_id := by
    apply Arrow.ext
    funext n
    change (Part.some (X.type.fromNat n)).bind
      (fun x => Part.some (X.type.toNat x))=Part.some n
    simp only [Part.bind_some,X.type.to_fromNat]

instance isotype : RecursionCategory.Isotype (Restricted S) where
  iso X Y := ⟨codeIso X ≪≫ (codeIso Y).symm⟩

end Restricted
end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
