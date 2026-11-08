/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxState

/-! # Canonical finite lists over arbitrary uniform carriers

Membership witnesses are existential data of the positive finite guard.
The numerical list itself has the existing zero/one-plus-pair code.
-/
noncomputable section
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def carrier (V : Total.Carrier P) : Total.Carrier P where
  support := {n | ∀ v ∈ Nat.natToList n,v ∈ V.support}
  enumerable := Uniform.Enumerable.comp (f := Nat.natToList) Primrec.nat_natToList.to_comp V.enumerable.listAll

@[simp] theorem nil_mem (V : Total.Carrier P) : 0 ∈ (carrier V).support := by
  simp [carrier,Nat.natToList]

@[simp] theorem adjoin_mem (V : Total.Carrier P) (v rest : ℕ) :
    adjoin v rest ∈ (carrier V).support ↔ v ∈ V.support ∧ rest ∈ (carrier V).support := by
  change (∀ a ∈ Nat.natToList (adjoin v rest),a ∈ V.support) ↔ _
  rw [natToList_adjoin]
  exact List.forall_mem_cons

@[simp] theorem pack_mem (V : Total.Carrier P) (L : List ℕ) :
    pack L ∈ (carrier V).support ↔ ∀ v ∈ L,v ∈ V.support := by
  change (∀ a ∈ Nat.natToList (pack L),a ∈ V.support) ↔ _
  rw [natToList_pack]

def object (V : Total.Carrier P) : Total.TotalCategory P := ⟨carrier V⟩

def family (R : Total.TotalCategory P) (V : Total.Carrier P) : Over R :=
  Over.mk (Total.totalFst R (object V))

def polynomial (V : Total.TotalCategory P) : SyntaxPolynomial (Total.TotalCategory P) :=
  .sum .unit (.product (.coefficient V) .term)

def nil (V : Total.Carrier P) : (⟨Total.terminalCarrier (P := P)⟩ : Total.TotalCategory P) ⟶ object V :=
  ⟨Total.totalFromFunction (fun _ => 0) (Computable.const 0) (fun _ _ => nil_mem V),
    Total.totalFromFunction_total _ _ _⟩

def adjoinMap (V : Total.Carrier P) :
    (⟨Total.product V (carrier V)⟩ : Total.TotalCategory P) ⟶ object V :=
  ⟨Total.totalFromFunction (fun n => adjoin (Nat.unpair n).1 (Nat.unpair n).2)
    (adjoin_primrec.to_comp.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair))
    (fun _ hn => (adjoin_mem V _ _).mpr hn),Total.totalFromFunction_total _ _ _⟩

theorem nil_graph (V : Total.Carrier P) (x y : ℕ) :
    y ∈ Total.val (nil V).hom x ↔ x=0 ∧ y=0 := by
  change y ∈ Total.val (Total.totalFromFunction (fun _ => 0) (Computable.const 0)
    (fun _ _ => nil_mem V)) x ↔ x=0 ∧ y=0
  exact Total.mem_totalFromFunction (X := Total.terminalCarrier) (Y := carrier V)
    (fun _ => 0) (Computable.const 0) (fun _ _ => nil_mem V) x y

theorem adjoin_graph (V : Total.Carrier P) (v rest y : ℕ) :
    y ∈ Total.val (adjoinMap V).hom (Nat.pair v rest) ↔
      v ∈ V.support ∧ rest ∈ (carrier V).support ∧ y=adjoin v rest := by
  change y ∈ Total.val (Total.totalFromFunction (X := Total.product V (carrier V)) (Y := carrier V)
    (fun n => adjoin (Nat.unpair n).1 (Nat.unpair n).2)
    (adjoin_primrec.to_comp.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair))
    (fun _ hn => (adjoin_mem V _ _).mpr hn)) (Nat.pair v rest) ↔ _
  rw [Total.mem_totalFromFunction]
  change (((Nat.unpair (Nat.pair v rest)).1 ∈ V.support ∧
    (Nat.unpair (Nat.pair v rest)).2 ∈ (carrier V).support) ∧ _) ↔ _
  simp only [Nat.unpair_pair,and_assoc]

end CategoricalEssentialIncompleteness.V46.Miller.Lists
