/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCoding
public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# The language of equivalence relations in Foundation

Foundation represents equality and one binary relation by its two binary relation symbols. The translation assigns successive names to the bound variables, and preserves satisfaction in every equality structure.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.NativeInput

open FFL FFL.FirstOrder
open FFL.FirstOrder.Language
open FFL.FirstOrder.Semiterm FFL.FirstOrder.Semiformula

/-- Equality and the single nonlogical binary relation have symbol codes zero and one. -/
instance : Language.Primcodable ℒₛₑₜ where
  func := by
    exact (Primrec₂.const 0).of_eq fun _ _ ↦ rfl
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 < 2 then p.2 + 1 else 0 :=
      Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
        (Primrec.nat_lt.comp Primrec.snd (Primrec.const 2)))
        (Primrec.succ.comp Primrec.snd) (Primrec.const 0)
    refine h.of_eq ?_
    rintro ⟨k,e⟩
    match k,e with
    | 0,_ => simp [Encodable.decode]
    | 1,_ => simp [Encodable.decode]
    | 2,0 => rfl
    | 2,1 => rfl
    | 2,_+2 => simp [Encodable.decode]
    | _+3,_ => simp [Encodable.decode]

/-- Bound-variable indices count outwards from a binder; names count inwards
from the outermost binder. The language has no function symbols. -/
def name {n : ℕ} : Semiterm ℒₛₑₜ Empty n → ℕ
  | bvar j => n-(j.val+1)
  | fvar x => x.elim
  | func f _ => Empty.elim f

def atom {n : ℕ} {a : ℕ} (R : (ℒₛₑₜ).Rel a) (v : Fin a → Semiterm ℒₛₑₜ Empty n) : Janiczak.Formula :=
  match R with
  | Language.Set.Rel.eq => .equal (name (v 0)) (name (v 1))
  | Language.Set.Rel.mem => .related (name (v 0)) (name (v 1))

/-- Translation from every native semisentence to a formula with named variables. -/
def named : {n : ℕ} → Semisentence ℒₛₑₜ n → Janiczak.Formula
  | _, .verum => .top
  | _, .falsum => .neg .top
  | _, .rel R v => atom R v
  | _, .nrel R v => .neg (atom R v)
  | _, .and p q => .conj (named p) (named q)
  | _, .or p q => Janiczak.Formula.disj (named p) (named q)
  | n, .all p => Janiczak.Formula.all n (named p)
  | n, .exs p => .ex n (named p)

variable {X : Type*} [s : Tarski.Structure ℒₛₑₜ X] [Tarski.Structure.Eq ℒₛₑₜ X]

def relation (a b : X) := s.rel Language.Set.Rel.mem ![a,b]

omit [Tarski.Structure.Eq ℒₛₑₜ X] in
private theorem val_name {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) (bv : Fin n → X) (v : ℕ → X)
    (hv : ∀ i : Fin n, v (n-(i.val+1)) = bv i) :
    v (name t) = t.val bv Empty.elim := by
  cases t with
  | bvar i => exact hv i
  | fvar a => exact a.elim
  | func f _ => exact Empty.elim f

private theorem atom_correct {n a : ℕ} (R : (ℒₛₑₜ).Rel a) (ts : Fin a → Semiterm ℒₛₑₜ Empty n)
    (bv : Fin n → X) (v : ℕ → X) (hv : ∀ i : Fin n, v (n-(i.val+1)) = bv i) :
    (atom R ts).Holds relation v ↔ s.rel R (fun i ↦ (ts i).val bv Empty.elim) := by
  cases R with
  | eq =>
    change v (name (ts 0)) = v (name (ts 1)) ↔ _
    rw [val_name _ _ _ hv, val_name _ _ _ hv]
    exact (Tarski.Structure.eq_lang (L := ℒₛₑₜ) (M := X) (v := fun i ↦ (ts i).val bv Empty.elim)).symm
  | mem =>
    change relation _ _ ↔ _
    rw [val_name _ _ _ hv, val_name _ _ _ hv]
    exact Iff.of_eq (congrArg (s.rel Language.Set.Rel.mem) (Matrix.fun_eq_vec_two (fun i ↦ (ts i).val bv Empty.elim)).symm)

omit s [Tarski.Structure.Eq ℒₛₑₜ X] in
private theorem update_env {n : ℕ} (bv : Fin n → X) (v : ℕ → X)
    (hv : ∀ i : Fin n, v (n-(i.val+1)) = bv i) (a : X) :
    ∀ i : Fin (n+1), Function.update v n a ((n+1)-(i.val+1)) = (a :> bv) i := by
  intro i
  refine Fin.cases (by simp) (fun j ↦ ?_) i
  have lt : n-(j.val+1) < n := by have := j.isLt; omega
  have e : n+1-(j.succ.val+1) = n-(j.val+1) := by simp
  rw [e,Function.update_of_ne (Nat.ne_of_lt lt)]
  exact hv j

theorem named_correct {n : ℕ} (p : Semisentence ℒₛₑₜ n) (bv : Fin n → X) (v : ℕ → X)
    (hv : ∀ i : Fin n, v (n-(i.val+1)) = bv i) :
    (named p).Holds relation v ↔ Semiformula.Evalb bv p := by
  induction p generalizing v with
  | verum => rfl
  | falsum => exact ⟨fun h ↦ h trivial, False.elim⟩
  | rel R ts => exact atom_correct R ts bv v hv
  | nrel R ts => exact not_congr (atom_correct R ts bv v hv)
  | and p q ih jh => exact and_congr (ih bv v hv) (jh bv v hv)
  | or p q ih jh => exact (Janiczak.Formula.holds_disj _ _ _ _).trans (or_congr (ih bv v hv) (jh bv v hv))
  | all p ih =>
    rw [named, Janiczak.Formula.holds_all]
    exact forall_congr' (fun a ↦ ih _ _ (update_env bv v hv a))
  | exs p ih =>
    exact exists_congr (fun a ↦ ih _ _ (update_env bv v hv a))

end Janiczak.NativeInput
