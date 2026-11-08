/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw

/-! # Explicit recursive constant-family polynomial codes

The external parameter is inserted at term and formula leaves. Coefficient
and unit payloads retain their literal codes, products retain ordered
children, and sums retain their original inner tags. These are ordinary
primitive-recursive maps for each fixed polynomial expression.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family}

def constantObject (R A : Total.TotalCategory P) : Over R := Over.mk (Total.totalFst R A)

def constantLift : SyntaxPolynomial (Total.TotalCategory P) → ℕ → ℕ → ℕ
  | .term,r,u => Nat.pair r u
  | .formula,r,u => Nat.pair r u
  | .coefficient _,_,u => u
  | .unit,_,u => u
  | .product a b,r,u => Nat.pair (constantLift a r (Nat.unpair u).1)
      (constantLift b r (Nat.unpair u).2)
  | .sum a b,r,u => Nat.pair
      (if (Nat.unpair u).2=0 then constantLift a r (Nat.unpair u).1
       else constantLift b r (Nat.unpair u).1) (Nat.unpair u).2

def constantUnlift : SyntaxPolynomial (Total.TotalCategory P) → ℕ → ℕ
  | .term,u => (Nat.unpair u).2
  | .formula,u => (Nat.unpair u).2
  | .coefficient _,u => u
  | .unit,u => u
  | .product a b,u => Nat.pair (constantUnlift a (Nat.unpair u).1)
      (constantUnlift b (Nat.unpair u).2)
  | .sum a b,u => Nat.pair
      (if (Nat.unpair u).2=0 then constantUnlift a (Nat.unpair u).1
       else constantUnlift b (Nat.unpair u).1) (Nat.unpair u).2

theorem constantLift_product (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v : ℕ) :
    constantLift (.product a b) r (Nat.pair u v)=Nat.pair (constantLift a r u) (constantLift b r v) := by
  simp only [constantLift,Nat.unpair_pair]

theorem constantLift_inl (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    constantLift (.sum a b) r (Nat.pair u 0)=Nat.pair (constantLift a r u) 0 := by
  simp [constantLift,Nat.unpair_pair]

theorem constantLift_inr (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    constantLift (.sum a b) r (Nat.pair u 1)=Nat.pair (constantLift b r u) 1 := by
  simp only [constantLift,Nat.unpair_pair,ite_eq_right (by decide : (1:ℕ)≠0)]

theorem constantUnlift_product (a b : SyntaxPolynomial (Total.TotalCategory P)) (u v : ℕ) :
    constantUnlift (.product a b) (Nat.pair u v)=Nat.pair (constantUnlift a u) (constantUnlift b v) := by
  simp only [constantUnlift,Nat.unpair_pair]

theorem constantUnlift_inl (a b : SyntaxPolynomial (Total.TotalCategory P)) (u : ℕ) :
    constantUnlift (.sum a b) (Nat.pair u 0)=Nat.pair (constantUnlift a u) 0 := by
  simp [constantUnlift,Nat.unpair_pair]

theorem constantUnlift_inr (a b : SyntaxPolynomial (Total.TotalCategory P)) (u : ℕ) :
    constantUnlift (.sum a b) (Nat.pair u 1)=Nat.pair (constantUnlift b u) 1 := by
  simp only [constantUnlift,Nat.unpair_pair,ite_eq_right (by decide : (1:ℕ)≠0)]

theorem constantLift_primrec (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec₂ (constantLift p) := by
  induction p with
  | term => exact Primrec₂.natPair
  | formula => exact Primrec₂.natPair
  | coefficient C => exact Primrec.snd
  | unit => exact Primrec.snd
  | product a b ia ib =>
    exact Primrec₂.natPair.comp
      (ia.comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
      (ib.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  | sum a b ia ib =>
    have ht : Primrec (fun z:ℕ×ℕ => (Nat.unpair z.2).2) :=
      Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
    have hv : Primrec (fun z:ℕ×ℕ => (Nat.unpair z.2).1) :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    exact Primrec₂.natPair.comp
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
        (ia.comp Primrec.fst hv) (ib.comp Primrec.fst hv)) ht

theorem constantUnlift_primrec (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec (constantUnlift p) := by
  induction p with
  | term => exact Primrec.snd.comp Primrec.unpair
  | formula => exact Primrec.snd.comp Primrec.unpair
  | coefficient C => exact Primrec.id
  | unit => exact Primrec.id
  | product a b ia ib =>
    exact Primrec₂.natPair.comp (ia.comp (Primrec.fst.comp Primrec.unpair))
      (ib.comp (Primrec.snd.comp Primrec.unpair))
  | sum a b ia ib =>
    have ht : Primrec (fun u:ℕ => (Nat.unpair u).2) := Primrec.snd.comp Primrec.unpair
    have hv : Primrec (fun u:ℕ => (Nat.unpair u).1) := Primrec.fst.comp Primrec.unpair
    exact Primrec₂.natPair.comp
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (ia.comp hv) (ib.comp hv)) ht

theorem constantUnlift_lift (p : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    constantUnlift p (constantLift p r u)=u := by
  induction p generalizing u with
  | term => simp only [constantLift,constantUnlift,Nat.unpair_pair]
  | formula => simp only [constantLift,constantUnlift,Nat.unpair_pair]
  | coefficient C => rfl
  | unit => rfl
  | product a b ia ib =>
    simp only [constantLift,constantUnlift,Nat.unpair_pair,ia,ib,Nat.pair_unpair]
  | sum a b ia ib =>
    by_cases h:(Nat.unpair u).2=0
    · simp only [constantLift,constantUnlift,Nat.unpair_pair,ite_eq_left h,ia,Nat.pair_unpair]
    · simp only [constantLift,constantUnlift,Nat.unpair_pair,ite_eq_right h,ib,Nat.pair_unpair]

variable (R A B : Total.TotalCategory P)

theorem constantLift_supported (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (hr:r∈R.obj.support) (hu:u∈(carrier A.obj B.obj p).support) :
    fiber R (constantObject R A) (constantObject R B) p (r,constantLift p r u) := by
  induction p generalizing u with
  | term =>
    change u∈A.obj.support at hu
    exact (Total.mem_partialFst R.obj A.obj (Nat.pair r u) r).mpr
      ⟨by
        change (Nat.unpair (Nat.pair r u)).1∈R.obj.support ∧
          (Nat.unpair (Nat.pair r u)).2∈A.obj.support
        simpa only [Nat.unpair_pair] using And.intro hr hu,by simp⟩
  | formula =>
    change u∈B.obj.support at hu
    exact (Total.mem_partialFst R.obj B.obj (Nat.pair r u) r).mpr
      ⟨by
        change (Nat.unpair (Nat.pair r u)).1∈R.obj.support ∧
          (Nat.unpair (Nat.pair r u)).2∈B.obj.support
        simpa only [Nat.unpair_pair] using And.intro hr hu,by simp⟩
  | coefficient C => exact ⟨hr,hu⟩
  | unit => exact ⟨hr,hu⟩
  | product a b ia ib =>
    change fiber R (constantObject R A) (constantObject R B) a
      (r,(Nat.unpair (constantLift (.product a b) r u)).1) ∧
      fiber R (constantObject R A) (constantObject R B) b
      (r,(Nat.unpair (constantLift (.product a b) r u)).2)
    simp only [constantLift,Nat.unpair_pair]
    exact ⟨ia hu.1,ib hu.2⟩
  | sum a b ia ib =>
    rcases hu with ⟨ht,ha⟩ | ⟨ht,hb⟩
    · simp only [constantLift,ite_eq_left ht,fiber,Nat.unpair_pair]
      exact Or.inl ⟨ht,ia ha⟩
    · have ht0 : (Nat.unpair u).2≠0 := by
        have ht1 : (Nat.unpair u).2=1 := ht
        omega
      simp only [constantLift,ite_eq_right ht0,fiber,Nat.unpair_pair]
      exact Or.inr ⟨ht,ib hb⟩

theorem constantUnlift_supported (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h:fiber R (constantObject R A) (constantObject R B) p (r,u)) :
    r∈R.obj.support ∧ constantUnlift p u∈(carrier A.obj B.obj p).support := by
  induction p generalizing u with
  | term =>
    have hs := (Total.mem_partialFst R.obj A.obj u r).mp h
    exact ⟨hs.2 ▸ hs.1.1,hs.1.2⟩
  | formula =>
    have hs := (Total.mem_partialFst R.obj B.obj u r).mp h
    exact ⟨hs.2 ▸ hs.1.1,hs.1.2⟩
  | coefficient C => exact h
  | unit => exact h
  | product a b ia ib =>
    have ha := ia h.1
    have hb := ib h.2
    refine ⟨ha.1,?_⟩
    change (Nat.unpair (constantUnlift (.product a b) u)).1∈(carrier A.obj B.obj a).support ∧
      (Nat.unpair (constantUnlift (.product a b) u)).2∈(carrier A.obj B.obj b).support
    simpa only [constantUnlift,Nat.unpair_pair] using And.intro ha.2 hb.2
  | sum a b ia ib =>
    rcases h with ⟨ht,ha⟩ | ⟨ht,hb⟩
    · have hs := ia ha
      refine ⟨hs.1,?_⟩
      change ((Nat.unpair (constantUnlift (.sum a b) u)).2=0 ∧
        (Nat.unpair (constantUnlift (.sum a b) u)).1∈(carrier A.obj B.obj a).support) ∨ _
      simpa only [constantUnlift,Nat.unpair_pair,ite_eq_left ht] using Or.inl ⟨ht,hs.2⟩
    · have hs := ib hb
      have ht0 : (Nat.unpair u).2≠0 := by
        have ht1 : (Nat.unpair u).2=1 := ht
        omega
      refine ⟨hs.1,?_⟩
      change _ ∨ ((Nat.unpair (constantUnlift (.sum a b) u)).2=1 ∧
        (Nat.unpair (constantUnlift (.sum a b) u)).1∈(carrier A.obj B.obj b).support)
      simpa only [constantUnlift,Nat.unpair_pair,ite_eq_right ht0] using Or.inr ⟨ht,hs.2⟩

/-- The reverse equation uses the actual fiber condition: every recursive
leaf's stored parameter is forced to equal the external r. -/
theorem constantLift_unlift (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h:fiber R (constantObject R A) (constantObject R B) p (r,u)) :
    constantLift p r (constantUnlift p u)=u := by
  induction p generalizing u with
  | term =>
    have he := ((Total.mem_partialFst R.obj A.obj u r).mp h).2
    change Nat.pair r (Nat.unpair u).2=u
    rw [← he,Nat.pair_unpair]
  | formula =>
    have he := ((Total.mem_partialFst R.obj B.obj u r).mp h).2
    change Nat.pair r (Nat.unpair u).2=u
    rw [← he,Nat.pair_unpair]
  | coefficient C => rfl
  | unit => rfl
  | product a b ia ib =>
    simp only [constantLift,constantUnlift,Nat.unpair_pair,ia h.1,ib h.2,Nat.pair_unpair]
  | sum a b ia ib =>
    rcases h with ⟨ht,ha⟩ | ⟨ht,hb⟩
    · simp only [constantLift,constantUnlift,Nat.unpair_pair,ite_eq_left ht,ia ha,Nat.pair_unpair]
    · have ht0 : (Nat.unpair u).2≠0 := by
        have ht1 : (Nat.unpair u).2=1 := ht
        omega
      simp only [constantLift,constantUnlift,Nat.unpair_pair,ite_eq_right ht0,ib hb,Nat.pair_unpair]

theorem constant_fiber_iff (p : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    fiber R (constantObject R A) (constantObject R B) p (r,constantLift p r u) ↔
      r∈R.obj.support ∧ u∈(carrier A.obj B.obj p).support := by
  constructor
  · intro h
    have hs := constantUnlift_supported R A B p h
    simpa only [constantUnlift_lift] using hs
  · exact fun h => constantLift_supported R A B p h.1 h.2

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
