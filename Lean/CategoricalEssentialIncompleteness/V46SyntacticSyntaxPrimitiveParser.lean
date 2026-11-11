/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveVectors
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser

/-! # Actual standard primitive-recursion certificates for the postfix parser -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors
open Coding Postfix
local instance primitiveParserDecidableEq : DecidableEq ℕ := Classical.decEq ℕ

theorem pi1_primrec : Primrec (pi₁ : ℕ → ℕ) := by
  exact Primrec.of_eq (Primrec.fst.comp Primrec.unpair)
    (fun n => (FiniteSigmaOne.nat_pi₁_eq n).symm)

theorem nat_pi₂_eq (r : ℕ) : π₂ r = r.unpair.2 := by
  have hp : Nat.pair (π₁ r) (π₂ r) = r := by
    simpa only [nat_pair_eq] using pair_unpair r
  have hu : (π₁ r, π₂ r) = r.unpair := by
    simpa only [Nat.unpair_pair] using congrArg Nat.unpair hp
  exact congrArg Prod.snd hu

theorem pi2_primrec : Primrec (pi₂ : ℕ → ℕ) := by
  exact Primrec.of_eq (Primrec.snd.comp Primrec.unpair) (fun n => (nat_pi₂_eq n).symm)

theorem pair_primrec : Primrec₂ (fun x y : ℕ => ⟪x, y⟫) := by
  simpa only [nat_pair_eq] using Primrec₂.natPair

theorem arithmetic_sub_eq (a b : ℕ) : Arithmetic.sub a b = Nat.sub a b := by
  symm
  apply Arithmetic.sub_eq_iff.mpr
  constructor
  · intro h
    have hn : Nat.le b a := by
      rcases Arithmetic.le_def.mp h with he | hlt
      · exact Nat.le_of_eq he
      · exact Nat.le_of_lt hlt
    exact (Nat.add_sub_of_le hn).symm
  · intro h
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

theorem arithmetic_sub_primrec : Primrec₂ (Arithmetic.sub : ℕ → ℕ → ℕ) := by
  exact Primrec₂.of_eq Primrec.nat_sub fun a b => (arithmetic_sub_eq a b).symm

theorem fstIdx_primrec : Primrec (fstIdx : ℕ → ℕ) := by
  exact Primrec.of_eq (pi1_primrec.comp
    (arithmetic_sub_primrec.comp Primrec.id (Primrec.const 1))) (fun _ => rfl)

theorem sndIdx_primrec : Primrec (sndIdx : ℕ → ℕ) := by
  exact Primrec.of_eq (pi2_primrec.comp
    (arithmetic_sub_primrec.comp Primrec.id (Primrec.const 1))) (fun _ => rfl)

theorem shape_primrec (q : RawPolynomial) : Primrec (shape q : ℕ → ℕ) := by
  induction q with
  | term => exact Primrec.const 0
  | formula => exact Primrec.const 0
  | coefficient C => exact Primrec.id
  | unit => exact Primrec.const 0
  | product a b ia ib =>
      exact pair_primrec.comp (ia.comp pi1_primrec) (ib.comp pi2_primrec)
  | sum a b ia ib =>
      exact pair_primrec.comp
        (Primrec.ite (Primrec.eq.comp pi2_primrec (Primrec.const 0))
          (ia.comp pi1_primrec) (ib.comp pi1_primrec)) pi2_primrec

theorem childrenWord_primrec (q : RawPolynomial) : Primrec (childrenWord q : ℕ → ℕ) := by
  induction q with
  | term => exact Primrec.id
  | formula => exact Primrec.id
  | coefficient C => exact Primrec.const 0
  | unit => exact Primrec.const 0
  | product a b ia ib =>
      exact append_primrec.comp (ia.comp pi1_primrec) (ib.comp pi2_primrec)
  | sum a b ia ib =>
      exact Primrec.ite (Primrec.eq.comp pi2_primrec (Primrec.const 0))
        (ia.comp pi1_primrec) (ib.comp pi1_primrec)

theorem refillLeaf_primrec (formula : Bool) : Primrec₂ (refillLeaf formula : ℕ → ℕ → ℕ) := by
  have hc : PrimrecPred (fun p : ℕ × ℕ =>
      p.1 = 0 ∧ p.2 ≠ 0 ∧ π₂ (fstIdx p.2) = (if formula then 1 else 0)) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).and <|
      (Primrec.eq.comp Primrec.snd (Primrec.const 0)).not.and <|
        Primrec.eq.comp (pi2_primrec.comp (fstIdx_primrec.comp Primrec.snd))
          (Primrec.const (if formula then 1 else 0))
  exact Primrec.ite hc
    (adjoin_primrec.comp (pi1_primrec.comp (fstIdx_primrec.comp Primrec.snd))
      (sndIdx_primrec.comp Primrec.snd)) (Primrec.const 0)

theorem refill_primrec (q : RawPolynomial) : Primrec₂ (refill q : ℕ → ℕ → ℕ) := by
  induction q with
  | term => exact refillLeaf_primrec false
  | formula => exact refillLeaf_primrec true
  | coefficient C => exact adjoin_primrec
  | unit =>
      exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
        (adjoin_primrec.comp (Primrec.const 0) Primrec.snd) (Primrec.const 0)
  | product a b ia ib =>
      have hr := ib.comp (pi2_primrec.comp Primrec.fst) Primrec.snd
      have hl := ia.comp (pi1_primrec.comp Primrec.fst) (sndIdx_primrec.comp hr)
      exact Primrec.ite
        ((Primrec.eq.comp hr (Primrec.const 0)).or (Primrec.eq.comp hl (Primrec.const 0)))
        (Primrec.const 0)
        (adjoin_primrec.comp
          (pair_primrec.comp (fstIdx_primrec.comp hl) (fstIdx_primrec.comp hr))
          (sndIdx_primrec.comp hl))
  | sum a b ia ib =>
      have hl := ia.comp (pi1_primrec.comp Primrec.fst) Primrec.snd
      have hr := ib.comp (pi1_primrec.comp Primrec.fst) Primrec.snd
      exact Primrec.ite (Primrec.eq.comp (pi2_primrec.comp Primrec.fst) (Primrec.const 0))
        (Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) (Primrec.const 0)
          (adjoin_primrec.comp
            (pair_primrec.comp (fstIdx_primrec.comp hl) (Primrec.const 0))
            (sndIdx_primrec.comp hl)))
        (Primrec.ite (Primrec.eq.comp (pi2_primrec.comp Primrec.fst) (Primrec.const 1))
          (Primrec.ite (Primrec.eq.comp hr (Primrec.const 0)) (Primrec.const 0)
            (adjoin_primrec.comp
              (pair_primrec.comp (fstIdx_primrec.comp hr) (Primrec.const 1))
              (sndIdx_primrec.comp hr))) (Primrec.const 0))

theorem constructor_primrec (formula : Bool) (q : RawPolynomial) :
    Primrec (constructor formula q : ℕ → ℕ) :=
  concat_primrec.comp (childrenWord_primrec q)
    (pair_primrec.comp (shape_primrec q) (Primrec.const (if formula then 1 else 0)))

theorem step_primrec (a b : RawPolynomial) : Primrec₂ (step a b : ℕ → ℕ → ℕ) := by
  have hs := pi1_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1))
  have hk := pi2_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1))
  have hst := arithmetic_sub_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2)) (Primrec.const 1)
  have hl := (refill_primrec a).comp hs hst
  have hr := (refill_primrec b).comp hs hst
  have hleft := Primrec.succ.comp <| adjoin_primrec.comp
    (pair_primrec.comp
      (concat_primrec.comp ((childrenWord_primrec a).comp (fstIdx_primrec.comp hl)) Primrec.fst)
      (Primrec.const 0)) (sndIdx_primrec.comp hl)
  have hright := Primrec.succ.comp <| adjoin_primrec.comp
    (pair_primrec.comp
      (concat_primrec.comp ((childrenWord_primrec b).comp (fstIdx_primrec.comp hr)) Primrec.fst)
      (Primrec.const 1)) (sndIdx_primrec.comp hr)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) (Primrec.const 0) hleft)
      (Primrec.ite (Primrec.eq.comp hk (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp hr (Primrec.const 0)) (Primrec.const 0) hright)
        (Primrec.const 0)))

theorem runPrefix_primrec (a b : RawPolynomial) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => runPrefix a b p.1.1 p.2 p.1.2) := by
  have hz : Primrec (fun p : ℕ × ℕ => (construction (M := ℕ) a b).zero ![p.1, p.2]) :=
    Primrec.snd
  have hs : Primrec₂ (fun (p : ℕ × ℕ) (t : ℕ × ℕ) =>
      (construction (M := ℕ) a b).succ ![p.1, p.2] t.1 t.2) :=
    (step_primrec a b).comp
      (nth_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact pr_primrec (construction (M := ℕ) a b) (fun p : ℕ × ℕ => ![p.1, p.2]) hz hs

private theorem atLength_primrec {f : (ℕ × ℕ) × ℕ → ℕ} (hf : Primrec f) :
    Primrec (fun p : ℕ × ℕ => f ((p.1, p.2), len p.1)) :=
  hf.comp (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) (len_primrec.comp Primrec.fst))

/-- The numerical parser used in the PA graph theorems has an actual
standard primitive-recursion certificate, for arbitrary fixed signature
polynomials and arbitrary input stacks. -/
theorem run_primrec (a b : RawPolynomial) : Primrec₂ (run a b : ℕ → ℕ → ℕ) := by
  exact Primrec.of_eq (atLength_primrec (runPrefix_primrec a b)) (fun _ => rfl)

theorem run_natPrimrec (a b : RawPolynomial) :
    Nat.Primrec (Nat.unpaired (run a b : ℕ → ℕ → ℕ)) :=
  Primrec₂.unpaired'.mpr (run_primrec a b)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors
