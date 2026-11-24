/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! # Recursive membership in the numerical syntax of Proposition 8.8

At a fixed arity bound, the recursive symbol supports decide the labels in each
record. A word belongs to the indicated sort when all its records pass this test
and the postfix parser leaves a single tree of that sort. -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxMembership
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors SyntacticSyntax.Postfix

private theorem preimage {p : ℕ → Prop} {f : ℕ → ℕ}
    (hp : ComputablePred p) (hf : Computable f) : ComputablePred (fun n => p (f n)) := by
  classical
  exact (hp.decide.comp hf).computablePred

private theorem conjunction {p q : ℕ → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun n => p n ∧ q n) := by
  classical
  apply Computable.computablePred
  exact (Primrec.and.to_comp.comp hp.decide hq.decide).of_eq (by simp)

private theorem disjunction {p q : ℕ → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun n => p n ∨ q n) := by
  classical
  apply Computable.computablePred
  exact (Primrec.or.to_comp.comp hp.decide hq.decide).of_eq (by simp)

private def recursiveLabels : RawPolynomial → Prop
  | .term | .formula | .unit => True
  | .coefficient C => ComputablePred (fun n : ℕ => C.val.Evalb ![n])
  | .product a b | .sum a b => recursiveLabels a ∧ recursiveLabels b

private theorem shape_membership (p : RawPolynomial) (hp : recursiveLabels p) :
    ComputablePred (fun n : ℕ => (rawCarrier zeroCarrier zeroCarrier p).val.Evalb ![n]) := by
  have zeroTest :=
    (Primrec.eq.comp (Primrec.id : Primrec (id : ℕ → ℕ)) (Primrec.const 0)).computablePred
  induction p with
  | term => simpa [rawCarrier, zeroCarrier] using zeroTest
  | formula => simpa [rawCarrier, zeroCarrier] using zeroTest
  | coefficient C => exact hp
  | unit => simpa [rawCarrier] using zeroTest
  | product a b ia ib =>
    apply (conjunction (preimage (ia hp.1) pi1_primrec.to_comp)
      (preimage (ib hp.2) pi2_primrec.to_comp)).of_eq
    intro n
    rw [rawCarrier_product_eval]
    constructor
    · rintro ⟨hu, hv⟩
      exact ⟨π₁ n, π₂ n, (pair_unpair n).symm, hu, hv⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      simpa using And.intro hu hv
  | sum a b ia ib =>
    have tag (k : ℕ) := (Primrec.eq.comp pi2_primrec (Primrec.const k)).computablePred
    apply (disjunction (conjunction (tag 0) (preimage (ia hp.1) pi1_primrec.to_comp))
      (conjunction (tag 1) (preimage (ib hp.2) pi1_primrec.to_comp))).of_eq
    intro n
    rw [rawCarrier_sum_eval]
    constructor
    · rintro (⟨hk, hu⟩ | ⟨hk, hv⟩)
      · exact Or.inl ⟨π₁ n, by simpa only [hk] using (pair_unpair n).symm, hu⟩
      · exact Or.inr ⟨π₁ n, by simpa only [hk] using (pair_unpair n).symm, hv⟩
    · rintro (⟨u, rfl, hu⟩ | ⟨v, rfl, hv⟩)
      · exact Or.inl (by simpa using And.intro (rfl : (0 : ℕ) = 0) hu)
      · exact Or.inr (by simpa using And.intro (rfl : (1 : ℕ) = 1) hv)

private theorem all_entries {p : ℕ → Prop} (hp : ComputablePred p) :
    ComputablePred (fun w : ℕ => ∀ i < len w, p (nth w i)) := by
  classical
  let step (w : ℕ) (s : ℕ × Bool) := s.2 && decide (p (nth w s.1))
  let test (w i : ℕ) : Bool :=
    Nat.rec (motive := fun _ => Bool) true (fun j acc => step w (j, acc)) i
  have hs : Computable₂ step := (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
    (hp.decide.comp (nth_primrec.to_comp.comp Computable.fst
      (Computable.fst.comp Computable.snd)))).to₂
  have spec (w i : ℕ) : test w i = true ↔ ∀ j < i, p (nth w j) := by
    induction i with
    | zero => simp [test]
    | succ i ih =>
      change (test w i && decide (p (nth w i))) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_eq, ih, Nat.forall_lt_succ_right]
  refine ComputablePred.computable_iff.mpr ⟨fun w => test w (len w),
    Computable.nat_rec len_primrec.to_comp (Computable.const true) hs, ?_⟩
  exact funext fun w => propext (spec w (len w)).symm

private theorem word_membership (formula : Bool) (a b : RawPolynomial)
    (ha : recursiveLabels a) (hb : recursiveLabels b) :
    ComputablePred (fun w : ℕ => (plainCarrier formula a b).val.Evalb ![w]) := by
  have hrecord : ComputablePred (fun n : ℕ => (recordCarrier a b).val.Evalb ![n]) := by
    simpa only [rawCarrier, recordCarrier] using shape_membership (.sum a b) ⟨ha, hb⟩
  have hc : ComputablePred (fun w : ℕ => (coefficients a b).val.Evalb ![w]) := by
    apply (all_entries hrecord).of_eq
    intro w
    rw [coefficients, ← FiniteSigmaOne.finite_membership_model,
      FiniteSigmaOne.allEntriesCondition_eval]
  let tag : ℕ := if formula then 1 else 0
  have hr : Primrec (fun w : ℕ => run a b w 1) :=
    (run_primrec a b).comp Primrec.id (Primrec.const 1)
  have hs : Primrec (fun w : ℕ => adjoin (Arithmetic.pair w tag) 0 + 1) :=
    Primrec.succ.comp (adjoin_primrec.comp
      (pair_primrec.comp Primrec.id (Primrec.const tag)) (Primrec.const 0))
  apply (conjunction hc (Primrec.eq.comp hr hs).computablePred).of_eq
  intro w
  rw [← carrier_plain_model, carrier_eval]

private theorem power_labels (p : RawPolynomial) (h : recursiveLabels p) :
    ∀ k, recursiveLabels (SyntaxPolynomial.power p k)
  | 0 => trivial
  | 1 => h
  | k + 2 => ⟨power_labels p h (k + 1), h⟩

private theorem constructor_labels (σ : ℕ → Carrier) (d : ℕ)
    (hσ : ∀ k ≤ d, ComputablePred (fun n : ℕ => (σ k).val.Evalb ![n])) :
    recursiveLabels (SyntaxPolynomial.constructors σ d) := by
  induction d with
  | zero => exact ⟨hσ 0 (by omega), trivial⟩
  | succ d ih =>
    exact ⟨ih fun k hk => hσ k (by omega),
      hσ (d + 1) (by omega), power_labels .term trivial (d + 1)⟩

/-- For either sort, the coefficient decision procedures through the given arity bound
decide membership on every natural-number word. -/
theorem postfix_membership (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (hV : ComputablePred (fun n : ℕ => V.val.Evalb ![n]))
    (hσ : ∀ k ≤ d, ComputablePred (fun n : ℕ => (σ k).val.Evalb ![n]))
    (hπ : ∀ k ≤ d, ComputablePred (fun n : ℕ => (π k).val.Evalb ![n])) (formula : Bool) :
    ComputablePred (fun w : ℕ =>
      (plainCarrier formula (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![w]) :=
  word_membership formula _ _ ⟨hV, constructor_labels σ d hσ⟩
    ⟨⟨⟨⟨power_labels .term trivial 2, constructor_labels π d hπ⟩, trivial⟩,
      power_labels .formula trivial 2⟩, hV, trivial⟩

/-- In Proposition 8.8 the variables range over all naturals, and each symbol object
is unary. Its tuple code is the symbol itself. -/
theorem numerical_word_membership (σ π : ℕ → EnumerableCarriers.Total) (d : ℕ)
    (hσ : ∀ k ≤ d, ComputablePred (· ∈ (σ k).obj.support))
    (hπ : ∀ k ≤ d, ComputablePred (· ∈ (π k).obj.support)) (formula : Bool) :
    ComputablePred (fun w : ℕ => (plainCarrier formula
      (SyntaxPolynomial.termExpression
        (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
        (fun k => NumericalCoordinates.codedPredicate (NumericalTuples.unary (σ k))) d)
      (SyntaxPolynomial.formulaExpression
        (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
        (fun k => NumericalCoordinates.codedPredicate (NumericalTuples.unary (π k))) d)
      ).val.Evalb ![w]) := by
  have coeff (C : EnumerableCarriers.Total) (hC : ComputablePred (· ∈ C.obj.support)) :
      ComputablePred (fun n : ℕ =>
        (NumericalCoordinates.codedPredicate (NumericalTuples.unary C)).val.Evalb ![n]) :=
    hC.of_eq fun n => by
      rw [NumericalCoordinates.codedPredicate_eval, NumericalTuples.codedSupport_unary]
  apply postfix_membership
  · apply (Primrec.eq.comp (Primrec.const (0 : ℕ)) (Primrec.const 0)).computablePred.of_eq
    intro n
    exact iff_of_true rfl (NumericalNamed.codedVariable_member n)
  · exact fun k hk => coeff (σ k) (hσ k hk)
  · exact fun k hk => coeff (π k) (hπ k hk)

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxMembership
