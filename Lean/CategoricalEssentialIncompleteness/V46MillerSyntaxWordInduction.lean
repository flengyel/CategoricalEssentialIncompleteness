/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance

/-! # Arbitrary-property induction on the original standard syntax words

The existing PA-proved parser decomposition and strict child-size laws are
used at their standard N values. The induction predicate is any Lean Prop;
no PA-definability of the uniform target operation or candidate morphism is
required. The same word carrier is retained through the proved plain/stored
acceptance equivalence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.WordInduction

def ChildHolds (H : Bool → ℕ → Prop) : RawPolynomial → ℕ → Prop
  | .term,u => H false u
  | .formula,u => H true u
  | .coefficient _,_ => True
  | .unit,_ => True
  | .product a b,u => ChildHolds H a (π₁ u) ∧ ChildHolds H b (π₂ u)
  | .sum a b,u => if π₂ u=0 then ChildHolds H a (π₁ u) else ChildHolds H b (π₁ u)

theorem childHolds_of_smaller (a b : RawPolynomial) (H : Bool → ℕ → Prop)
    (q : RawPolynomial) (n u : ℕ)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) q).val.Evalb ![u])
    (hs : ChildSize q n u)
    (h : ∀ (formula : Bool) (word : ℕ), len word<n → (Postfix.carrier formula a b).val.Evalb ![word] → H formula word) :
    ChildHolds H q u := by
  induction q generalizing u with
  | term => exact h false u (by simpa [ChildSize] using hs) hu
  | formula => exact h true u (by simpa [ChildSize] using hs) hu
  | coefficient _ => trivial
  | unit => trivial
  | product c d ic id =>
      obtain ⟨x,y,rfl,hx,hy⟩ :=
        (rawCarrier_product_eval (Postfix.carrier false a b) (Postfix.carrier true a b) c d u).mp hu
      have hsz : ChildSize c n x ∧ ChildSize d n y := by simpa [ChildSize] using hs
      simpa [ChildHolds] using And.intro (ic x hx hsz.1) (id y hy hsz.2)
  | sum c d ic id =>
      rcases (rawCarrier_sum_eval (Postfix.carrier false a b) (Postfix.carrier true a b) c d u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · simpa [ChildHolds] using ic x hx (by simpa [ChildSize] using hs)
      · simpa [ChildHolds] using id y hy (by simpa [ChildSize] using hs)

/-- Every accepted constructor word is generated from its ordered strictly smaller
children, for arbitrary external properties. -/
theorem word_induction (a b : RawPolynomial) (H : Bool → ℕ → Prop)
    (root : ∀ (formula : Bool) (u : ℕ),
      (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b)
        (if formula then b else a)).val.Evalb ![u] →
      ChildHolds H (if formula then b else a) u →
        H formula (constructor formula (if formula then b else a) u)) :
    ∀ formula word,(Postfix.carrier formula a b).val.Evalb (M := ℕ) ![word] → H formula word := by
  have aux : ∀ n : ℕ,∀ formula word,len word=n →
      (Postfix.carrier formula a b).val.Evalb (M := ℕ) ![word] → H formula word := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro formula word hn hw
        obtain ⟨u,hu,he⟩ := Postfix.carrier_decomposition formula a b word hw
        subst word
        apply root formula u hu
        apply childHolds_of_smaller a b H (if formula then b else a) n u hu
        · rw [← hn]
          exact (childSizeGraph_eval _ _ _).mp (children_smaller formula (if formula then b else a) u)
        · intro sort child hlt hc
          exact ih (len child) hlt sort child rfl hc
  intro formula word hw
  exact aux (len word) formula word rfl hw

theorem plain_word_induction (a b : RawPolynomial) (H : Bool → ℕ → Prop)
    (root : ∀ (formula : Bool) (u : ℕ),
      (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b)
        (if formula then b else a)).val.Evalb ![u] →
      ChildHolds H (if formula then b else a) u →
        H formula (constructor formula (if formula then b else a) u)) :
    ∀ formula word,(Postfix.plainCarrier formula a b).val.Evalb (M := ℕ) ![word] → H formula word := by
  intro formula word hw
  exact word_induction a b H root formula word ((Postfix.carrier_plain_model formula a b word).mpr hw)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.WordInduction
