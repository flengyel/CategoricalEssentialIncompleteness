import CategoricalEssentialIncompleteness.V46ForkAxiomClosure

/-! # Arbitrary c.e. axiom sets and individual endpoint extensions -/

noncomputable section

open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
open CategoricalEssentialIncompleteness.V46.ForkAxiomClosure

example (A : Set ℕ) (hA : REPred (· ∈ A)) : REPred (Derives A) := derives_re A hA

example (A : Set ℕ) (hA : REPred (· ∈ A)) : REPred (· ∈ theoremCodes A) :=
  theoremCodes_re A hA

example (A : Set ℕ) (p : Formula) : Derives A p ↔ ∃ t : ProofTree,
    CategoricalEssentialIncompleteness.V46.ForkAxiomClosure.conclusion t = some p ∧
      ∀ n ∈ t.positiveList, n ∈ A := derives_iff_record A p

example {A : Set ℕ} {S : Set Formula}
    (h1 : ∀ p q, H1 p q ∈ S) (h2 : ∀ p q r, H2 p q r ∈ S)
    (h3 : ∀ p q, H3 p q ∈ S) (ha : ∀ n ∈ A, Formula.decode n ∈ S)
    (hm : ∀ p q, p ∈ S → Formula.imp p q ∈ S → q ∈ S) :
    ∀ p, Derives A p → p ∈ S := derives_least h1 h2 h3 ha hm

example (i : Bool) (A : Set ℕ) (hA : REPred (· ∈ A))
    (hext : EnumerableCarriers.support (endpointTheory i categoricalTheory) ⊆ theoremCodes A)
    (hc : ∀ p : Formula, ¬(Derives A p ∧ Derives A (.neg p))) :
    ∃ p : Formula, ¬Derives A p ∧ ¬Derives A (.neg p) :=
  endpoint_axiom_extension_incomplete i A hA hext hc
