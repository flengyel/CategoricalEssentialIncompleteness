/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Applications

/-! # Finite Hilbert proofs from an arbitrary computably enumerable axiom set -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
open CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

namespace CategoricalEssentialIncompleteness.V46.ForkAxiomClosure

/-- Axioms are arbitrary formula codes; modus ponens and the three
displayed Hilbert schemes generate their deductive closure. -/
inductive Derives (A : Set ℕ) : Formula → Prop where
  | logical1 (p q) : Derives A (H1 p q)
  | logical2 (p q r) : Derives A (H2 p q r)
  | logical3 (p q) : Derives A (H3 p q)
  | fromAxiom {n} : n ∈ A → Derives A (Formula.decode n)
  | mp {p q} : Derives A p → Derives A (.imp p q) → Derives A q

/-- The existing numerical proof-tree data support arbitrary axiom
formulas by decoding their leaf labels. -/
def conclusion : ProofTree → Option Formula :=
  ProofTree.fold (fun p => some (H1 p.1 p.2))
    (fun p => some (H2 p.1 p.2.1 p.2.2)) (fun p => some (H3 p.1 p.2))
    (fun n => some (Formula.decode n)) (fun _ => none) mpStep

theorem conclusion_computable : Computable conclusion :=
  ProofTree.fold_computable
    (Primrec.option_some.to_comp.comp H1_computable)
    (Primrec.option_some.to_comp.comp H2_computable)
    (Primrec.option_some.to_comp.comp H3_computable)
    (Primrec.option_some.to_comp.comp Formula.decode_computable)
    (Computable.const none) mpStep_computable

theorem derives_of_conclusion (A : Set ℕ) (t : ProofTree)
    (hs : ∀ n ∈ t.positiveList, n ∈ A) (p : Formula) (hp : conclusion t = some p) :
    Derives A p := by
  induction t generalizing p with
  | logical1 a b =>
    have he : H1 a b = p := Option.some.inj hp
    exact he ▸ Derives.logical1 a b
  | logical2 a b c =>
    have he : H2 a b c = p := Option.some.inj hp
    exact he ▸ Derives.logical2 a b c
  | logical3 a b =>
    have he : H3 a b = p := Option.some.inj hp
    exact he ▸ Derives.logical3 a b
  | positive n =>
    have he : Formula.decode n = p := Option.some.inj hp
    exact he ▸ Derives.fromAxiom (hs n (by simp [ProofTree.positiveList, ProofTree.fold, List.singleton]))
  | negative n => simp [conclusion, ProofTree.fold] at hp
  | mp t u iht ihu =>
    change (conclusion t).bind (fun a => (conclusion u).bind (mpResult a)) = some p at hp
    obtain ⟨a, ha, hh⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨b, hb, hm⟩ := Option.bind_eq_some_iff.mp hh
    rw [mpResult_eq] at hm
    cases b with
    | atom n => simp at hm
    | neg b => simp at hm
    | imp c d =>
      by_cases he : c = a
      · simp only [he, ↓reduceIte] at hm
        have hd : d = p := Option.some.inj hm
        subst c
        subst p
        exact Derives.mp
          (iht (fun n hn => hs n (by
            change n ∈ t.positiveList ++ u.positiveList
            exact List.mem_append.mpr (Or.inl hn))) a ha)
          (ihu (fun n hn => hs n (by
            change n ∈ t.positiveList ++ u.positiveList
            exact List.mem_append.mpr (Or.inr hn))) (.imp a d) hb)
      · simp [he] at hm

/-- The inductive consequence relation has exactly the displayed finite
proof records, with all their axiom leaves checked. -/
theorem derives_iff_record (A : Set ℕ) (p : Formula) :
    Derives A p ↔ ∃ t : ProofTree,
      conclusion t = some p ∧ ∀ n ∈ t.positiveList, n ∈ A := by
  constructor
  · intro h
    induction h with
    | logical1 p q => exact ⟨.logical1 p q, rfl, by simp [ProofTree.positiveList, ProofTree.fold]⟩
    | logical2 p q r => exact ⟨.logical2 p q r, rfl, by simp [ProofTree.positiveList, ProofTree.fold]⟩
    | logical3 p q => exact ⟨.logical3 p q, rfl, by simp [ProofTree.positiveList, ProofTree.fold]⟩
    | @fromAxiom n hn =>
      exact ⟨.positive n, rfl, by simpa [ProofTree.positiveList, ProofTree.fold, List.singleton] using hn⟩
    | @mp p q _ _ ihp ihq =>
      obtain ⟨t, ht, hs⟩ := ihp
      obtain ⟨u, hu, hr⟩ := ihq
      refine ⟨.mp t u, ?_, ?_⟩
      · change mpStep (conclusion t, conclusion u) = some q
        rw [ht, hu]
        simp [mpStep, mpResult_eq]
      · intro n hn
        change n ∈ t.positiveList ++ u.positiveList at hn
        exact (List.mem_append.mp hn).elim (hs n) (hr n)
  · rintro ⟨t, ht, hs⟩
    exact derives_of_conclusion A t hs p ht

theorem derives_least {A : Set ℕ} {S : Set Formula}
    (h1 : ∀ p q, H1 p q ∈ S) (h2 : ∀ p q r, H2 p q r ∈ S)
    (h3 : ∀ p q, H3 p q ∈ S) (ha : ∀ n ∈ A, Formula.decode n ∈ S)
    (hm : ∀ p q, p ∈ S → Formula.imp p q ∈ S → q ∈ S) :
    ∀ p, Derives A p → p ∈ S := by
  intro p hp
  induction hp with
  | logical1 p q => exact h1 p q
  | logical2 p q r => exact h2 p q r
  | logical3 p q => exact h3 p q
  | fromAxiom hn => exact ha _ hn
  | mp _ _ ihp ihq => exact hm _ _ ihp ihq

theorem supported_leaves_re (A : Set ℕ) (hA : REPred (· ∈ A)) :
    REPred (fun t : ProofTree => ∀ n ∈ t.positiveList, n ∈ A) := by
  let X : EnumerableCarriers.Carrier := ⟨A, hA⟩
  apply (((PartialLists.traverse_partrec
    (EnumerableCarriers.val_partrec (𝟙 X))).comp ProofTree.positiveList_computable).dom_re).of_eq
  intro t
  exact PartialLists.identity_dom X t.positiveList

/-- Finite proof search is computably enumerable for every c.e. axiom
set, with no decidability assumption on membership in that set. -/
theorem derives_re (A : Set ℕ) (hA : REPred (· ∈ A)) : REPred (Derives A) := by
  have he : Computable (fun z : Formula × ProofTree => decide (conclusion z.2 = some z.1)) :=
    Primrec.eq.decide.to_comp.comp
      (conclusion_computable.comp Computable.snd)
      (Primrec.option_some.to_comp.comp Computable.fst)
  have hc : REPred (fun z : Formula × ProofTree => conclusion z.2 = some z.1) :=
    he.computablePred.to_re.of_eq (fun _ => by simp)
  have hs : REPred (fun z : Formula × ProofTree => ∀ n ∈ z.2.positiveList, n ∈ A) :=
    REPred.comp Computable.snd (supported_leaves_re A hA)
  exact (hc.and hs).projection.of_eq (fun p => (derives_iff_record A p).symm)

def theoremCodes (A : Set ℕ) : Set ℕ := {n | Derives A (Formula.decode n)}

theorem theoremCodes_re (A : Set ℕ) (hA : REPred (· ∈ A)) : REPred (· ∈ theoremCodes A) :=
  (derives_re A hA).comp Formula.decode_computable

/-- An individual endpoint has no complete consistent c.e.-axiomatized
extension. Extension is inclusion in the generated theorem set. -/
theorem endpoint_axiom_extension_incomplete (i : Bool) (A : Set ℕ)
    (hA : REPred (· ∈ A))
    (hext : EnumerableCarriers.support (ForkSyntax.endpointTheory i ForkSyntax.categoricalTheory) ⊆
      theoremCodes A)
    (hc : ∀ p : Formula, ¬(Derives A p ∧ Derives A (.neg p))) :
    ∃ p : Formula, ¬Derives A p ∧ ¬Derives A (.neg p) := by
  have hcons : ∀ n : ℕ, n ∈ theoremCodes A → negCode n ∉ theoremCodes A := by
    intro n hn hneg
    exact hc (Formula.decode n) ⟨hn, by
      change Derives A (Formula.decode (negCode n)) at hneg
      rwa [ForkSyntax.decode_negCode] at hneg⟩
  obtain ⟨n, hn, hneg⟩ := ForkSyntax.endpoint_ce_extension_incomplete i (theoremCodes A)
    (theoremCodes_re A hA) hext hcons
  refine ⟨Formula.decode n, hn, ?_⟩
  simpa only [theoremCodes, Set.mem_ofPred_eq, ForkSyntax.decode_negCode] using hneg

end CategoricalEssentialIncompleteness.V46.ForkAxiomClosure
