/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkProofComputability
import CategoricalEssentialIncompleteness.EnumerableWords

/-! # Effective validity of the manuscript's finite proof trees -/

noncomputable section
open CategoryTheory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

namespace ProofTree

theorem concludes_of_conclusion {A B : Set ℕ} (t : ProofTree)
    (hp : ∀ x ∈ t.positiveLabels,x ∈ A) (hn : ∀ x ∈ t.negativeLabels,x ∈ B)
    (p : Formula) (h : t.conclusion=some p) : Concludes A B t p := by
  induction t generalizing p with
  | logical1 a b =>
    have he : H1 a b=p := Option.some.inj h
    exact he ▸ Concludes.logical1 a b
  | logical2 a b c =>
    have he : H2 a b c=p := Option.some.inj h
    exact he ▸ Concludes.logical2 a b c
  | logical3 a b =>
    have he : H3 a b=p := Option.some.inj h
    exact he ▸ Concludes.logical3 a b
  | positive x =>
    have he : Formula.atom x=p := Option.some.inj h
    exact he ▸ Concludes.positive (hp x (Finset.mem_singleton_self x))
  | negative x =>
    have he : Formula.neg (.atom x)=p := Option.some.inj h
    exact he ▸ Concludes.negative (hn x (Finset.mem_singleton_self x))
  | mp t u iht ihu =>
    change (t.conclusion.bind (fun a => u.conclusion.bind (fun b =>
      match b with
      | .imp c d => if c=a then some d else none
      | _ => none)))=some p at h
    obtain ⟨a,ha,hh⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b,hb,hm⟩ := Option.bind_eq_some_iff.mp hh
    cases b with
    | atom x => simp at hm
    | neg b => simp at hm
    | imp c d =>
      by_cases he : c=a
      · simp only [he,ite_true] at hm
        have hd : d=p := Option.some.inj hm
        subst c
        subst p
        exact Concludes.mp
          (iht (fun x hx => hp x (Finset.mem_union.mpr (Or.inl hx)))
            (fun x hx => hn x (Finset.mem_union.mpr (Or.inl hx))) a ha)
          (ihu (fun x hx => hp x (Finset.mem_union.mpr (Or.inr hx)))
            (fun x hx => hn x (Finset.mem_union.mpr (Or.inr hx))) (.imp a d) hb)
      · simp [he] at hm

def Valid (A B : Set ℕ) (t : ProofTree) : Prop := ∃ p,Concludes A B t p

theorem valid_iff (A B : Set ℕ) (t : ProofTree) :
    Valid A B t ↔ t.conclusion.isSome ∧
      (∀ x ∈ t.positiveList,x ∈ A) ∧ (∀ x ∈ t.negativeList,x ∈ B) := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨?_,?_,?_⟩
    · rw [concludes_conclusion hp]
      rfl
    · intro x hx
      exact hp.positive_supported x ((mem_positiveList t x).mp hx)
    · intro x hx
      exact hp.negative_supported x ((mem_negativeList t x).mp hx)
  · rintro ⟨hs,hp,hn⟩
    obtain ⟨p,he⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨p,concludes_of_conclusion t
      (fun x hx => hp x ((mem_positiveList t x).mpr hx))
      (fun x hx => hn x ((mem_negativeList t x).mpr hx)) p he⟩

theorem valid_re (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    REPred (Valid A B) := by
  let X : EnumerableCarriers.Carrier := ⟨A,hA⟩
  let Y : EnumerableCarriers.Carrier := ⟨B,hB⟩
  have hp : REPred (fun t : ProofTree => ∀ x ∈ t.positiveList,x ∈ A) := by
    apply (((PartialLists.traverse_partrec
      (EnumerableCarriers.val_partrec (𝟙 X))).comp positiveList_computable).dom_re).of_eq
    intro t
    exact PartialLists.identity_dom X t.positiveList
  have hn : REPred (fun t : ProofTree => ∀ x ∈ t.negativeList,x ∈ B) := by
    apply (((PartialLists.traverse_partrec
      (EnumerableCarriers.val_partrec (𝟙 Y))).comp negativeList_computable).dom_re).of_eq
    intro t
    exact PartialLists.identity_dom Y t.negativeList
  have hs : REPred (fun t : ProofTree => t.conclusion.isSome) :=
    (Primrec.option_isSome.to_comp.comp conclusion_computable).computablePred.to_re
  exact (hs.and (hp.and hn)).of_eq (fun t => (valid_iff A B t).symm)

end ProofTree
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
