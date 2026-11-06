/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbert
import Foundation.Propositional.Entailment.Cl

/-! # Propositional proof rules in the literal named calculus

Local hypotheses are closed only under propositional rules. Deduction,
classical negation, conjunction and disjunction are derived from the actual
three schemes and modus ponens. The constructed entailment instance exposes
these proved rules for subsequent proof-presentation comparisons.
-/

namespace CategoricalEssentialIncompleteness.V46.NamedHilbertPropositional
open SyntacticPredicates
abbrev Formula (σ π : ℕ → Carrier) (d : ℕ) :=
  NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

inductive Local (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
    (Δ : Set (Formula σ π d)) : Formula σ π d → Prop
  | base {φ} : SyntacticNamedHilbert.Derives σ π d Γ φ → Local σ π d Γ Δ φ
  | hypothesis {φ} : φ ∈ Δ → Local σ π d Γ Δ φ
  | mp {φ ψ} : Local σ π d Γ Δ φ → Local σ π d Γ Δ (.imp φ ψ) → Local σ π d Γ Δ ψ

variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)

theorem local_identity (Δ : Set (Formula σ π d)) (φ : Formula σ π d) :
    Local σ π d Γ Δ (.imp φ φ) := by
  have a : Local σ π d Γ Δ (.imp φ (.imp (.imp φ φ) φ)) := .base (.one _ _)
  have b : Local σ π d Γ Δ (.imp φ (.imp φ φ)) := .base (.one _ _)
  have c := Local.base (Δ := Δ) (SyntacticNamedHilbert.Derives.two
    (σ := σ) (π := π) (d := d) (Γ := Γ) φ (.imp φ φ) φ)
  exact .mp b (.mp a c)

theorem deduction (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (h : Local σ π d Γ (insert φ Δ) ψ) : Local σ π d Γ Δ (.imp φ ψ) := by
  classical
  induction h with
  | base h => exact .mp (.base h) (.base (.one _ _))
  | @hypothesis χ hχ =>
      rcases Set.mem_insert_iff.mp hχ with h | h
      · subst χ; exact local_identity σ π d Γ Δ φ
      · exact .mp (.hypothesis h) (.base (.one _ _))
  | @mp χ ψ hc hi ihc ihi => exact .mp ihc (.mp ihi (.base (.two _ _ _)))

theorem local_explosion (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hp : Local σ π d Γ Δ φ) (hn : Local σ π d Γ Δ (.neg φ)) :
    Local σ π d Γ Δ ψ := by
  have a : Local σ π d Γ Δ (.imp (.neg ψ) (.neg φ)) :=
    .mp hn (.base (.one _ _))
  exact .mp hp (.mp a (.base (.three _ _)))

theorem local_empty (φ : Formula σ π d) (h : Local σ π d Γ ∅ φ) :
    SyntacticNamedHilbert.Derives σ π d Γ φ := by
  induction h with
  | base h => exact h
  | hypothesis h => exact False.elim h
  | mp hp hi ihp ihi => exact .modusPonens ihp ihi

theorem local_doubleNegElim (φ : Formula σ π d) :
    Local σ π d Γ {(.neg (.neg φ))} φ := by
  let n : Formula σ π d := .neg φ
  let nn : Formula σ π d := .neg n
  let nnn : Formula σ π d := .neg nn
  let nnnn : Formula σ π d := .neg nnn
  have h0 : Local σ π d Γ {nn} nn := .hypothesis (by simp)
  have h1 : Local σ π d Γ {nn} (.imp (.imp nnnn nn) (.imp n nnn)) :=
    .base (.three n nnn)
  have h2 : Local σ π d Γ {nn} (.imp (.imp n nnn) (.imp nn φ)) :=
    .base (.three nn φ)
  have h3 : Local σ π d Γ {nn} (.imp nn (.imp nnnn nn)) :=
    .base (.one nn nnnn)
  have h4 : Local σ π d Γ {nn} (.imp nnnn nn) := .mp h0 h3
  have h5 : Local σ π d Γ {nn} (.imp n nnn) := .mp h4 h1
  have h6 : Local σ π d Γ {nn} (.imp nn φ) := .mp h5 h2
  exact .mp h0 h6

theorem doubleNegElim (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (.neg (.neg φ)) φ) := by
  apply local_empty σ π d Γ
  exact deduction σ π d Γ ∅ (.neg (.neg φ)) φ
    (by simpa using local_doubleNegElim σ π d Γ φ)

theorem doubleNegIntro (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp φ (.neg (.neg φ))) := by
  exact .modusPonens (doubleNegElim σ π d Γ (.neg φ)) (.three φ (.neg (.neg φ)))

theorem implication_identity (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp φ φ) :=
  local_empty σ π d Γ _ (local_identity σ π d Γ ∅ φ)

theorem implication_trans {φ ψ χ : Formula σ π d}
    (hp : SyntacticNamedHilbert.Derives σ π d Γ (.imp φ ψ))
    (hq : SyntacticNamedHilbert.Derives σ π d Γ (.imp ψ χ)) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp φ χ) := by
  have h := SyntacticNamedHilbert.Derives.modusPonens hq
    (SyntacticNamedHilbert.Derives.one (.imp ψ χ) φ)
  exact .modusPonens hp (.modusPonens h (.two φ ψ χ))

theorem local_mono {Δ Θ : Set (Formula σ π d)} (hsub : Δ ⊆ Θ)
    {φ : Formula σ π d} (h : Local σ π d Γ Δ φ) : Local σ π d Γ Θ φ := by
  induction h with
  | base h => exact .base h
  | hypothesis h => exact .hypothesis (hsub h)
  | mp hp hi ihp ihi => exact .mp ihp ihi

theorem local_trans (Δ : Set (Formula σ π d)) {φ ψ χ : Formula σ π d}
    (hp : Local σ π d Γ Δ (.imp φ ψ)) (hq : Local σ π d Γ Δ (.imp ψ χ)) :
    Local σ π d Γ Δ (.imp φ χ) := by
  have h : Local σ π d Γ Δ (.imp φ (.imp ψ χ)) := .mp hq (.base (.one _ _))
  exact .mp hp (.mp h (.base (.two φ ψ χ)))

def truth : Formula σ π d := .equal (.var 0) (.var 0)
def falsehood : Formula σ π d := .neg (truth σ π d)
def conjunction (φ ψ : Formula σ π d) : Formula σ π d := .neg (.imp φ (.neg ψ))
def disjunction (φ ψ : Formula σ π d) : Formula σ π d := .imp (.neg φ) ψ

theorem local_truth (Δ : Set (Formula σ π d)) : Local σ π d Γ Δ (truth σ π d) :=
  .base (.reflexivity (.var 0))

theorem local_falsehood_elim (Δ : Set (Formula σ π d)) (φ : Formula σ π d)
    (h : Local σ π d Γ Δ (falsehood σ π d)) : Local σ π d Γ Δ φ :=
  local_explosion σ π d Γ Δ (truth σ π d) φ (local_truth σ π d Γ Δ) h

theorem local_neg_intro (Δ : Set (Formula σ π d)) (φ : Formula σ π d)
    (h : Local σ π d Γ (insert φ Δ) (falsehood σ π d)) :
    Local σ π d Γ Δ (.neg φ) := by
  have hd := deduction σ π d Γ Δ φ (falsehood σ π d) h
  have he : Local σ π d Γ Δ (.imp (.neg (.neg φ)) (falsehood σ π d)) :=
    local_trans σ π d Γ Δ (.base (doubleNegElim σ π d Γ φ)) hd
  have hc : Local σ π d Γ Δ (.imp (truth σ π d) (.neg φ)) :=
    .mp he (.base (.three (truth σ π d) (.neg φ)))
  exact .mp (local_truth σ π d Γ Δ) hc

theorem local_by_contradiction (Δ : Set (Formula σ π d)) (φ : Formula σ π d)
    (h : Local σ π d Γ (insert (.neg φ) Δ) (falsehood σ π d)) :
    Local σ π d Γ Δ φ :=
  .mp (local_neg_intro σ π d Γ Δ (.neg φ) h) (.base (doubleNegElim σ π d Γ φ))

theorem local_conjunction_intro (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hp : Local σ π d Γ Δ φ) (hq : Local σ π d Γ Δ ψ) :
    Local σ π d Γ Δ (conjunction σ π d φ ψ) := by
  apply local_neg_intro σ π d Γ Δ (.imp φ (.neg ψ))
  have hp' := local_mono σ π d Γ (Θ := insert (.imp φ (.neg ψ)) Δ)
    (by intro a ha; exact Or.inr ha) hp
  have hq' := local_mono σ π d Γ (Θ := insert (.imp φ (.neg ψ)) Δ)
    (by intro a ha; exact Or.inr ha) hq
  have hd : Local σ π d Γ (insert (.imp φ (.neg ψ)) Δ) (.imp φ (.neg ψ)) :=
    .hypothesis (by simp)
  exact local_explosion σ π d Γ _ ψ (falsehood σ π d) hq' (.mp hp' hd)

theorem local_conjunction_left (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hc : Local σ π d Γ Δ (conjunction σ π d φ ψ)) : Local σ π d Γ Δ φ := by
  apply local_by_contradiction σ π d Γ Δ φ
  let Θ := insert (.neg φ) Δ
  have hn : Local σ π d Γ Θ (.neg φ) := .hypothesis (by simp [Θ])
  have hd : Local σ π d Γ Θ (.imp φ (.neg ψ)) := by
    apply deduction σ π d Γ Θ φ (.neg ψ)
    exact local_explosion σ π d Γ _ φ (.neg ψ) (.hypothesis (by simp))
      (local_mono σ π d Γ (by intro a ha; exact Or.inr ha) hn)
  have hc' := local_mono σ π d Γ (Θ := Θ) (by intro a ha; exact Or.inr ha) hc
  exact local_explosion σ π d Γ Θ (.imp φ (.neg ψ)) (falsehood σ π d) hd hc'

theorem local_conjunction_right (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hc : Local σ π d Γ Δ (conjunction σ π d φ ψ)) : Local σ π d Γ Δ ψ := by
  apply local_by_contradiction σ π d Γ Δ ψ
  let Θ := insert (.neg ψ) Δ
  have hn : Local σ π d Γ Θ (.neg ψ) := .hypothesis (by simp [Θ])
  have hd : Local σ π d Γ Θ (.imp φ (.neg ψ)) := .mp hn (.base (.one _ _))
  have hc' := local_mono σ π d Γ (Θ := Θ) (by intro a ha; exact Or.inr ha) hc
  exact local_explosion σ π d Γ Θ (.imp φ (.neg ψ)) (falsehood σ π d) hd hc'

theorem local_disjunction_left (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hp : Local σ π d Γ Δ φ) : Local σ π d Γ Δ (disjunction σ π d φ ψ) := by
  apply deduction σ π d Γ Δ (.neg φ) ψ
  exact local_explosion σ π d Γ _ φ ψ
    (local_mono σ π d Γ (by intro a ha; exact Or.inr ha) hp) (.hypothesis (by simp))

theorem local_disjunction_right (Δ : Set (Formula σ π d)) (φ ψ : Formula σ π d)
    (hq : Local σ π d Γ Δ ψ) : Local σ π d Γ Δ (disjunction σ π d φ ψ) :=
  .mp hq (.base (.one _ _))

theorem local_disjunction_elim (Δ : Set (Formula σ π d)) (φ ψ χ : Formula σ π d)
    (hp : Local σ π d Γ Δ (.imp φ χ)) (hq : Local σ π d Γ Δ (.imp ψ χ))
    (hor : Local σ π d Γ Δ (disjunction σ π d φ ψ)) : Local σ π d Γ Δ χ := by
  apply local_by_contradiction σ π d Γ Δ χ
  let Θ := insert (.neg χ) Δ
  have hn : Local σ π d Γ Θ (.neg χ) := .hypothesis (by simp [Θ])
  have hp' := local_mono σ π d Γ (Θ := Θ) (by intro a ha; exact Or.inr ha) hp
  have hq' := local_mono σ π d Γ (Θ := Θ) (by intro a ha; exact Or.inr ha) hq
  have hor' := local_mono σ π d Γ (Θ := Θ) (by intro a ha; exact Or.inr ha) hor
  have hnp : Local σ π d Γ Θ (.neg φ) := by
    apply local_neg_intro σ π d Γ Θ φ
    have hp'' := local_mono σ π d Γ (Θ := insert φ Θ)
      (by intro a ha; exact Or.inr ha) hp'
    have hn' := local_mono σ π d Γ (Θ := insert φ Θ)
      (by intro a ha; exact Or.inr ha) hn
    exact local_explosion σ π d Γ _ χ (falsehood σ π d)
      (.mp (.hypothesis (by simp)) hp'') hn'
  exact local_explosion σ π d Γ Θ χ (falsehood σ π d) (.mp (.mp hnp hor') hq') hn

theorem conjunction_left (φ ψ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (conjunction σ π d φ ψ) φ) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ (conjunction σ π d φ ψ) φ
  exact local_conjunction_left σ π d Γ _ φ ψ (.hypothesis (by simp))

theorem conjunction_right (φ ψ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (conjunction σ π d φ ψ) ψ) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ (conjunction σ π d φ ψ) ψ
  exact local_conjunction_right σ π d Γ _ φ ψ (.hypothesis (by simp))

theorem conjunction_intro (φ ψ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp φ (.imp ψ (conjunction σ π d φ ψ))) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ φ (.imp ψ (conjunction σ π d φ ψ))
  apply deduction σ π d Γ (insert φ ∅) ψ (conjunction σ π d φ ψ)
  exact local_conjunction_intro σ π d Γ _ φ ψ
    (.hypothesis (by simp)) (.hypothesis (by simp))

theorem disjunction_left (φ ψ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp φ (disjunction σ π d φ ψ)) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ φ (disjunction σ π d φ ψ)
  exact local_disjunction_left σ π d Γ _ φ ψ (.hypothesis (by simp))

theorem disjunction_right (φ ψ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp ψ (disjunction σ π d φ ψ)) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ ψ (disjunction σ π d φ ψ)
  exact local_disjunction_right σ π d Γ _ φ ψ (.hypothesis (by simp))

theorem disjunction_elim (φ ψ χ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (disjunction σ π d φ ψ) χ))) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ (.imp φ χ) _
  apply deduction σ π d Γ (insert (.imp φ χ) ∅) (.imp ψ χ) _
  apply deduction σ π d Γ (insert (.imp ψ χ) (insert (.imp φ χ) ∅))
    (disjunction σ π d φ ψ) χ
  exact local_disjunction_elim σ π d Γ _ φ ψ χ
    (.hypothesis (by simp)) (.hypothesis (by simp)) (.hypothesis (by simp))

theorem negation_forward (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (.imp (.neg φ) (.imp φ (falsehood σ π d))) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ (.neg φ) _
  apply deduction σ π d Γ (insert (.neg φ) ∅) φ (falsehood σ π d)
  exact local_explosion σ π d Γ _ φ (falsehood σ π d)
    (.hypothesis (by simp)) (.hypothesis (by simp))

theorem negation_reverse (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (.imp (.imp φ (falsehood σ π d)) (.neg φ)) := by
  apply local_empty σ π d Γ
  apply deduction σ π d Γ ∅ (.imp φ (falsehood σ π d)) (.neg φ)
  apply local_neg_intro σ π d Γ _ φ
  exact .mp (φ := φ) (.hypothesis (by simp)) (.hypothesis (by simp))

theorem negation_equiv (φ : Formula σ π d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (conjunction σ π d (.imp (.neg φ) (.imp φ (falsehood σ π d)))
        (.imp (.imp φ (falsehood σ π d)) (.neg φ))) := by
  apply local_empty σ π d Γ
  exact local_conjunction_intro σ π d Γ ∅ _ _
    (.base (negation_forward σ π d Γ φ)) (.base (negation_reverse σ π d Γ φ))

instance connectives : FFL.LogicalConnective (Formula σ π d) where
  tilde := .neg
  arrow := .imp
  wedge := conjunction σ π d
  vee := disjunction σ π d

instance neutral : FFL.LogicalNeutral (Formula σ π d) where
  top := truth σ π d
  bot := falsehood σ π d

structure System (σ π : ℕ → Carrier) (d : ℕ) where
  axioms : Carrier

instance systemEntailment : FFL.Entailment (System σ π d) (Formula σ π d) where
  Prf S φ := PLift (SyntacticNamedHilbert.Derives σ π d S.axioms φ)

noncomputable instance systemClassical (S : System σ π d) : FFL.Entailment.Cl S where
  mdp! hi hp := ⟨.modusPonens hp.down hi.down⟩
  implyK! := ⟨.one _ _⟩
  implyS! := ⟨.two _ _ _⟩
  verum! := ⟨.reflexivity (.var 0)⟩
  dne! := ⟨doubleNegElim σ π d S.axioms _⟩
  and₁! := ⟨conjunction_left σ π d S.axioms _ _⟩
  and₂! := ⟨conjunction_right σ π d S.axioms _ _⟩
  and₃! := ⟨conjunction_intro σ π d S.axioms _ _⟩
  or₁! := ⟨disjunction_left σ π d S.axioms _ _⟩
  or₂! := ⟨disjunction_right σ π d S.axioms _ _⟩
  or₃! := ⟨disjunction_elim σ π d S.axioms _ _ _⟩
  negEquiv! := ⟨negation_equiv σ π d S.axioms _⟩

theorem system_provable_iff (S : System σ π d) (φ : Formula σ π d) :
    FFL.Entailment.Provable S φ ↔ SyntacticNamedHilbert.Derives σ π d S.axioms φ := by
  constructor
  · rintro ⟨h⟩; exact h.down
  · intro h; exact ⟨⟨h⟩⟩

end CategoricalEssentialIncompleteness.V46.NamedHilbertPropositional
