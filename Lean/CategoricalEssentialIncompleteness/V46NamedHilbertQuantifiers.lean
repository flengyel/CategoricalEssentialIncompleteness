/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedHilbertPropositional
import CategoricalEssentialIncompleteness.V46NamedFiniteSemantics

/-! # Derived first-order rules in the literal named calculus

Every proof below is built from the existing seven native schemes,
generalization and ordered modus ponens. No first-order entailment
instance or substitution-compatibility theorem is supplied as a field.
-/
noncomputable section
open FFL
namespace CategoricalEssentialIncompleteness.V46.NamedHilbertQuantifiers
open NamedFiniteSyntax NamedPostfixEncoding SyntacticPredicates

section Syntax
universe u v
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ}

theorem term_substitute_self (r : NamedFiniteSyntax.Term Sig d) (x : ℕ) :
    r.substitute x (.var x) = r := by
  induction r with
  | var y => by_cases h : y = x <;> simp [Term.substitute,h]
  | app n f children ih =>
      change Term.app n f (fun i => (children i).substitute x (.var x)) = Term.app n f children
      congr 1
      funext i
      exact ih i

theorem formula_freeFor_self (φ : NamedFiniteSyntax.Formula Sig Rel d) (x : ℕ) :
    φ.FreeFor x (.var x) := by
  induction φ with
  | equal r t => trivial
  | relation n p children => trivial
  | neg body ih => exact ih
  | imp left right il ir => exact ⟨il,ir⟩
  | all y body ih =>
      by_cases h : y = x
      · exact Or.inl h
      · exact Or.inr ⟨h,Or.inr (by simpa [Term.freeVariables] using h),ih⟩

theorem formula_substitute_self (φ : NamedFiniteSyntax.Formula Sig Rel d) (x : ℕ) :
    φ.substitute x (.var x) = some φ := by
  induction φ with
  | equal r t => simp [Formula.substitute,term_substitute_self]
  | relation n p children =>
      simp only [Formula.substitute]
      congr 2
      funext i
      exact term_substitute_self (children i) x
  | neg body ih => simp [Formula.substitute,ih]
  | imp left right il ir => simp [Formula.substitute,il,ir]
  | all y body ih =>
      by_cases h : y = x
      · simp [Formula.substitute,h]
      · have hy : y ∉ (Term.var x : NamedFiniteSyntax.Term Sig d).freeVariables := by
          simpa [Term.freeVariables] using h
        simp [Formula.substitute,h,hy,ih]

/-- Absence is a syntactic substitution equation even under an equal
binder, where no condition on the recursive body is required. -/
theorem formula_substitute_absent (φ : NamedFiniteSyntax.Formula Sig Rel d) (x : ℕ)
    (t : NamedFiniteSyntax.Term Sig d) (hx : x ∉ φ.freeVariables) :
    φ.substitute x t = some φ :=
  NamedFiniteSyntax.Formula.substitute_absent φ x t hx

theorem bound_absent (x : ℕ) (φ : NamedFiniteSyntax.Formula Sig Rel d) :
    x ∉ (Formula.all x φ).freeVariables := by
  simp [Formula.freeVariables]

end Syntax

variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "D" => SyntacticNamedHilbert.Derives σ π d Γ

/-- Self-instantiation is the actual native instantiation constructor,
with its independently proved free-for and substitution equations. -/
theorem all_elim_self (x : ℕ) (φ : Fm) : D (.imp (.all x φ) φ) :=
  .instantiation x φ (.var x) φ (formula_freeFor_self φ x) (formula_substitute_self φ x)

/-- Global implication proofs are mapped by universal quantification.
The printed distribution scheme is used with antecedent ∀xφ, whose
absence side condition follows from the literal FV definition. -/
theorem all_mono (x : ℕ) {φ ψ : Fm} (h : D (.imp φ ψ)) :
    D (.imp (.all x φ) (.all x ψ)) := by
  have he : D (.imp (.all x φ) ψ) :=
    NamedHilbertPropositional.implication_trans σ π d Γ (all_elim_self σ π d Γ x φ) h
  have hg : D (.all x (.imp (.all x φ) ψ)) := .generalization x he
  exact .modusPonens hg (.distribution x (.all x φ) ψ (bound_absent x φ))

theorem all_congr (x : ℕ) {φ ψ : Fm}
    (hp : D (.imp φ ψ)) (hq : D (.imp ψ φ)) :
    D (.imp (.all x φ) (.all x ψ)) ∧ D (.imp (.all x ψ) (.all x φ)) :=
  ⟨all_mono σ π d Γ x hp,all_mono σ π d Γ x hq⟩

/-- Vacuous quantification follows from the actual distribution scheme
and a proved identity implication. -/
theorem all_vacuous (x : ℕ) (φ : Fm) (hx : x ∉ φ.freeVariables) :
    D (.imp φ (.all x φ)) := by
  have hi : D (.all x (.imp φ φ)) :=
    .generalization x (NamedHilbertPropositional.implication_identity σ π d Γ φ)
  exact .modusPonens hi (.distribution x φ φ hx)

/-- A concrete capture-free named substitution and genuine absence
condition give the corresponding universal binder-renaming implication.
No alpha-equivalence or first-order proof comparison is assumed. -/
theorem all_rename_forward (x y : ℕ) (φ ψ : Fm)
    (hff : φ.FreeFor x (.var y)) (hs : φ.substitute x (.var y) = some ψ)
    (hy : y ∉ (Formula.all x φ).freeVariables) :
    D (.imp (.all x φ) (.all y ψ)) := by
  have hi : D (.imp (.all x φ) ψ) := .instantiation x φ (.var y) ψ hff hs
  have hg : D (.all y (.imp (.all x φ) ψ)) := .generalization y hi
  exact .modusPonens hg (.distribution y (.all x φ) ψ hy)

/-- Generalization under an antecedent uses exactly the manuscript
absence side condition, expressed in the independent literal FV list. -/
theorem all_intro_under (x : ℕ) (δ φ : Fm)
    (hx : x ∉ δ.freeVariables) (h : D (.imp δ φ)) : D (.imp δ (.all x φ)) :=
  .modusPonens (.generalization x h) (.distribution x δ φ hx)

/-- Existential introduction is derived from actual universal
instantiation and the existing third propositional scheme. -/
theorem exists_intro (x : ℕ) (φ ψ : Fm) (t : Tm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    D (.imp ψ (.neg (.all x (.neg φ)))) := by
  have hsn : (Formula.neg φ).substitute x t = some (.neg ψ) := by
    simp [Formula.substitute,hs]
  have hi : D (.imp (.all x (.neg φ)) (.neg ψ)) :=
    .instantiation x (.neg φ) t (.neg ψ) hff hsn
  have hd : D (.imp (.neg (.neg (.all x (.neg φ)))) (.neg ψ)) :=
    NamedHilbertPropositional.implication_trans σ π d Γ
      (NamedHilbertPropositional.doubleNegElim σ π d Γ (.all x (.neg φ))) hi
  exact .modusPonens hd (.three ψ (.neg (.all x (.neg φ))))

end CategoricalEssentialIncompleteness.V46.NamedHilbertQuantifiers
