/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedFiniteSyntax
public import Mathlib.Logic.Function.Basic

/-! # Semantics and capture-free substitution on literal named finite trees -/

@[expose] public section

universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax.Formula
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ}

theorem substitute_absent (φ : Formula Sig Rel d) (x : ℕ) (t : Term Sig d)
    (hx : x ∉ φ.freeVariables) : φ.substitute x t = some φ := by
  induction φ with
  | equal r s =>
      have hr : x ∉ r.freeVariables := fun h => hx (by simp only [freeVariables, List.mem_append]; exact Or.inl h)
      have hs : x ∉ s.freeVariables := fun h => hx (by simp only [freeVariables, List.mem_append]; exact Or.inr h)
      simp [substitute, r.substitute_absent x t hr, s.substitute_absent x t hs]
  | relation n p children =>
      have he : (fun i => (children i).substitute x t) = children := by
        funext i
        apply Term.substitute_absent
        intro h
        apply hx
        simpa [freeVariables] using (show ∃ i, x ∈ (children i).freeVariables from ⟨i, h⟩)
      simp [substitute, he]
  | neg body ih =>
      have hb : x ∉ body.freeVariables := hx
      simp [substitute, ih hb]
  | imp left right il ir =>
      have hl : x ∉ left.freeVariables := fun h => hx (by simp only [freeVariables, List.mem_append]; exact Or.inl h)
      have hr : x ∉ right.freeVariables := fun h => hx (by simp only [freeVariables, List.mem_append]; exact Or.inr h)
      simp [substitute, il hl, ir hr]
  | all y body ih =>
      by_cases hy : y = x
      · simp [substitute, hy]
      · have hb : x ∉ body.freeVariables := by
          intro h
          apply hx
          simp only [freeVariables, List.mem_filter, bne_iff_ne]
          exact ⟨h, Ne.symm hy⟩
        simp [substitute, hy, hb, ih hb]

variable {K : Type w} (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop)

theorem holds_congr (φ : Formula Sig Rel d) {ρ τ : ℕ → K}
    (h : ∀ x, x ∈ φ.freeVariables → ρ x = τ x) :
    φ.Holds functions relations ρ ↔ φ.Holds functions relations τ := by
  induction φ generalizing ρ τ with
  | equal r t =>
      have hr := r.evaluate_congr functions (fun x hx => h x (by simp only [freeVariables, List.mem_append]; exact Or.inl hx))
      have ht := t.evaluate_congr functions (fun x hx => h x (by simp only [freeVariables, List.mem_append]; exact Or.inr hx))
      simp only [Holds, hr, ht]
  | relation n p children =>
      have he : (fun i => (children i).evaluate functions ρ) =
          (fun i => (children i).evaluate functions τ) := by
        funext i
        apply Term.evaluate_congr
        intro x hx
        apply h
        simpa [freeVariables] using (show ∃ i, x ∈ (children i).freeVariables from ⟨i, hx⟩)
      simp only [Holds, he]
  | neg body ih => exact not_congr (ih h)
  | imp left right il ir =>
      exact imp_congr
        (il (fun x hx => h x (by simp only [freeVariables, List.mem_append]; exact Or.inl hx)))
        (ir (fun x hx => h x (by simp only [freeVariables, List.mem_append]; exact Or.inr hx)))
  | all y body ih =>
      simp only [Holds]
      apply forall_congr'
      intro a
      apply ih
      intro z hz
      by_cases he : z = y
      · subst z
        simp
      · have hz' : z ∈ (all y body).freeVariables := by
          simp only [freeVariables, List.mem_filter, bne_iff_ne]
          exact ⟨hz, he⟩
        simpa [he] using h z hz'

theorem holds_update_absent (φ : Formula Sig Rel d) (x : ℕ) (ρ : ℕ → K) (a : K)
    (hx : x ∉ φ.freeVariables) :
    φ.Holds functions relations (Function.update ρ x a) ↔ φ.Holds functions relations ρ := by
  apply holds_congr
  intro y hy
  have hne : y ≠ x := by
    intro he
    exact hx (he ▸ hy)
  simp [hne]

/-- Semantic substitution retains the original named binder in the
equal-name branch, independently of recursive substitution success. -/
theorem holds_substitute (φ ψ : Formula Sig Rel d) (t : Term Sig d) (x : ℕ) (ρ : ℕ → K)
    (h : φ.substitute x t = some ψ) :
    ψ.Holds functions relations ρ ↔
      φ.Holds functions relations (Function.update ρ x (t.evaluate functions ρ)) := by
  induction φ generalizing ψ ρ with
  | equal r s =>
      simp only [substitute, Option.some.injEq] at h
      subst ψ
      simp only [Holds, Term.evaluate_substitute]
  | relation n p children =>
      simp only [substitute, Option.some.injEq] at h
      subst ψ
      simp only [Holds, Term.evaluate_substitute]
  | neg body ih =>
      cases hb : body.substitute x t with
      | none => simp [substitute, hb] at h
      | some body' =>
          simp only [substitute, hb, Option.map_some, Option.some.injEq] at h
          subst ψ
          exact not_congr (ih body' ρ hb)
  | imp left right il ir =>
      cases hl : left.substitute x t with
      | none => simp [substitute, hl] at h
      | some left' =>
          cases hr : right.substitute x t with
          | none => simp [substitute, hl, hr] at h
          | some right' =>
              simp [substitute, hl, hr] at h
              subst ψ
              exact imp_congr (il left' ρ hl) (ir right' ρ hr)
  | all y body ih =>
      by_cases hy : y = x
      · subst y
        simp [substitute] at h
        subst ψ
        simp only [Holds, Function.update_idem]
      · by_cases hx : x ∉ body.freeVariables
        · have hf : x ∉ (all y body).freeVariables := by
            intro hm
            exact hx (List.mem_filter.mp hm).1
          rw [substitute_absent _ x t hf] at h
          have he := Option.some.inj h
          subst ψ
          exact (holds_update_absent functions relations _ x ρ _ hf).symm
        · by_cases ht : y ∉ t.freeVariables
          · cases hb : body.substitute x t with
            | none => simp [substitute, hy, ht, hb] at h
            | some body' =>
                simp [substitute, hy, ht, hb] at h
                subst ψ
                simp only [Holds]
                apply forall_congr'
                intro a
                have hi := ih body' (Function.update ρ y a) hb
                have hv := t.evaluate_update_absent functions y ρ a ht
                rw [hv, Function.update_comm hy] at hi
                exact hi
          · simp [substitute, hy, hx, ht] at h

end CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax.Formula
