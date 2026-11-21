/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationTerms

/-! # Original-name quantifiers and computed alpha comparison

Only the single removed free name is bound. The remaining source free-name type
excludes that name, so capture avoidance follows from name inequalities rather than a
normal-form assumption on the given syntax.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature ArithmeticNamedOpenTranslation

variable (Γ : SyntacticPredicates.Carrier)
local notation "S" => ArithmeticNamedProofConnectives.system Γ

private theorem fromNative (φ : Formula)
    (h : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff
    functionSymbols relationSymbols bound (ArithmeticNamedProofConnectives.system Γ) φ).mpr h

/-- A one-slot source body computes both literal capture-free variable
renamings under the same fresh inner binder seed. -/
theorem body_rename {ξ : Type} (φ : Semiformula ℒₒᵣ ξ 1)
    (seed x y : ℕ) (fn : ξ → ℕ) (hx : x < seed) (hy : y < seed)
    (hf : ∀ i, fn i ≠ x) :
    (ArithmeticNamedOpenTranslation.formula seed ![x] fn φ).substitute x (.var y) =
      some (ArithmeticNamedOpenTranslation.formula seed ![y] fn φ) := by
  have h := formula_substitution_rew φ (Rew.id (L := ℒₒᵣ)) seed ![y] fn ![x] fn
    x (NamedFiniteSyntax.Term.var y) hx (by
      intro z hz
      have he : z = y := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
      subst z
      exact hy)
  have hb : ∀ i : Fin 1, (NamedFiniteSyntax.Term.var (![x] i)).substitute x (.var y) =
      ArithmeticNamedOpenTranslation.term ![y] fn ((Rew.id (L := ℒₒᵣ)) (.bvar i)) := by
    intro i
    fin_cases i
    simp [ArithmeticNamedOpenTranslation.term,NamedFiniteSyntax.Term.substitute]
  have hf' : ∀ i, (NamedFiniteSyntax.Term.var (fn i)).substitute x (.var y) =
      ArithmeticNamedOpenTranslation.term ![y] fn ((Rew.id (L := ℒₒᵣ)) (.fvar i)) := by
    intro i
    simp only [Rew.id_app,ArithmeticNamedOpenTranslation.term,
      NamedFiniteSyntax.Term.substitute,ite_eq_right (hf i)]
  simpa only [ReflectiveRewriting.id_app] using h hb hf'

private theorem body_absent {ξ : Type} (φ : Semiformula ℒₒᵣ ξ 1)
    (seed x z : ℕ) (fn : ξ → ℕ) (hz : z ≠ x) (hf : ∀ i, fn i ≠ z) :
    z ∉ (ArithmeticNamedOpenTranslation.formula seed ![x] fn φ).freeVariables := by
  intro h
  rcases formula_names φ seed ![x] fn z h with ⟨i,hi⟩ | ⟨i,hi⟩
  · fin_cases i
    exact hz (by simpa using hi.symm)
  · exact hf i hi

/-- The universal alpha step is a pair of Hilbert derivations. The body can have arbitrary
nested binders; only the two displayed names must be distinct from its remaining
free-name map. -/
theorem body_alpha {ξ : Type} (φ : Semiformula ℒₒᵣ ξ 1)
    (seed x y : ℕ) (fn : ξ → ℕ) (hx : x < seed) (hy : y < seed)
    (hxy : x ≠ y) (hfx : ∀ i, fn i ≠ x) (hfy : ∀ i, fn i ≠ y) :
    S ⊢ (NamedFiniteSyntax.Formula.all x
      (ArithmeticNamedOpenTranslation.formula seed ![x] fn φ)) 🡘
      (.all y (ArithmeticNamedOpenTranslation.formula seed ![y] fn φ)) := by
  let A := ArithmeticNamedOpenTranslation.formula seed ![x] fn φ
  let B := ArithmeticNamedOpenTranslation.formula seed ![y] fn φ
  have hs : A.substitute x (.var y) = some B := body_rename φ seed x y fn hx hy hfx
  have hr : B.substitute y (.var x) = some A := body_rename φ seed y x fn hy hx hfy
  have hff : A.FreeFor x (.var y) := formula_freeFor_bounded φ seed ![x] fn x (.var y)
    (by
      intro z hz
      have he : z = y := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
      subst z
      exact hy)
  have hfr : B.FreeFor y (.var x) := formula_freeFor_bounded φ seed ![y] fn y (.var x)
    (by
      intro z hz
      have he : z = x := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
      subst z
      exact hx)
  have ha : y ∉ A.freeVariables := body_absent φ seed x y fn (Ne.symm hxy) hfy
  have hb : x ∉ B.freeVariables := body_absent φ seed y x fn hxy hfx
  have hav : y ∉ (NamedFiniteSyntax.Formula.all x A).freeVariables :=
    fun h => ha (List.mem_of_mem_filter h)
  have hbv : x ∉ (NamedFiniteSyntax.Formula.all y B).freeVariables :=
    fun h => hb (List.mem_of_mem_filter h)
  exact E_intro
    (fromNative Γ _ (NamedHilbertQuantifiers.all_rename_forward functionSymbols relationSymbols bound Γ
      x y A B hff hs hav))
    (fromNative Γ _ (NamedHilbertQuantifiers.all_rename_forward functionSymbols relationSymbols bound Γ
      y x B A hfr hr hbv))

/-- Binding a free name and then restoring that name in the bound slot preserves the translated formula. -/
theorem bindRemove_original {n : ℕ} (x : Fin n) (φ : Semiformula ℒₒᵣ (Fin n) 0)
    (seed : ℕ) :
    ArithmeticNamedOpenTranslation.formula seed ![x.val] (fun y => y.val.val)
      (bindRemove x ▹ φ) =
      ArithmeticNamedOpenTranslation.formula seed ![] Fin.val φ := by
  apply formula_rew φ (bindRemove x) seed ![x.val] (fun y => y.val.val) ![] Fin.val
  · intro i; exact i.elim0
  · intro y
    by_cases he : y = x
    · subst y
      simp [bindRemove,ArithmeticNamedOpenTranslation.term]
    · simp [bindRemove,he,ArithmeticNamedOpenTranslation.term]

/-- Giving the removed slot a fresh name agrees exactly with the
ordinary source closing rewrite, including under nested binders. -/
theorem bindRemove_fresh {n : ℕ} (x : Fin n) (φ : Semiformula ℒₒᵣ (Fin n) 0)
    (seed fresh : ℕ) :
    ArithmeticNamedOpenTranslation.formula seed ![fresh] (fun y => y.val.val)
      (bindRemove x ▹ φ) =
      ArithmeticNamedOpenTranslation.formula seed ![fresh] Fin.val (bindName x ▹ φ) := by
  have hr := formula_rew φ (bindRemove x) seed ![fresh] (fun y => y.val.val)
    ![] (fun y => if y = x then fresh else y.val)
    (by intro i; exact i.elim0) (by
      intro y
      by_cases he : y = x
      · subst y; simp [bindRemove,ArithmeticNamedOpenTranslation.term]
      · simp [bindRemove,he,ArithmeticNamedOpenTranslation.term])
  have hn := formula_rew φ (bindName x) seed ![fresh] Fin.val
    ![] (fun y => if y = x then fresh else y.val)
    (by intro i; exact i.elim0) (by
      intro y
      by_cases he : y = x
      · subst y; simp [bindName,ArithmeticNamedOpenTranslation.term]
      · simp [bindName,he,ArithmeticNamedOpenTranslation.term])
  exact hr.trans hn.symm

/-- Each concrete original binder admits the alpha comparison needed by
back translation. The original body is retained exactly. -/
theorem closed_name_alpha {n : ℕ} (x : Fin n) (φ : Semiformula ℒₒᵣ (Fin n) 0)
    (seed : ℕ) (hn : n ≤ seed) :
    S ⊢ (NamedFiniteSyntax.Formula.all x.val
      (ArithmeticNamedOpenTranslation.formula (seed+1) ![] Fin.val φ)) 🡘
      (.all seed (ArithmeticNamedOpenTranslation.formula (seed+1) ![seed] Fin.val
        (bindName x ▹ φ))) := by
  have hx : x.val < seed := x.isLt.trans_le hn
  have h := body_alpha Γ (bindRemove x ▹ φ) (seed+1) x.val seed
    (fun y => y.val.val) (Nat.lt_succ_of_lt hx) (Nat.lt_succ_self seed)
    (Nat.ne_of_lt hx)
    (by
      intro y he
      exact y.property (Fin.ext he))
    (fun y => Nat.ne_of_lt (y.val.isLt.trans_le hn))
  rw [bindRemove_original x φ (seed+1),bindRemove_fresh x φ (seed+1) seed] at h
  exact h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
