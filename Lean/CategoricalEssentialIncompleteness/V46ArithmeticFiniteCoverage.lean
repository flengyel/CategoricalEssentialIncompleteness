/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedFiniteSupport

/-! # Definable coverage of one internal finite support by another -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ArithmeticFiniteCoverage
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Every entry of the first vector occurs in the second vector. -/
def Covers (s l : M) : Prop := ∀ i < len s, MemVec (nth s i) l

/-- Coverage has both Sigma-one and Pi-one definitions, even for internal
vectors of nonstandard length. -/
instance covers_definable (Γ m) : Γ-[m + 1]-Relation (Covers : M → M → Prop) := by
  unfold Covers
  definability

theorem covers_iff (s l : M) : Covers s l ↔ ∀ x, MemVec x s → MemVec x l := by
  constructor
  · rintro h x ⟨i, hi, hx⟩
    exact hx ▸ h i hi
  · intro h i hi
    exact h (nth s i) ⟨i, hi, rfl⟩

@[simp] theorem covers_nil (l : M) : Covers 0 l := by simp [Covers]

@[simp] theorem covers_adjoin (x s l : M) :
    Covers (adjoin x s) l ↔ MemVec x l ∧ Covers s l := by
  simp only [covers_iff, memVec_adjoin_iff]
  constructor
  · intro h
    exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩
  · rintro ⟨hx, hs⟩ y (rfl | hy)
    · exact hx
    · exact hs y hy

@[simp] theorem covers_append (a b l : M) :
    Covers (SyntacticSyntax.Words.append a b) l ↔ Covers a l ∧ Covers b l := by
  simp only [covers_iff, ArithmeticSignedFiniteSupport.mem_append]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨ha, hb⟩ x (hx | hx)
    · exact ha x hx
    · exact hb x hx

theorem covers_refl (s : M) : Covers s s :=
  (covers_iff s s).mpr (fun _ h => h)

theorem covers_trans {a b l : M} (hab : Covers a b) (hbl : Covers b l) : Covers a l :=
  (covers_iff a l).mpr (fun x hx => (covers_iff b l).mp hbl x ((covers_iff a b).mp hab x hx))

theorem covers_append_left (a b : M) : Covers a (SyntacticSyntax.Words.append a b) :=
  (covers_iff _ _).mpr (fun x hx =>
    (ArithmeticSignedFiniteSupport.mem_append x a b).mpr (Or.inl hx))

theorem covers_append_right (a b : M) : Covers b (SyntacticSyntax.Words.append a b) :=
  (covers_iff _ _).mpr (fun x hx =>
    (ArithmeticSignedFiniteSupport.mem_append x a b).mpr (Or.inr hx))

/-- A Sigma-one formula used negatively in the Pi-one truth invariant. -/
def formula : 𝚺₁.Semiformula M 2 :=
  Classical.choose (covers_definable (M := M) 𝚺 0).definable

@[simp] theorem formula_eval (s l : M) :
    (formula (M := M)).val.Eval ![s, l] id ↔ Covers s l :=
  (Classical.choose_spec (covers_definable (M := M) 𝚺 0).definable).iff

end CategoricalEssentialIncompleteness.V46.ArithmeticFiniteCoverage
