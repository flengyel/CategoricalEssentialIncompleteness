/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ModelLogicalSoundness

/-! # Distribution soundness with an opaque interpreted variable object -/

@[expose] public section

noncomputable section
universe v u w k
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ModelQuantifierSoundness
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (G : C ⥤ Type w) {V Fm : C} {K : Type k}
variable (name : G.obj V → ℕ) (imp : Fm ⨯ Fm ⟶ Fm) (quantifier : V ⨯ Fm ⟶ Fm)
variable (P : G.obj Fm → (ℕ → K) → Prop)
variable (himp : ∀ (z : G.obj (Fm ⨯ Fm)) (ρ : ℕ → K), P (G.map imp z) ρ ↔
  (P (G.map (prod.fst : Fm ⨯ Fm ⟶ Fm) z) ρ → P (G.map (prod.snd : Fm ⨯ Fm ⟶ Fm) z) ρ))
variable (hall : ∀ (z : G.obj (V ⨯ Fm)) (ρ : ℕ → K), P (G.map quantifier z) ρ ↔
  ∀ a : K, P (G.map (prod.snd : V ⨯ Fm ⟶ Fm) z)
    (Function.update ρ (name (G.map (prod.fst : V ⨯ Fm ⟶ V) z)) a))

include himp hall

/-- The absence hypothesis is assignment invariance of the antecedent.
The concrete application proves it from the actual false-membership fiber. -/
theorem valid_distribution (q : G.obj (V ⨯ (Fm ⨯ Fm)))
    (habs : ∀ (ρ : ℕ → K) (a : K),
      P (G.map (prod.fst : Fm ⨯ Fm ⟶ Fm) (G.map (prod.snd : V ⨯ (Fm ⨯ Fm) ⟶ _) q))
          (Function.update ρ (name (G.map (prod.fst : V ⨯ (Fm ⨯ Fm) ⟶ V) q)) a) ↔
        P (G.map (prod.fst : Fm ⨯ Fm ⟶ Fm) (G.map (prod.snd : V ⨯ (Fm ⨯ Fm) ⟶ _) q)) ρ) :
    ∀ ρ : ℕ → K, P (G.map (prod.lift
      (prod.lift prod.fst (prod.snd ≫ imp) ≫ quantifier)
      (prod.lift (prod.snd ≫ prod.fst)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ quantifier) ≫ imp) ≫ imp) q) ρ := by
  intro ρ
  simp only [Functor.map_comp_apply,himp,hall,
    ModelLogicalSoundness.map_lift_fst,ModelLogicalSoundness.map_lift_snd]
  intro h hφ a
  exact h a ((habs ρ a).mpr hφ)

end CategoricalEssentialIncompleteness.V46.ModelQuantifierSoundness
