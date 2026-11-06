/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46DerivationConclusionInduction
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Ordered finite-power points for finite typed derivation trees -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
open SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

@[simp] theorem finiteChild_castSucc (X : PredicateCategory T) (n : ℕ) (k : Fin (n + 1)) :
    finiteChild T X (n + 2) k.castSucc =
      (prod.fst : finitePower X (n + 1) ⨯ X ⟶ _) ≫ finiteChild T X (n + 1) k := by
  simp only [finiteChild,SyntacticDerivation.PolynomialComparison.powerIso,
    prod.mapIso_hom,Iso.refl_hom,powerProjection_castSucc]
  exact prod.map_fst_assoc _ _ _

@[simp] theorem finiteChild_last (X : PredicateCategory T) (n : ℕ) :
    finiteChild T X (n + 2) (Fin.last (n + 1)) =
      (prod.snd : finitePower X (n + 1) ⨯ X ⟶ X) := by
  simp only [finiteChild,SyntacticDerivation.PolynomialComparison.powerIso,
    prod.mapIso_hom,Iso.refl_hom,powerProjection_last,prod.map_snd,Category.comp_id]

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Read one prefix coordinate through the actual product projection. -/
theorem finiteChild_castSucc_point (X : PredicateCategory T) (n : ℕ) (k : Fin (n + 1))
    (z : Obj T M (finitePower X (n + 2))) :
    (F T M).map (finiteChild T X (n + 2) k.castSucc) z =
      (F T M).map (finiteChild T X (n + 1) k)
        ((F T M).map (prod.fst : finitePower X (n + 1) ⨯ X ⟶ _) z) := by
  have h := congrArg (fun f => (F T M).map f z) (finiteChild_castSucc T X n k)
  exact h.trans ((F T M).map_comp_apply _ _ z)

/-- Every finite ordered family has an actual point of the chosen power.
The empty family uses the preserved terminal point, not a dummy formula. -/
theorem powerPoints_exists (X : PredicateCategory T) (n : ℕ) (xs : Fin n → Obj T M X) :
    ∃ z : Obj T M (finitePower X n),
      ∀ k : Fin n, (F T M).map (finiteChild T X n k) z = xs k := by
  induction n with
  | zero => exact ⟨modelTerminalPoint T M,fun k => k.elim0⟩
  | succ n ih =>
      cases n with
      | zero =>
          refine ⟨xs 0,fun k => ?_⟩
          erw [finiteChild_one,Functor.map_id_apply]
          congr 1
          exact (Fin.eq_zero k).symm
      | succ n =>
          obtain ⟨a,ha⟩ := ih (fun k => xs k.castSucc)
          obtain ⟨z,hz₁,hz₂⟩ := modelProduct_exists T M (finitePower X (n + 1)) X
            a (xs (Fin.last (n + 1)))
          refine ⟨z,fun k => ?_⟩
          refine Fin.lastCases ?_ (fun j => ?_) k
          · rw [finiteChild_last]
            exact hz₂
          · erw [finiteChild_castSucc,Functor.map_comp_apply]
            exact (congrArg ((F T M).map (finiteChild T X (n + 1) j)) hz₁).trans (ha j)

/-- The real ordered premise projections detect equality of power
points, uniformly in the model. -/
theorem powerPoints_ext (X : PredicateCategory T) (n : ℕ)
    {x y : Obj T M (finitePower X n)}
    (h : ∀ k : Fin n, (F T M).map (finiteChild T X n k) x =
      (F T M).map (finiteChild T X n k) y) : x = y := by
  induction n with
  | zero => exact SyntacticDerivation.modelTerminal_ext T M x y
  | succ n ih =>
      cases n with
      | zero =>
          have he := h 0
          erw [finiteChild_one,Functor.map_id_apply,Functor.map_id_apply] at he
          exact he
      | succ n =>
          apply modelProduct_ext T M
          · apply ih
            intro k
            exact (finiteChild_castSucc_point T M X n k x).symm.trans
              ((h k.castSucc).trans (finiteChild_castSucc_point T M X n k y))
          · have he := h (Fin.last (n + 1))
            erw [finiteChild_last] at he
            exact he

end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
