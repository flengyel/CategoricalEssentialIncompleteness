/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PropositionalRuleComparison
public import CategoricalEssentialIncompleteness.V46SliceEvaluationSubobjects

/-! # Propositional closure for constant families and evaluation at a theorem point -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PropositionalClosureTransfer
open PropositionalRuleComparison
open PropositionalSchemeTransport (implication ternaryComparison)
open RetractedRuleComparison (productBackward)

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Regular C] [Regular D] [FinitaryExtensive C] [FinitaryExtensive D]
  (B : C ⥤ D) [PreservesFiniteLimits B] {S : C} (n : S ⟶ S) (i : S ⨯ S ⟶ S)
  (P : Proofs n i) (hP : ∀ A, IsInitial (P A))
  (Q : Proofs (B.map n) (implication B i)) (hQ : ∀ W, IsInitial (Q W))

local instance ternaryIso : IsIso (ternaryComparison B S) := by
  unfold ternaryComparison
  infer_instance

include hQ in
theorem forward_closed (A : Subobject S) (hA : generated n i P A = A) :
    generated (B.map n) (implication B i) Q (FiniteLimitSubobjects.object B A) =
      FiniteLimitSubobjects.object B A := by
  let W := FiniteLimitSubobjects.object B A
  let c := prodComparison B S S
  let τ := translation n i B (B.map n) (implication B i) (𝟙 _) (inv c)
    (inv (ternaryComparison B S))
    (by rw [PropositionalSchemeTransport.one, Category.comp_id, IsIso.inv_hom_id_assoc])
    (by rw [PropositionalSchemeTransport.two, Category.comp_id, IsIso.inv_hom_id_assoc])
    (by rw [PropositionalSchemeTransport.three, Category.comp_id, IsIso.inv_hom_id_assoc])
    A W (Subobject.underlyingIso (B.map A.arrow)).hom
    (by rw [Subobject.underlyingIso_hom_comp_eq_mk, Category.comp_id]; rfl)
    (by rw [Category.comp_id]; exact inv_prodComparison_map_fst B)
    (Category.comp_id _).symm
    (by rw [Category.comp_id]; exact inv_prodComparison_map_snd B)
  apply le_antisymm _ (extensive _ _ _ _)
  have h := generated_le n i B (B.map n) (implication B i) A W P Q hQ τ
  change generated _ _ Q W ≤ (Subobject.pullback (𝟙 _)).obj
    (FiniteLimitSubobjects.object B (generated n i P A)) at h
  rwa [Subobject.pullback_id, hA] at h

variable (E : D ⥤ C) [PreservesFiniteLimits E] (e : B ⋙ E ≅ 𝟭 C)

include hP in
theorem backward_closed (W : Subobject (B.obj S))
    (hW : generated (B.map n) (implication B i) Q W = W) :
    let A := RetractedClosedTheories.backObject B E e W
    generated n i P A = A := by
  let A := RetractedClosedTheories.backObject B E e W
  let p := productBackward B E e S S
  let q := e.inv.app (Triple S) ≫ E.map (ternaryComparison B S)
  let τ := translation (B.map n) (implication B i) E n i (e.inv.app S) p q
    (by
      dsimp only [p, productBackward]
      rw [Category.assoc, ← E.map_comp, ← PropositionalSchemeTransport.one]
      exact (e.inv.naturality _).symm)
    (by
      dsimp only [q]
      rw [Category.assoc, ← E.map_comp, ← PropositionalSchemeTransport.two]
      exact (e.inv.naturality _).symm)
    (by
      dsimp only [p, productBackward]
      rw [Category.assoc, ← E.map_comp, ← PropositionalSchemeTransport.three]
      exact (e.inv.naturality _).symm)
    W A (RetractedClosedTheories.axiomMap B E e W) (RetractedClosedTheories.axiomMap_law B E e W)
    (RetractedRuleComparison.productBackward_fst B E e S S)
    (RetractedRuleComparison.productBackward_operation B E e i)
    (RetractedRuleComparison.productBackward_snd B E e S S)
  apply le_antisymm _ (extensive n i P _)
  have h := generated_le (B.map n) (implication B i) E n i W A Q P hP τ
  change generated n i P A ≤ (Subobject.pullback (e.inv.app S)).obj
    (FiniteLimitSubobjects.object E (generated _ _ Q W)) at h
  rw [hW] at h
  exact h

section Slice
variable (U : C) {Z : C} (z : Z ⟶ U) (hZ : IsTerminal Z)
local notation "Bᵤ" => constantFamilyFunctor U
local instance : Regular (Over U) := RegularSlices.regular U
local instance : FinitaryExtensive (Over U) := RegularSlices.finitaryExtensive U
local instance : PreservesFiniteLimits (Bᵤ) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
local instance : PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation z hZ) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits z hZ

abbrev SliceProofs := Proofs ((Bᵤ).map n) (implication (Bᵤ) i)
variable (R : SliceProofs n i U) (hR : ∀ W, IsInitial (R W))

def constantTheory (T : Theory n i P) : Theory ((Bᵤ).map n) (implication (Bᵤ) i) R :=
  ⟨FiniteLimitSubobjects.object (Bᵤ) T.val, forward_closed (Bᵤ) n i P R hR T.val T.property⟩

def evaluationTheory (W : Theory ((Bᵤ).map n) (implication (Bᵤ) i) R) : Theory n i P := by
  refine ⟨SliceSubobjectPredicates.evaluate z hZ W.val, ?_⟩
  rw [SliceSubobjectPredicates.evaluate_eq_retraction]
  exact backward_closed (Bᵤ) n i P hP R (SliceBaseChangeGeometry.evaluation z hZ)
    (SliceBaseChangeGeometry.ordinaryRetraction z hZ) W.val W.property
end Slice
end CategoricalEssentialIncompleteness.V46.PropositionalClosureTransfer
