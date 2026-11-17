/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PropositionalClosureTransfer
public import CategoricalEssentialIncompleteness.V46AssociatedExtensionWitness
public import CategoricalEssentialIncompleteness.V46SliceInseparability

/-! # The standalone propositional case of Theorem 5.3 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.PropositionalAssociatedIncompleteness
open PropositionalRuleComparison PropositionalClosureTransfer
open PropositionalSchemeTransport (implication)

section Transfer
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {S : D} (n : S ⟶ S) (i : S ⨯ S ⟶ S) (P : Proofs n i) (hP : ∀ A, IsInitial (P A))

def Consistent (T : Subobject S) := T ⊓ (Subobject.pullback n).obj T = ⊥
def Complete (T : Subobject S) := T ⊔ (Subobject.pullback n).obj T = ⊤
def EssentiallyIncomplete (T : Theory n i P) : Prop :=
  Consistent n T.val ∧ ∀ W : Theory n i P, T.val ≤ W.val → Consistent n W.val → ¬ Complete n W.val

variable (U : D) (Q : SliceProofs n i U) (hQ : ∀ W, IsInitial (Q W))
local notation "Bᵤ" => constantFamilyFunctor U
local instance : Regular (Over U) := RegularSlices.regular U
local instance : FinitaryExtensive (Over U) := RegularSlices.finitaryExtensive U
local instance : PreservesFiniteLimits (Bᵤ) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U

variable {Z : D} (z : Z ⟶ U) (hZ : IsTerminal Z)

include hP z hZ in
theorem essential_iff (T : Theory n i P) (hc : Consistent n T.val) :
    EssentiallyIncomplete n i P T ↔ EssentiallyIncomplete ((Bᵤ).map n) (implication (Bᵤ) i) Q
      (constantTheory n i P U Q hQ T) := by
  constructor
  · intro h
    refine ⟨SliceSubobjectPredicates.constant_consistency U n T.val hc, ?_⟩
    intro W hTW hcW hdW
    let W₀ := evaluationTheory n i P hP U z hZ Q W
    have hb := SliceSubobjectPredicates.evaluate_monotone z hZ hTW
    change SliceSubobjectPredicates.evaluate z hZ
      (FiniteLimitSubobjects.object (Bᵤ) T.val) ≤ W₀.val at hb
    rw [SliceSubobjectPredicates.evaluate_constant] at hb
    exact h.2 W₀ hb (SliceSubobjectPredicates.evaluate_consistency z hZ n W.val hcW)
      (SliceSubobjectPredicates.evaluate_completeness z hZ n W.val hdW)
  · intro h
    refine ⟨hc, ?_⟩
    intro W hTW hcW hdW
    exact h.2 (constantTheory n i P U Q hQ W)
      (FiniteLimitSubobjects.object_monotone (Bᵤ) hTW)
      (SliceSubobjectPredicates.constant_consistency U n W.val hcW)
      (SliceSubobjectPredicates.constant_completeness U n W.val hdW)
end Transfer

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
  [Regular (Tot C)] [FinitaryExtensive (Tot C)] (m : MonoInverses C) {S Z : Tot C}
  (n : S ⟶ S) (i : S ⨯ S ⟶ S)
  (P : Proofs n i) (hP : ∀ A, IsInitial (P A))
  (Q : (U : Tot C) → SliceProofs n i U) (hQ : ∀ U W, IsInitial (Q U W))
  (logicalTheorem : Z ⟶ S) (hZ : IsTerminal Z)
  (factors : ∀ U : Theory n i P, Consistent n U.val →
    ∃ point : Z ⟶ (U.val : Tot C), point ≫ U.val.arrow = logicalTheorem)

local instance (U : Tot C) : Regular (Over U) := RegularSlices.regular U
local instance (U : Tot C) : FinitaryExtensive (Over U) := RegularSlices.finitaryExtensive U
local instance (U : Tot C) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U

variable (U : Theory n i P) (hc : Consistent n U.val)
local notation "Bᵤ" => constantFamilyFunctor (U.val : Tot C)

def familyDecision :=
  (PartialSliceTheoryFamilies.constantFunctor m (U.val : Tot C)).map
    (BooleanPartialDecision.decision m U.val ((Subobject.pullback n).obj U.val) hc)

include hP factors hZ in
theorem associated_incompleteness :
    (EssentiallyIncomplete n i P U ↔ EssentiallyIncomplete ((Bᵤ).map n)
      (implication (Bᵤ) i) (Q _) (constantTheory n i P _ (Q _) (hQ _) U)) ∧
    (¬ Complete n U.val ↔ ¬ isTotal (familyDecision m n i P U hc)) ∧
    (SubobjectInseparable U.val ((Subobject.pullback n).obj U.val) ↔
      ¬ RestrictionRetraction.HasTotalExtension (familyDecision m n i P U hc)) := by
  obtain ⟨z, _⟩ := factors U hc
  exact ⟨essential_iff n i P hP _ (Q _) (hQ _) z hZ U hc,
    (not_congr ((AssociatedCategory.constant_total_iff m z hZ _).trans
      (BooleanPartialDecision.total_iff m _ _ hc))).symm,
    (BooleanPartialDecision.inseparable_iff_noTotalExtension m _ _ hc).trans
      (AssociatedCategory.noTotalExtension_iff m z hZ _).symm⟩

include hP factors hZ in
theorem associated_reduction {X : Tot C} (a b : Subobject X) (hab : SubobjectInseparable a b)
    (θ : X ⟶ S) (t : Theory n i P) (ha : a ≤ (Subobject.pullback θ).obj t.val)
    (hb : b ≤ (Subobject.pullback θ).obj ((Subobject.pullback n).obj t.val)) (htU : t.val ≤ U.val) :
    EssentiallyIncomplete ((Bᵤ).map n) (implication (Bᵤ) i) (Q _)
      (constantTheory n i P _ (Q _) (hQ _) U) ∧
    ¬ RestrictionRetraction.HasTotalExtension (familyDecision m n i P U hc) := by
  have h := associated_incompleteness m n i P hP Q hQ logicalTheorem hZ factors U hc
  have hi := AssociatedCategory.extension_inseparable a b hab θ n t.val U.val ha hb htU hc
  exact ⟨h.1.mp ⟨hc, fun W hUW hcW => SliceInseparability.noncoverage n U.val hi W.val hUW hcW⟩,
    h.2.2.mp hi⟩

end CategoricalEssentialIncompleteness.V46.PropositionalAssociatedIncompleteness
