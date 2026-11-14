/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedClosedTheories
public import CategoricalEssentialIncompleteness.V46AssociatedExtensionWitness

/-! # Manuscript v58 Theorem 5.3: incompleteness in an associated category -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AssociatedCategory

section Reduction
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (P : FirstOrderPresentation V)
variable (a b : Subobject X) (hab : SubobjectInseparable a b)
variable (θ : X ⟶ P.syntaxData.sentenceObject) (t : Subobject P.syntaxData.sentenceObject)
variable (ha : a ≤ (Subobject.pullback θ).obj t)
variable (hb : b ≤ (Subobject.pullback θ).obj
  ((Subobject.pullback P.syntaxData.sentenceNegation).obj t))

include hab ha hb in
theorem essential_incomplete_of_reduction (U : P.Theories) (htU : t ≤ U.val)
    (hcU : P.Consistent U.val) : P.EssentiallyIncomplete U := by
  refine ⟨hcU, ?_⟩
  intro W hUW hcW hcompW
  have hi := extension_inseparable a b hab θ P.syntaxData.sentenceNegation t W.val
    ha hb (htU.trans hUW) hcW
  exact hi.2 ⟨⟨W.val, (Subobject.pullback P.syntaxData.sentenceNegation).obj W.val,
    ⟨disjoint_iff.mpr hcW, codisjoint_iff.mpr hcompW⟩⟩, le_rfl, le_rfl⟩
end Reduction

open RestrictionSubobjects AssociatedClosedTheories
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
variable (inverses : MonoInverses C) {V Z : Tot C} (P : FirstOrderPresentation V)
variable (Q : (U : Tot C) → AssociatedClosedTheories.SliceProofs P U)
variable (hQ : ∀ U W, IsInitial (Q U W))
variable (logicalTheorem : Z ⟶ P.syntaxData.sentenceObject) (hZ : IsTerminal Z)
variable (factors : ∀ U : P.Theories, P.Consistent U.val →
  ∃ point : Z ⟶ (U.val : Tot C), point ≫ U.val.arrow = logicalTheorem)

include hQ factors hZ in
/-- The full equivalence quantifies over all closed slice extensions.
The displayed Boolean conclusions use the actual partial-slice functor. -/
theorem associated_incompleteness (U : P.Theories) (hcU : P.Consistent U.val) :
    (P.EssentiallyIncomplete U ↔
      AssociatedClosedTheories.EssentiallyIncomplete P (U.val : Tot C) (Q (U.val : Tot C))
        (constantTheory P (U.val : Tot C) (Q (U.val : Tot C)) (hQ (U.val : Tot C)) U)) ∧
    (¬ P.Complete U.val ↔
      ¬ isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
        (theoryDecision inverses P U.val hcU))) ∧
    (SubobjectInseparable U.val ((Subobject.pullback P.syntaxData.sentenceNegation).obj U.val) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
          (theoryDecision inverses P U.val hcU))) := by
  obtain ⟨point, _⟩ := factors U hcU
  exact ⟨essential_incomplete_iff P (U.val : Tot C) (Q (U.val : Tot C))
      (hQ (U.val : Tot C)) point hZ U hcU,
    incomplete_iff_decision_not_total inverses P U.val hcU point hZ,
    subobject_inseparable_iff_no_total_extension inverses P U.val hcU point hZ⟩

include hQ factors hZ in
/-- The final clause holds for every consistent closed extension of the
theory receiving the reduction, together with its total-extension obstruction. -/
theorem associated_reduction {X : Tot C} (a b : Subobject X) (hab : SubobjectInseparable a b)
    (θ : X ⟶ P.syntaxData.sentenceObject) (t : Subobject P.syntaxData.sentenceObject)
    (ha : a ≤ (Subobject.pullback θ).obj t)
    (hb : b ≤ (Subobject.pullback θ).obj
      ((Subobject.pullback P.syntaxData.sentenceNegation).obj t))
    (U : P.Theories) (htU : t ≤ U.val) (hcU : P.Consistent U.val) :
    AssociatedClosedTheories.EssentiallyIncomplete P (U.val : Tot C) (Q (U.val : Tot C))
        (constantTheory P (U.val : Tot C) (Q (U.val : Tot C)) (hQ (U.val : Tot C)) U) ∧
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
          (theoryDecision inverses P U.val hcU)) := by
  obtain ⟨point, _⟩ := factors U hcU
  exact ⟨(essential_incomplete_iff P (U.val : Tot C) (Q (U.val : Tot C))
      (hQ (U.val : Tot C)) point hZ U hcU).mp
        (essential_incomplete_of_reduction P a b hab θ t ha hb U htU hcU),
    no_total_extension_of_reduction inverses P a b hab θ t U.val ha hb point hZ htU hcU⟩

end CategoricalEssentialIncompleteness.V46.AssociatedCategory
