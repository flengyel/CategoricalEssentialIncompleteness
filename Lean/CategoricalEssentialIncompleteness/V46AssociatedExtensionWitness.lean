/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedBooleanDecision

/-! # Total-extension obstructions for consistent theory extensions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AssociatedCategory

section Subobjects

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {X S : D} (a b : Subobject X) (hab : SubobjectInseparable a b)
variable (θ : X ⟶ S) (ν : S ⟶ S) (T U : Subobject S)
variable (ha : a ≤ (Subobject.pullback θ).obj T)
variable (hb : b ≤ (Subobject.pullback θ).obj ((Subobject.pullback ν).obj T))

include hab ha hb in
theorem extension_inseparable (hTU : T ≤ U)
    (hc : U ⊓ (Subobject.pullback ν).obj U = ⊥) :
    SubobjectInseparable U ((Subobject.pullback ν).obj U) := by
  refine ⟨hc, fun hs => hab.2 ?_⟩
  apply subobject_separator_mono
    (ha.trans ((Subobject.pullback θ).monotone hTU))
    (hb.trans ((Subobject.pullback θ).monotone ((Subobject.pullback ν).monotone hTU)))
  exact subobject_separator_pullback θ hs

end Subobjects

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
variable (inverses : MonoInverses C) {V X Z : Tot C} (P : FirstOrderPresentation V)
variable (a b : Subobject X) (hab : SubobjectInseparable a b)
variable (θ : X ⟶ P.syntaxData.sentenceObject) (T U : Subobject P.syntaxData.sentenceObject)
variable (ha : a ≤ (Subobject.pullback θ).obj T)
variable (hb : b ≤ (Subobject.pullback θ).obj
  ((Subobject.pullback P.syntaxData.sentenceNegation).obj T))
variable (point : Z ⟶ (U : Tot C)) (hZ : IsTerminal Z)

include hab ha hb point hZ in
theorem no_total_extension_of_reduction (hTU : T ≤ U) (hc : P.Consistent U) :
    ¬ RestrictionRetraction.HasTotalExtension
      ((PartialSliceTheoryFamilies.constantFunctor inverses (U : Tot C)).map
        (theoryDecision inverses P U hc)) :=
  (subobject_inseparable_iff_no_total_extension inverses P U hc point hZ).mp
    (extension_inseparable a b hab θ P.syntaxData.sentenceNegation T U ha hb hTU hc)

end CategoricalEssentialIncompleteness.V46.AssociatedCategory
