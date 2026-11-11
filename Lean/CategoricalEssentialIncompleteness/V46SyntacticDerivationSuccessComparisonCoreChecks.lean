/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessComparisonCore

/-! The comparison follows from actual conservative interpretations and computed premise equality. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {J : Type w} (K : D ⥤ (Discrete J ⥤ Type)) [K.ReflectsIsomorphisms]
  [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K]
  {F : D} {N : ℕ} (R : RulePresentation F N)
  (E : ∀ i : Fin (N + 1), DecidableVariables (finitePower F i.val))
example : SliceInitial.functor (PolynomialComparison.ordinary R) (SuccessComparisonCore.validator R E) ⋙
    SuccessComparisonCore.success (F := F) ≅
      SuccessComparisonCore.success (F := F) ⋙ R.inference :=
  SuccessComparisonCore.comparison K R E
