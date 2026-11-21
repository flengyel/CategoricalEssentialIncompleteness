/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionTransport


/-! # The numerical absent-variable fiber under the literal equivalence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionTransport.Checks
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => NumericalNamed.literalEquivalence
local notation "S₀" => NumericalNamed.literalSourceSyntax V σ π d
local notation "S₁" => NumericalNamed.literalCategoricalSyntax V σ π d
example : (E).functor.obj (S₀).distributionParameters ≅ (S₁).distributionParameters :=
  fiberIso (E) V σ π d (S₀) (S₁)
    (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)
example :
    (fiberIso (E) V σ π d (S₀) (S₁)
      (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)).hom ≫
        (S₁).distributionInclusion =
      (E).functor.map (S₀).distributionInclusion ≫
        (baseIso (E) V σ π d (S₀) (S₁) (NumericalNamed.literalAlgebraIso V σ π d)).hom :=
  fiberIso_inclusion (E) V σ π d (S₀) (S₁)
    (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionTransport.Checks
