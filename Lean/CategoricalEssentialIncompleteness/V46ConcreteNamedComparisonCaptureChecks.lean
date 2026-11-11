/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCapture


/-! # Statement checks in `V46ConcreteNamedComparisonCaptureChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CaptureChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedComparisonCaptureChecksDecidableEq : DecidableEq M :=
  namedComparisonCaptureModelDecidableEq M
example {X : PredicateCategory T} (V : PredicateCategory T)
    (x y : X ⟶ V) (body replacement : X ⟶ listObject T V) (q : Obj T M X) :
    (F T M).map (absenceOr T V x y body replacement) q =
      (F T M).map (Two.constant X
        (if ConcreteNamedSubstitution.member ((F T M).map x q).val ((F T M).map body q).val = 0 ∨
          ConcreteNamedSubstitution.member ((F T M).map y q).val ((F T M).map replacement q).val = 0
          then true else false)) q := absenceOr_point T M V x y body replacement q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CaptureChecks
