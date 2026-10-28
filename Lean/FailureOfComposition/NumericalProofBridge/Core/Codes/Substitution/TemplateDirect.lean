/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.DirectEquality

/-! # The fixed equality template and its direct closed instance -/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

theorem equalitySentenceTemplate_subst_eq_direct (q r : ℕ) :
    (equalitySentenceTemplate/[
      (↑q : ArithmeticSemiterm Empty 0),
      (↑r : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      directEqualitySentence q r := by
  have hleft :
      ((Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 0),
        (↑r : ArithmeticSemiterm Empty 0)]).q.q).comp
          (Rew.subst ![
            (#2 : ArithmeticSemiterm Empty 4),
            (#1 : ArithmeticSemiterm Empty 4),
            (#0 : ArithmeticSemiterm Empty 4)]) =
        Rew.subst ![
          (↑q : ArithmeticSemiterm Empty 2),
          (#1 : ArithmeticSemiterm Empty 2),
          (#0 : ArithmeticSemiterm Empty 2)] := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  have hright :
      ((Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 0),
        (↑r : ArithmeticSemiterm Empty 0)]).q.q.q).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 5),
            (#4 : ArithmeticSemiterm Empty 5),
            (#2 : ArithmeticSemiterm Empty 5),
            (#1 : ArithmeticSemiterm Empty 5)]) =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 3),
          (↑r : ArithmeticSemiterm Empty 3),
          (#2 : ArithmeticSemiterm Empty 3),
          (#1 : ArithmeticSemiterm Empty 3)] := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  simp only [equalitySentenceTemplate, directEqualitySentence,
    Rewriting.app_all, equalityLeftBody, equalityRightOpen]
  rw [LogicalConnective.HomClass.map_iff, Rewriting.app_exs]
  rw [← TransitiveRewriting.comp_app,
    ← TransitiveRewriting.comp_app]
  rw [hleft, hright]

end FailureOfComposition.NumericalProofBridge
