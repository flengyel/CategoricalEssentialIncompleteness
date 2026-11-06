/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonResults
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOriginal

/-! # The computed state pair preserves originals before the fold comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => categoricalSyntax T V σ π d
local notation "A" => projectionSourceAlgebra T V V σ π d
local notation "K" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.withParameters
    (CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)) (SyntaxPolynomial.termExpression V σ d))
  (SyntaxPolynomial.withParameters
    (CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)) (SyntaxPolynomial.formulaExpression V π d))

/-- This is only the actual pair of typed state arrows. Its algebra
commutation is a separate result to be proved from all constructor cases. -/
def computedStatePair : (A).a ⟶ (S).substitutionAlgebra.a :=
  (computedTermState T V V σ π d,computedFormulaState T V V σ π d)

theorem computedStatePair_original_projection :
    computedStatePair T V σ π d ≫ (S).substitutionOriginalHom.f = originalProjectionPair T V V σ π d := by
  apply Prod.ext
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [computedStatePair,computedTermState,CategoricalSyntax.substitutionOriginalHom,
        originalProjectionPair,payloadProjectionFamily,constantFamilyFunctor]
    all_goals first
      | erw [Category.comp_id,prod.lift_fst]
      | erw [prod.lift_fst,prod.lift_snd]
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [computedStatePair,computedFormulaState,CategoricalSyntax.substitutionOriginalHom,
        originalProjectionPair,payloadProjectionFamily,constantFamilyFunctor]
    all_goals first
      | erw [Category.comp_id,prod.lift_fst]
      | erw [prod.lift_fst,prod.lift_snd]

theorem computedStatePair_original :
    computedStatePair T V σ π d ≫ (S).substitutionOriginalHom.f = 𝟙 (A).a := by
  rw [computedStatePair_original_projection,originalProjectionPair_eq_id T V V σ π d]

/-- The original components of the required commutation square already
commute. This is derived from the actual generic original-projection
Hom and the proved metadata identity, not from the missing full square. -/
theorem computedStatePair_original_commutes :
    ((K).map (computedStatePair T V σ π d) ≫ (S).substitutionAlgebra.str) ≫
      (S).substitutionOriginalHom.f =
    ((A).str ≫ computedStatePair T V σ π d) ≫ (S).substitutionOriginalHom.f := by
  rw [Category.assoc,← (S).substitutionOriginalHom.h,← Category.assoc,← Functor.map_comp,
    computedStatePair_original T V σ π d]
  erw [CategoryTheory.Functor.map_id,Category.id_comp,
    Category.assoc,computedStatePair_original T V σ π d,Category.comp_id]
  all_goals rfl

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
