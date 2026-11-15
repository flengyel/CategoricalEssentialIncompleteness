/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceInference
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTotal

/-! # Constructed initial deduction algebras in every total syntactic slice -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticSliceDerivations
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {P : TotalSplit T}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- Rule labels may be arbitrary families over P. Their original label,
premise and conclusion morphisms define the underlying arithmetic rules. -/
def algebra : Endofunctor.Algebra R.inference :=
  SliceInference.algebra R
    (SyntacticDerivation.totalDerivationAlgebra T (SliceRuleObjects.rules R))

/-- The universal property quantifies over every slice-algebra morphism.
No choice of evaluator or initiality conclusion is an input hypothesis. -/
def initial : IsInitial (algebra T R) :=
  SliceInference.initial R _
    (SyntacticDerivation.totalDerivationInitial T (SliceRuleObjects.rules R))

def fold (B : Endofunctor.Algebra R.inference) : algebra T R ⟶ B :=
  (initial T R).to B

theorem fold_unique (B : Endofunctor.Algebra R.inference) (f : algebra T R ⟶ B) :
    f = fold T R B := (initial T R).hom_ext _ _

end CategoricalEssentialIncompleteness.V46.SyntacticSliceDerivations
