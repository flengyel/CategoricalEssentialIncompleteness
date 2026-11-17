/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46InitialRuleDiagrams
public import CategoricalEssentialIncompleteness.V46NumericalDerivation
public import CategoricalEssentialIncompleteness.V46SliceInference

/-! # Initial finite derivations in numerical diagrams and all parameter slices -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalDiagramDerivations
variable {J : Type u} [Category.{v} J] [Regular (J ⥤ NumericalTuples.Object)]
variable {F : J ⥤ NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)

irreducible_def componentAlgebra (j : J) : Endofunctor.Algebra (InitialRuleDiagrams.rules R j).inference :=
  NumericalDerivation.derivationAlgebra (InitialRuleDiagrams.rules R j)

def componentInitial (j : J) : IsInitial (componentAlgebra R j) := by
  rw [componentAlgebra_def]
  exact NumericalDerivation.derivationInitial (InitialRuleDiagrams.rules R j)

/-- All finite rule labels are arbitrary numerical diagrams. The
constructor and its transition squares are constructed from initial folds. -/
def algebra : Endofunctor.Algebra R.inference :=
  InitialRuleDiagrams.algebra R (componentAlgebra R) (componentInitial R)

def initial : IsInitial (algebra R) :=
  InitialRuleDiagrams.initial R (componentAlgebra R) (componentInitial R)

def componentIso (j : J) :
    FiniteInferenceEvaluation.algebra (InitialRuleDiagrams.evaluation j) R (algebra R) ≅
      componentAlgebra R j :=
  InitialRuleDiagrams.sourceIso R (componentAlgebra R) (componentInitial R) j

def fold (B : Endofunctor.Algebra R.inference) : algebra R ⟶ B := (initial R).to B

theorem fold_conclusion (B : Endofunctor.Algebra R.inference) :
    (fold R B).f.left ≫ B.a.hom = (algebra R).a.hom := Over.w _

theorem fold_constructor (B : Endofunctor.Algebra R.inference) :
    R.inference.map (fold R B).f ≫ B.str = (algebra R).str ≫ (fold R B).f := (fold R B).h

theorem fold_underlying_unique (B : Endofunctor.Algebra R.inference)
    (m : (algebra R).a.left ⟶ B.a.left) (hm : m ≫ B.a.hom = (algebra R).a.hom)
    (hc : R.inference.map (Over.homMk m hm) ≫ B.str = (algebra R).str ≫ Over.homMk m hm) :
    m = (fold R B).f.left :=
  congrArg (fun n => n.f.left) ((initial R).hom_ext (⟨Over.homMk m hm, hc⟩ : algebra R ⟶ B) _)

namespace Parameterized
variable {P : J ⥤ NumericalTuples.Object}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- Flattening the iterated slice retains the common parameter in every
premise; the original relative inference functor is recovered by equivalence. -/
def algebra : Endofunctor.Algebra R.inference :=
  SliceInference.algebra R (NumericalDiagramDerivations.algebra (SliceRuleObjects.rules R))

def initial : IsInitial (algebra R) :=
  SliceInference.initial R _ (NumericalDiagramDerivations.initial (SliceRuleObjects.rules R))
end Parameterized
end CategoricalEssentialIncompleteness.V46.NumericalDiagramDerivations
