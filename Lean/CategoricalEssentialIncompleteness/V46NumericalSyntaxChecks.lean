/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalSyntax


/-! # Statement checks in `V46NumericalSyntaxChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46

example : SyntacticPredicates.PredicateCategory 𝗧𝗔 ≌ NumericalTuples.Object :=
  NumericalSyntax.predicateEquivalence

example (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ) :
    CategoricalSyntax V σ π d := NumericalSyntax.categoricalSyntax V σ π d

example (V P : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (NumericalSyntax.categoricalSyntax V σ π d).algebra P) :=
  (NumericalSyntax.categoricalSyntax V σ π d).stable P

example (R : ℕ → NumericalTuples.Object) (N : ℕ) :
    IsInitial (NumericalSyntax.oneSortAlgebra R N) := NumericalSyntax.oneSortInitial R N

example (V P : NumericalTuples.Object) :
    IsInitial ((NumericalSyntax.categoricalSyntax V (fun _ => V) (fun _ => V) 0).lists.algebra.withParameters P).asAlgebra :=
  (NumericalSyntax.categoricalSyntax V (fun _ => V) (fun _ => V) 0).lists.stable P
