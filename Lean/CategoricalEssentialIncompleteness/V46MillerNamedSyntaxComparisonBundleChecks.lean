/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonBundle


/-! # The explicitly presented named signature and its canonical push -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
example : CategoricalSyntax ((Syntax.predicateFunctor P).obj V)
    (fun n => (Syntax.predicateFunctor P).obj (σ n)) (fun n => (Syntax.predicateFunctor P).obj (π n)) d :=
  NamedSyntaxComparison.presentedSyntax P V σ π d
example : (NamedSyntaxComparison.presentedSyntax P V σ π d).algebra ≅
    NamedSyntaxComparison.sourceMappedAlgebra P V σ π d := NamedSyntaxComparison.sourceAlgebraIso P V σ π d
example (R : Total.TotalCategory P) : IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression ((Syntax.predicateFunctor P).obj V) (fun n => (Syntax.predicateFunctor P).obj (σ n)) d)
    (SyntaxPolynomial.formulaExpression ((Syntax.predicateFunctor P).obj V) (fun n => (Syntax.predicateFunctor P).obj (π n)) d)
    (NamedSyntaxComparison.presentedSyntax P V σ π d).algebra R) :=
  (NamedSyntaxComparison.presentedSyntax P V σ π d).stable R
example (z : Point) : CategoricalSyntax
    ((Total.pointPresentation z).functor.obj ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj V))
    (fun n => (Total.pointPresentation z).functor.obj ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj (σ n)))
    (fun n => (Total.pointPresentation z).functor.obj ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj (π n))) d :=
  NamedSyntaxComparison.canonicalPresentedSyntax z V σ π d
