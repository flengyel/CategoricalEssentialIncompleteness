/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonLists


/-! # The list comparison for a PA-described coefficient predicate -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (C : PredicateCategory 𝗣𝗔)
example : Lists.object ((Syntax.predicateFunctor P).obj C).obj ≅
    (Syntax.predicateFunctor P).obj (SyntacticLists.listObject 𝗣𝗔 C) := NamedSyntaxComparison.listIso P C
example (word output : ℕ) : output∈Total.val (NamedSyntaxComparison.listIso P C).hom.hom word ↔
    word∈(Lists.carrier ((Syntax.predicateFunctor P).obj C).obj).support ∧ output=word :=
  NamedSyntaxComparison.listIso_graph P C word output
example : (Lists.algebra ((Syntax.predicateFunctor P).obj C).obj).nil ≫
    (NamedSyntaxComparison.listIso P C).hom=(NamedSyntaxComparison.mappedListAlgebra P C).nil :=
  NamedSyntaxComparison.list_nil_comparison P C
example : (Lists.algebra ((Syntax.predicateFunctor P).obj C).obj).cons ≫
    (NamedSyntaxComparison.listIso P C).hom=
      prod.map (𝟙 ((Syntax.predicateFunctor P).obj C)) (NamedSyntaxComparison.listIso P C).hom ≫
        (NamedSyntaxComparison.mappedListAlgebra P C).cons := NamedSyntaxComparison.list_cons_comparison P C
example : (Lists.algebra ((Syntax.predicateFunctor P).obj C).obj).asAlgebra ≅
    (NamedSyntaxComparison.mappedListAlgebra P C).asAlgebra := NamedSyntaxComparison.listAlgebraIso P C
example (R : Total.TotalCategory P) : IsInitial ((NamedSyntaxComparison.mappedListAlgebra P C).withParameters R).asAlgebra :=
  (NamedSyntaxComparison.mappedListStable P C).stable R
