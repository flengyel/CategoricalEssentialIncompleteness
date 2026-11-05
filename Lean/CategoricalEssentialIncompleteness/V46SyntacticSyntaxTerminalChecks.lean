/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTerminal

/-! # Exact terminal-parameter reflection in the manuscript category context -/

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

example {C : Type u} [Category.{v} C] [HasFiniteLimits C] :
    (terminalCFEquivalence (C := C)).functor = constantFamilyFunctor (⊤_ C) := rfl

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

example (p : SyntaxPolynomial D) (X : D × D) :
    IsIso (SyntaxPolynomial.parameterComparison (⊤_ D) X p) :=
  terminalParameterComparison_isIso X p

example (p : SyntaxPolynomial D) (X : D × D) :
    (terminalPolynomialIso p).inv.app X =
      SyntaxPolynomial.parameterComparison (⊤_ D) X p := rfl

example (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (h : IsInitial (SyntaxPolynomial.algebraWithParameters p q A (⊤_ D))) : IsInitial A :=
  initialOfTerminalParameters p q A h
