/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparison


/-! # Constructor-preserving comparison with the original named PA syntax -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
local notation "p" => Syntax.Polynomial.mapped P a
local notation "q" => Syntax.Polynomial.mapped P b
example : Syntax.Raw.wordAlgebra p q ≅ Syntax.Polynomial.mappedAlgebra P a b
    (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b) := NamedSyntaxComparison.wordAlgebraIso P a b
example : (NamedSyntaxComparison.wordAlgebraIso P a b).hom.f=
    (NamedSyntaxComparison.plainPairIso P a b).hom := NamedSyntaxComparison.wordAlgebraIso_f P a b
example : (NamedSyntaxComparison.wordAlgebraIso P a b).inv.f=
    (NamedSyntaxComparison.plainPairIso P a b).inv := NamedSyntaxComparison.wordAlgebraIso_inverse_f P a b
example : (SyntaxPolynomial.jointFunctor p q).map (NamedSyntaxComparison.wordAlgebraIso P a b).hom.f ≫
    (Syntax.Polynomial.mappedAlgebra P a b (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b)).str=
      (Syntax.Raw.wordAlgebra p q).str ≫ (NamedSyntaxComparison.wordAlgebraIso P a b).hom.f :=
  (NamedSyntaxComparison.wordAlgebraIso P a b).hom.h
example : IsInitial (Syntax.Polynomial.mappedAlgebra P a b (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b)) :=
  NamedSyntaxComparison.mappedPlainInitial P a b
example (R : Total.TotalCategory P) : IsInitial (SyntaxPolynomial.algebraWithParameters p q
    (Syntax.Polynomial.mappedAlgebra P a b (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b)) R) :=
  NamedSyntaxComparison.mappedPlainWithParametersInitial P a b R
example (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b)) :
    (NamedSyntaxComparison.wordAlgebraIso P a b).hom ≫ NamedSyntaxComparison.mappedHom P a b
        ((SyntacticSyntax.plainPostfixInitial 𝗣𝗔 a b).to B)=
      (Syntax.Raw.wordInitial p q).to (Syntax.Polynomial.mappedAlgebra P a b B) :=
  NamedSyntaxComparison.mapped_fold P a b B
