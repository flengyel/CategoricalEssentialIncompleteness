/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSource


/-! # Statement checks in `V46MillerNamedProofImageNativeSourceChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSourceChecks
open NamedProofImage.NativeSubstitution
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example (x : ℕ) (t r : Tm) :
    (N).map (S₀).termSubstitution (paTermInput σ π d x t r)=
      SyntacticNamedHilbert.termPoint σ π d (r.substitute x t) := pa_term_value σ π d x t r

example (x : ℕ) (t : Tm) (φ : Fm) :
    (N).map (S₀).formulaSubstitutionOption (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)=
      paOptionPoint σ π d (φ.substitute x t) := pa_formula_option_value σ π d x t φ

example : ConcreteNamedComparison.optionCode 𝗣𝗔 ℕ (S₀).algebra.a.2 (paOptionPoint σ π d none)=0 :=
  paOptionPoint_code σ π d none

example (x : ℕ) (t r : Tm) :
    paTermState σ π d x t r=SyntacticLists.pairPoint 𝗣𝗔 ℕ
      (SyntacticNamedHilbert.termPoint σ π d r) (SyntacticNamedHilbert.termPoint σ π d (r.substitute x t)) :=
  paTermState_native σ π d x t r

example (x : ℕ) (t : Tm) (φ : Fm) :
    paFormulaState σ π d x t φ=SyntacticLists.pairPoint 𝗣𝗔 ℕ
      (SyntacticNamedHilbert.formulaPoint σ π d φ) (paOptionPoint σ π d (φ.substitute x t)) :=
  paFormulaState_native σ π d x t φ

example (t : Tm) :
    (N).map (S₀).algebra.str.1 (Standard.realize (S₀).algebra.a
      (SyntaxPolynomial.termExpression (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ d)
      (paTermNodeData σ π d t))=SyntacticNamedHilbert.termPoint σ π d t := pa_term_node_base σ π d t

example (φ : Fm) :
    (N).map (S₀).algebra.str.2 (Standard.realize (S₀).algebra.a
      (SyntaxPolynomial.formulaExpression (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) π d)
      (paFormulaNodeData σ π d φ))=SyntacticNamedHilbert.formulaPoint σ π d φ := pa_formula_node_base σ π d φ

example (x : ℕ) (t : Tm) :
    (U).map (NamedSyntaxComparison.substitutionParameterIso P
      (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ π d).hom
      (NamedProofImage.sourcePoint P (S₀).substitutionParameters (paParameterPoint σ π d x t))=
        parameterPoint P σ π d x t := paParameterPoint_chart P σ π d x t

example (v : Option Fm) :
    (U).map (NamedSyntaxComparison.Options.optionIso (Syntax.predicateFunctor P)
      (NamedSyntaxComparison.formulaIso P (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ π d).symm).hom
      (NamedProofImage.sourcePoint P (OptionSyntax.obj (S₀).algebra.a.2) (paOptionPoint σ π d v))=
        optionPoint P σ π d v := paOptionPoint_chart P σ π d v

example (x : ℕ) (t r : Tm) :
    expectedTermState P σ π d x t r=Points.pairPoint (NamedProofImage.termPoint P σ π d r)
      (NamedProofImage.termPoint P σ π d (r.substitute x t)) := expectedTermState_native P σ π d x t r

example (x : ℕ) (t : Tm) (φ : Fm) :
    expectedFormulaState P σ π d x t φ=Points.pairPoint (NamedProofImage.formulaPoint P σ π d φ)
      (optionPoint P σ π d (φ.substitute x t)) := expectedFormulaState_native P σ π d x t φ

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSourceChecks
