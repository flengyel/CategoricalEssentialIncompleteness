/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionValues


/-! # Complete option points and success of the substitution morphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionValuesChecks
open NamedProofImage.NativeSubstitution
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula
  (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example : Function.Bijective (optionPoint P σ π d) :=
  ⟨optionPoint_injective P σ π d,optionPoint_surjective P σ π d⟩

example (φ : Fm) : optionPoint P σ π d none ≠ optionPoint P σ π d (some φ) :=
  optionPoint_none_ne_some P σ π d φ

example (v : Option Fm) : decodeOption P σ π d (optionPoint P σ π d v)=v :=
  decode_optionPoint P σ π d v

example (q : (U).obj (OptionSyntax.obj (S).algebra.a.2)) :
    optionPoint P σ π d (decodeOption P σ π d q)=q := optionPoint_decode P σ π d q

example (x : ℕ) :
    (U).map (S).variableConstructor (Points.namePoint P x)=NamedProofImage.termPoint P σ π d (.var x) :=
  variable_point P σ π d x

example (x : ℕ) (r : Tm) :
    termValue P σ π d x (.var x) r=NamedProofImage.termPoint P σ π d r := identity_term P σ π d x r

example (x : ℕ) (φ : Fm) :
    formulaOptionValue P σ π d x (.var x) φ=optionPoint P σ π d (some φ) :=
  identity_option P σ π d x φ

example (x : ℕ) (t : Tm) (φ : Fm) (v : Option Fm) :
    (optionPoint P σ π d v).val∈Total.val (S).formulaSubstitutionOption.hom
      (formulaInput P σ π d x t φ).val ↔ decodedResult P σ π d x t φ=v :=
  option_graph P σ π d x t φ v

example (x : ℕ) (t : Tm) (φ ψ : Fm) :
    (∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) ↔
        decodedResult P σ π d x t φ=some ψ := success_iff P σ π d x t φ ψ

example (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t φ=none ↔
      ¬ ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t :=
  failure_iff P σ π d x t φ


end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionValuesChecks
