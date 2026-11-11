/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaSubstitutionComparison


/-! # Statement checks in `V46MillerNamedProofImageNativeFormulaSubstitutionComparisonChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeFormulaSubstitutionComparisonChecks
open NamedProofImage.NativeSubstitution
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example (x : ℕ) (t : Tm) (φ : Fm) :
    formulaState P σ π d x t φ=expectedFormulaState P σ π d x t φ :=
  formulaState_comparison P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    (Total.underlying (P := P)).map
      (CategoricalSyntax.formulaSubstitutionOption (NamedProofImage.syntaxData P σ π d))
      (Points.pairPoint (NamedProofImage.formulaPoint P σ π d φ)
        (Points.pairPoint (Points.namePoint P x) (NamedProofImage.termPoint P σ π d t)))=
      optionPoint P σ π d (φ.substitute x t) := formulaOptionValue_eq_native P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t φ=φ.substitute x t := decodedResult_eq_substitute P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) (v : Option Fm) :
    (optionPoint P σ π d v).val∈Total.val (S).formulaSubstitutionOption.hom
      (Points.substitutionPoint P σ π d x φ t).val ↔ φ.substitute x t=v :=
  native_option_graph P σ π d x t φ v

example (x : ℕ) (t : Tm) (φ ψ : Fm) (hs : φ.substitute x t=some ψ) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ :=
  native_substitution_instance P σ π d x t φ ψ hs

example (x : ℕ) (t : Tm) (φ ψ : Fm) (a : (U).obj (S).admissibleSubstitution)
    (hi : (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t)
    (hr : (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) :
    φ.FreeFor x t ∧ φ.substitute x t=some ψ := native_substitution_reflection P σ π d x t φ ψ a hi hr

example (x : ℕ) (t : Tm) (φ : Fm) :
    φ.FreeFor x t ↔ ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t :=
  native_freeFor_iff_success P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    φ.substitute x t=none ↔
      ¬ ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t :=
  native_failure_iff P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    formulaOptionValue P σ π d x t (.all x φ)=optionPoint P σ π d (some (.all x φ)) := by
  rw [formulaOptionValue_eq_native]
  simp only [NamedFiniteSyntax.Formula.substitute,ite_true]

example (x : ℕ) (t : Tm) (φ : Fm) (hf : φ.substitute x t=none) :
    formulaOptionValue P σ π d x t φ=optionPoint P σ π d none ∧
      formulaOptionValue P σ π d x t (.all x φ)=optionPoint P σ π d (some (.all x φ)) := by
  constructor
  · exact (formulaOptionValue_eq_native P σ π d x t φ).trans (congrArg (optionPoint P σ π d) hf)
  · rw [formulaOptionValue_eq_native]
    simp only [NamedFiniteSyntax.Formula.substitute,ite_true]

example (x y : ℕ) (t : Tm) (φ : Fm) (hxy : y≠x)
    (hx : x∈φ.freeVariables) (hy : y∈t.freeVariables) :
    formulaOptionValue P σ π d x t (.all y φ)=optionPoint P σ π d none := by
  rw [formulaOptionValue_eq_native]
  simp [NamedFiniteSyntax.Formula.substitute,hxy,hx,hy]

example (x : ℕ) (t : Tm) (φ : Fm) (hf : φ.substitute x t=none) :
    formulaOptionValue P σ π d x t (.neg φ)=optionPoint P σ π d none := by
  rw [formulaOptionValue_eq_native]
  change optionPoint P σ π d ((φ.substitute x t).map NamedFiniteSyntax.Formula.neg)=_
  rw [hf]
  rfl

example (x : ℕ) (t : Tm) (φ ψ φ' ψ' : Fm)
    (hφ : φ.substitute x t=some φ') (hψ : ψ.substitute x t=some ψ') :
    formulaOptionValue P σ π d x t (.imp φ ψ)=optionPoint P σ π d (some (.imp φ' ψ')) := by
  rw [formulaOptionValue_eq_native]
  simp [NamedFiniteSyntax.Formula.substitute,hφ,hψ]

example (x : ℕ) (t : Tm) (φ : Fm) :
    (optionPoint P σ π d none).val∈Total.val (S).formulaSubstitutionOption.hom
      (Points.substitutionPoint P σ π d x φ t).val ↔ ¬φ.FreeFor x t := by
  rw [native_option_graph]
  constructor
  · intro hn hf
    have hs := (NamedFiniteSyntax.Formula.substitute_isSome_iff φ x t).mpr hf
    rw [hn] at hs
    change (false : Bool)=true at hs
    cases hs
  · intro hf
    cases hs : φ.substitute x t with
    | none => rfl
    | some ψ =>
        exact False.elim (hf ((NamedFiniteSyntax.Formula.substitute_isSome_iff φ x t).mp (by rw [hs]; rfl)))

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeFormulaSubstitutionComparisonChecks
