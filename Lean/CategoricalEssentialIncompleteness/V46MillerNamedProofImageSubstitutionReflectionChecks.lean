/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSubstitutionReflection


/-! # Statement checks in `V46MillerNamedProofImageSubstitutionReflectionChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "U" => Total.underlying (P := P)
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d
example (a : Total.underlying.obj (S).admissibleSubstitution)
    (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hi : Total.underlying.map (S).admissibleInclusion a=
      NamedProofImage.Points.substitutionPoint P σ π d x φ t)
    (hr : Total.underlying.map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) :
    φ.FreeFor x t ∧ φ.substitute x t=some ψ :=
  NamedProofImage.substitution_reflects_native P σ π d a x φ t ψ hi hr

example (a : (U).obj (S).admissibleSubstitution)
    (x : ℕ) (φ : Fm) (t : Tm)
    (hi : (U).map (S).admissibleInclusion a=
      NamedProofImage.Points.substitutionPoint P σ π d x φ t) :
    φ.FreeFor x t ∧ φ.substitute x t=some
      (NamedProofImage.decodeFormula P σ π d ((U).map (S).formulaSubstitution a)) := by
  exact NamedProofImage.substitution_reflects_native P σ π d a x φ t
    (NamedProofImage.decodeFormula P σ π d ((U).map (S).formulaSubstitution a)) hi
    (NamedProofImage.formulaPoint_decode P σ π d _).symm

example (x : ℕ) (t : Tm) (φ ψ : Fm) :
    (∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=
        NamedProofImage.Points.substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) ↔
        φ.substitute x t=some ψ := by
  constructor
  · rintro ⟨a,hi,hr⟩
    exact (NamedProofImage.substitution_reflects_native P σ π d a x φ t ψ hi hr).2
  · intro hs
    exact (NamedProofImage.NativeSubstitution.success_iff P σ π d x t φ ψ).mpr
      ((NamedProofImage.NativeSubstitution.decodedResult_eq_substitute P σ π d x t φ).trans hs)

example (x : ℕ) (t : Tm) (φ : Fm) (hn : φ.substitute x t=none) :
    ¬ ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=
        NamedProofImage.Points.substitutionPoint P σ π d x φ t := by
  rintro ⟨a,hi⟩
  have hs := (NamedProofImage.substitution_reflects_native P σ π d a x φ t
    (NamedProofImage.decodeFormula P σ π d ((U).map (S).formulaSubstitution a)) hi
    (NamedProofImage.formulaPoint_decode P σ π d _).symm).2
  rw [hn] at hs
  cases hs

example (x : ℕ) (t : Tm) (φ : Fm) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=
        NamedProofImage.Points.substitutionPoint P σ π d x (.all x φ) t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d (.all x φ) := by
  apply (NamedProofImage.NativeSubstitution.success_iff P σ π d x t (.all x φ) (.all x φ)).mpr
  exact (NamedProofImage.NativeSubstitution.decodedResult_eq_substitute P σ π d x t (.all x φ)).trans
    (by simp only [NamedFiniteSyntax.Formula.substitute, ite_true])

example (x : ℕ) (t : Tm) (φ : Fm) :
    NamedProofImage.NativeSubstitution.formulaOptionValue P σ π d x t φ=
      NamedProofImage.NativeSubstitution.optionPoint P σ π d (φ.substitute x t) :=
  NamedProofImage.NativeSubstitution.formulaOptionValue_eq_native P σ π d x t φ
