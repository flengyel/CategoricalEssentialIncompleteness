/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemes


/-! # Seven scheme witnesses in the uniform parameter objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedFiniteSyntax NamedPostfixEncoding
open NamedProofImage
open NamedProofImage.Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P:=P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (φ ψ : Fm) :
    (U).map (S).hilbertOne (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))=
      formulaPoint P σ π d (.imp φ (.imp ψ φ)) := hilbertOne_point P σ π d φ ψ
example (φ ψ χ : Fm) :
    (U).map (S).hilbertTwo
      (pairPoint (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
        (formulaPoint P σ π d χ))=
      formulaPoint P σ π d (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))) :=
  hilbertTwo_point P σ π d φ ψ χ
example (φ ψ : Fm) :
    (U).map (S).hilbertThree (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))=
      formulaPoint P σ π d (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) :=
  hilbertThree_point P σ π d φ ψ
example (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hf : φ.FreeFor x t) (hs : φ.substitute x t=some ψ) :
    ∃ a : (U).obj (S).instantiationParameters,
      (U).map (S).hilbertInstantiation a=formulaPoint P σ π d (.imp (.all x φ) ψ) :=
  hilbertInstantiation_point P σ π d x φ t ψ hf hs
example (x : ℕ) (φ ψ : Fm) (hx : x∉φ.freeVariables) :
    ∃ a : (U).obj (S).distributionParameters,
      (U).map (S).hilbertDistribution a=
        formulaPoint P σ π d (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) :=
  hilbertDistribution_point P σ π d x φ ψ hx
example (t : Tm) : (U).map (S).hilbertReflexivity (termPoint P σ π d t)=
    formulaPoint P σ π d (.equal t t) := hilbertReflexivity_point P σ π d t
example (x : ℕ) (φ : Fm) (u t : Tm) (ψ χ : Fm)
    (hfu : φ.FreeFor x u) (hft : φ.FreeFor x t)
    (hsu : φ.substitute x u=some ψ) (hst : φ.substitute x t=some χ) :
    ∃ a : (U).obj (S).equalitySchemeParameters,
      (U).map (S).hilbertEquality a=formulaPoint P σ π d (.imp (.equal u t) (.imp ψ χ)) :=
  hilbertEquality_point P σ π d x φ u t ψ χ hfu hft hsu hst
example : (distributionBaseChart P σ π d).hom ≫ (S).distributionAbsence=
    (Syntax.predicateFunctor P).map
      (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d).distributionAbsence ≫
        (Derivation.booleanIso (Syntax.predicateFunctor P)).hom :=
  distributionAbsence_comparison P σ π d

example (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hf : φ.FreeFor x t) (hs : φ.substitute x t=some ψ) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ :=
  substitution_instance P σ π d x φ t ψ hf hs

/-- A binder equal to the substituted name retains its original body,
including when substitution into that body fails. -/
example (x : ℕ) (t : Tm) (φ : Fm) (hbody : φ.substitute x t=none) :
    NativeSubstitution.formulaOptionValue P σ π d x t φ=
        NativeSubstitution.optionPoint P σ π d none ∧
      ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=substitutionPoint P σ π d x (.all x φ) t ∧
        (U).map (S).formulaSubstitution a=formulaPoint P σ π d (.all x φ) := by
  constructor
  · exact (NativeSubstitution.formulaOptionValue_eq_native P σ π d x t φ).trans
      (congrArg (NativeSubstitution.optionPoint P σ π d) hbody)
  · have hs : (Formula.all x φ).substitute x t=some (.all x φ) := by
      simp only [Formula.substitute, ite_true]
    have hf : (Formula.all x φ).FreeFor x t :=
      (Formula.substitute_isSome_iff (.all x φ) x t).mp (by rw [hs]; rfl)
    exact substitution_instance P σ π d x (.all x φ) t (.all x φ) hf hs

example (x : ℕ) (φ : Fm) (t : Tm) :
    NativeSubstitution.formulaOptionValue P σ π d x t φ=
      NativeSubstitution.optionPoint P σ π d (φ.substitute x t) :=
  NativeSubstitution.formulaOptionValue_eq_native P σ π d x t φ
