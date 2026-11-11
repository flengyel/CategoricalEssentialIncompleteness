/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaSubstitutionComparison
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainAdmissibleValues
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageDecoding

/-! # Reflection of actual successful instances to literal named substitution

The input of the theorem is a point of the constructed success pullback.
Its free-for condition and native output equation are proved from that
point, using the full native option comparison and both projections of
the success pullback.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => (Total.underlying (P := P))
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
private theorem nativeOptionCode_injective :
    Function.Injective (NamedPostfixEncoding.optionCode (σ := σ) (π := π) (d := d)) :=
  NamedPostfixEncoding.optionCode_injective

theorem source_success_native (a : PredicateInterpretation.Obj ℕ (S₀).admissibleSubstitution)
    (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hi : (N).map (S₀).admissibleInclusion a=SyntacticNamedHilbert.substitutionPoint σ π d x φ t)
    (hr : (N).map (S₀).formulaSubstitution a=SyntacticNamedHilbert.formulaPoint σ π d ψ) :
    φ.FreeFor x t ∧ φ.substitute x t=some ψ := by
  have hf := (ConcreteNamedComparison.plain_admissible_model_iff 𝗣𝗔 (V) σ π d ℕ
    (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)).mp ⟨a,hi⟩
  have hf' : ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) (V) σ π d
      x (termCode t) (formulaCode φ)=1 :=
    (SyntacticNamedHilbert.substitutionInput_scalar σ π d
      (ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) (V) σ π d) x φ t).symm.trans hf
  refine ⟨(@NamedPostfixEncoding.substitutionFreeFor_formulaCode σ π d φ t x).mp hf',?_⟩
  have hv := ConcreteNamedComparison.plain_formulaSubstitution_result 𝗣𝗔 (V) σ π d ℕ a
  erw [hi,hr] at hv
  have he := (SyntacticNamedHilbert.substitutionInput_scalar σ π d
    (ConcreteNamedSubstitution.substitutionResult (M := ℕ) (V) σ π d) x φ t).symm.trans hv
  rw [NamedPostfixEncoding.substitutionResult_formulaCode,SyntacticNamedHilbert.formulaPoint_value] at he
  apply nativeOptionCode_injective σ π d
  exact he

/-- Both the independently defined FreeFor condition and the literal
successful substitution equation follow from the actual target point. -/
theorem substitution_reflects_native (a : (U).obj (S).admissibleSubstitution)
    (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hi : (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t)
    (hr : (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ) :
    φ.FreeFor x t ∧ φ.substitute x t=some ψ := by
  have hs : φ.substitute x t=some ψ :=
    (NativeSubstitution.decodedResult_eq_substitute P σ π d x t φ).symm.trans
      ((NativeSubstitution.success_iff P σ π d x t φ ψ).mp ⟨a,hi,hr⟩)
  refine ⟨(Formula.substitute_isSome_iff φ x t).mp ?_,hs⟩
  rw [hs]
  rfl

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
