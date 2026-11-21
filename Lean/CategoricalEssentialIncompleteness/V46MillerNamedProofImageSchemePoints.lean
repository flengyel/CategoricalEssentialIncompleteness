/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImagePoints
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaSubstitutionComparison
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonFreeVariables
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportDeletion

/-! # Seven scheme witnesses in the uniform parameter objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace Points
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

/-- The full substitution option comparison supplies a point of the success pullback with
its input and result projections. -/
theorem substitution_instance (x : ℕ) (φ : Fm) (t₀ : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t₀) (hs : φ.substitute x t₀=some ψ) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=substitutionPoint P σ π d x φ t₀ ∧
        (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ := by
  have hnative : φ.FreeFor x t₀ ∧ φ.substitute x t₀=some ψ := ⟨hff,hs⟩
  exact (NativeSubstitution.success_iff P σ π d x t₀ φ ψ).mpr
    ((NativeSubstitution.decodedResult_eq_substitute P σ π d x t₀ φ).trans hnative.2)

private theorem identity_value (X : Total.TotalCategory P) (x : (U).obj X) :
    ((U).map (𝟙 X) x).val=x.val := congrArg Subtype.val ((U).map_id_apply X x)
theorem hilbertOne_point (φ ψ : Fm) :
    (U).map (S).hilbertOne
      (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) =
        formulaPoint P σ π d (.imp φ (.imp ψ φ)) := by
  dsimp only [CategoricalSyntax.hilbertOne]
  apply implication_at P σ π d
  · exact pairPoint_fst _ _
  · apply implication_at P σ π d
    · exact pairPoint_snd _ _
    · exact pairPoint_fst _ _

theorem hilbertTwo_point (φ ψ χ : Fm) :
    (U).map (S).hilbertTwo
      (pairPoint
        (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
        (formulaPoint P σ π d χ)) =
        formulaPoint P σ π d (.imp (.imp φ (.imp ψ χ))
          (.imp (.imp φ ψ) (.imp φ χ))) := by
  dsimp only [CategoricalSyntax.hilbertTwo]
  apply implication_at P σ π d
  · apply implication_at P σ π d
    · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst]
    · apply implication_at P σ π d
      · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_snd]
      · exact pairPoint_snd _ _
  · apply implication_at P σ π d
    · exact ((U).map_comp_apply _ _ _).trans
        ((congrArg ((U).map (S).implicationConstructor)
          (pairPoint_fst _ _)).trans (implication_point P σ π d φ ψ))
    · apply implication_at P σ π d
      · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst]
      · exact pairPoint_snd _ _

theorem hilbertThree_point (φ ψ : Fm) :
    (U).map (S).hilbertThree
      (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) =
        formulaPoint P σ π d (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) := by
  dsimp only [CategoricalSyntax.hilbertThree]
  apply implication_at P σ π d
  · apply implication_at P σ π d
    · apply negation_at P σ π d
      exact pairPoint_snd _ _
    · apply negation_at P σ π d
      exact pairPoint_fst _ _
  · exact implication_point P σ π d φ ψ

theorem hilbertReflexivity_point (t : Tm) :
    (U).map (S).hilbertReflexivity (termPoint P σ π d t) =
      formulaPoint P σ π d (.equal t t) := by
  dsimp only [CategoricalSyntax.hilbertReflexivity]
  apply equality_at P σ π d
  · apply Subtype.ext
    exact identity_value P ((S).algebra.a.1) (termPoint P σ π d t)
  · apply Subtype.ext
    exact identity_value P ((S).algebra.a.1) (termPoint P σ π d t)

/-- The original instantiation coordinates map to the public substitution input through
its permutation morphism. -/
theorem instantiationInput_point (x : ℕ) (φ : Fm) (t : Tm) :
    (U).map (S).instantiationInput
      (pairPoint (namePoint P x)
        (pairPoint (formulaPoint P σ π d φ) (termPoint P σ π d t))) =
      substitutionPoint P σ π d x φ t := by
  dsimp only [CategoricalSyntax.instantiationInput,substitutionPoint]
  erw [lift_point,lift_point]
  erw [CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst,
    pairPoint_fst,CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]

theorem hilbertInstantiation_point (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ z : (U).obj (S).instantiationParameters,
      (U).map (S).hilbertInstantiation z = formulaPoint P σ π d (.imp (.all x φ) ψ) := by
  obtain ⟨a,ha,hr⟩ := substitution_instance P σ π d x φ t ψ hff hs
  let base := pairPoint (namePoint P x)
    (pairPoint (formulaPoint P σ π d φ) (termPoint P σ π d t))
  have hb : (U).map (S).instantiationInput base = (U).map (S).admissibleInclusion a :=
    (instantiationInput_point P σ π d x φ t).trans ha.symm
  obtain ⟨z,hz,ha'⟩ := pullback_point_exists
    (S).instantiationInput (S).admissibleInclusion base a hb
  have hz' : (U).map (S).instantiationInclusion z = base := hz
  have ha'' : (U).map (S).instantiationAdmissible z = a := ha'
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertInstantiation]
  apply implication_at P σ π d
  · apply quantifier_at P σ π d
    · exact ((U).map_comp_apply _ _ z).trans
        ((congrArg ((U).map prod.fst) hz').trans (pairPoint_fst _ _))
    · erw [CategoryTheory.Functor.map_comp_apply,hz',CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
  · exact ((U).map_comp_apply _ _ z).trans
      ((congrArg ((U).map (S).formulaSubstitution) ha'').trans hr)


end Points
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
