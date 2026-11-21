/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportParameterAlgebra
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportVariable
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFunction

/-!
The term half of the substitution algebra comparison. The variable and function
equations are derived from their proved base root comparisons, then combined by the
source coproduct.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
local notation "P₀" => S₀.substitutionParameters
local notation "P₁" => S₁.substitutionParameters
local notation "b" => substitutionParameterIso E V σ π d S₀ S₁ c
local notation "H" => sliceEquivalence E b
local notation "a" => substitutionStateIso E V σ π d S₀ S₁ c
local notation "t" => substitutionTermStateIso E V σ π d S₀ S₁ c

/-- The premise is an ordinary root-operation square, not a fold law.
This helper lifts it to its full parameter-polynomial input. -/
theorem pureSubstitutionParameter_structure
    (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (h₀ : p.mapCoefficients E.inverse.obj = p₀) (h₁ : p.mapCoefficients id = p₁)
    {Z : C} {Z' : D} (j : E.functor.obj Z ≅ Z')
    (f : (p₀).eval.obj S₀.substitutionCarriers ⟶ Z)
    (f' : (p₁).eval.obj S₁.substitutionCarriers ⟶ Z')
    (hf : E.functor.map f ≫ j.hom =
      (substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
        p p₀ p₁ h₀ h₁).hom ≫ f') :
    (H).functor.map (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers p₀ ≫
        (constantFamilyFunctor P₀).map f) ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
        p p₀ p₁ h₀ h₁).hom ≫ SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers p₁ ≫
          (constantFamilyFunctor P₁).map f' := by
  have hc := substitution_parameterize_square E b
    (substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a p p₀ p₁ h₀ h₁)
    j f f' hf
  have h := map_substitution_normalizedParameterOperation E b
    S₀.substitutionCarriers S₁.substitutionCarriers a p p₀ p₁ h₀ h₁ j
    (prod.snd ≫ f) (prod.snd ≫ f') hc
  simpa only [← substitution_constantFamily_map] using h

theorem variableSubstitutionParameter_structure :
    (H).functor.map (parameterHom S₀.variableSubstitutionPair) ≫
        (coefficientComparison E b S₀.substitutionCarriers.1 S₁.substitutionCarriers.1 t).hom =
      (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
        (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl).hom ≫
          parameterHom S₁.variableSubstitutionPair := by
  have hv : substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl = E.counitIso.app V :=
    Iso.ext (normalizedPolynomialIso_coefficient E S₀.substitutionCarriers S₁.substitutionCarriers a V)
  have hc : E.functor.map S₀.variableSubstitutionPair ≫ (t).hom =
      (SyntaxOptionTransport.productIso E b (substitutionNormalizedInputIso E
        S₀.substitutionCarriers S₁.substitutionCarriers a (.coefficient V)
        (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl)).hom ≫
          S₁.variableSubstitutionPair := by
    rw [hv]
    exact map_variableSubstitutionPair E V σ π d S₀ S₁ c
  simpa only [SyntaxPolynomial.parameterComparison,Category.id_comp] using
    map_substitution_normalizedParameterOperation E b S₀.substitutionCarriers S₁.substitutionCarriers a
      (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl t
      S₀.variableSubstitutionPair S₁.variableSubstitutionPair hc

theorem functionSubstitutionParameter_structure :
    (H).functor.map
      (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers
        (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d) ≫
          (constantFamilyFunctor P₀).map S₀.functionSubstitutionPair) ≫
        (coefficientComparison E b S₀.substitutionCarriers.1 S₁.substitutionCarriers.1 t).hom =
      (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
        (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
        (SyntaxPolynomial.constructors σ d) (mapCoefficients_constructors E.inverse.obj σ d)
        (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d)).hom ≫
      SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (SyntaxPolynomial.constructors σ d) ≫
        (constantFamilyFunctor P₁).map S₁.functionSubstitutionPair := by
  exact pureSubstitutionParameter_structure E V σ π d S₀ S₁ c
    (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    (SyntaxPolynomial.constructors σ d) (mapCoefficients_constructors E.inverse.obj σ d)
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d) t
    S₀.functionSubstitutionPair S₁.functionSubstitutionPair
    (map_functionSubstitutionPair E V σ π d S₀ S₁ c)

/-- The complete term constructor square is obtained from the two
proved summand equations. No substitution-fold equation is a premise. -/
theorem substitutionTargetTerm_structure :
    (H).functor.map S₀.substitutionAlgebra.str.1 ≫
        (coefficientComparison E b S₀.substitutionCarriers.1 S₁.substitutionCarriers.1 t).hom =
      (syntaxParameterTermInputIso E b V σ d S₀.substitutionCarriers S₁.substitutionCarriers a).hom ≫
        S₁.substitutionAlgebra.str.1 := by
  have h := substitutionNormalizedParameterCopair_square E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl
    (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    (SyntaxPolynomial.constructors σ d) (mapCoefficients_constructors E.inverse.obj σ d)
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d) t
    (parameterHom S₀.variableSubstitutionPair)
    (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers
      (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d) ≫
        (constantFamilyFunctor P₀).map S₀.functionSubstitutionPair)
    (parameterHom S₁.variableSubstitutionPair)
    (SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (SyntaxPolynomial.constructors σ d) ≫
      (constantFamilyFunctor P₁).map S₁.functionSubstitutionPair)
    (variableSubstitutionParameter_structure E V σ π d S₀ S₁ c)
    (functionSubstitutionParameter_structure E V σ π d S₀ S₁ c)
  simpa only [CategoricalSyntax.substitutionAlgebra,syntaxParameterTermInputIso,
    SyntaxPolynomial.termExpression] using h

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
