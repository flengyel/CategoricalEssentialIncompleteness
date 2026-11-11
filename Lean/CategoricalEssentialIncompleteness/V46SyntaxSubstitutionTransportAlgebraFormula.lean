/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportAlgebraTerm
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFormula
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportQuantifier

/-! The actual formula half of the substitution algebra comparison.
The pure constructor branches and both guarded quantifier branches are
transported before the actual coproduct universality is applied. -/

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
local notation "f" => substitutionFormulaStateIso E V σ π d S₀ S₁ c

theorem equalitySubstitutionParameter_structure :
    (H).functor.map
      (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers (SyntaxPolynomial.power .term 2) ≫
        (constantFamilyFunctor P₀).map S₀.equalitySubstitutionPair) ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
      (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
      (SyntaxPolynomial.power .term 2) rfl rfl).hom ≫
      SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (SyntaxPolynomial.power .term 2) ≫
        (constantFamilyFunctor P₁).map S₁.equalitySubstitutionPair := by
  exact pureSubstitutionParameter_structure E V σ π d S₀ S₁ c
    (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
    (SyntaxPolynomial.power .term 2) rfl rfl f
    S₀.equalitySubstitutionPair S₁.equalitySubstitutionPair
    (map_equalitySubstitutionPair E V σ π d S₀ S₁ c)

theorem relationSubstitutionParameter_structure :
    (H).functor.map
      (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers
        (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d) ≫
          (constantFamilyFunctor P₀).map S₀.relationSubstitutionPair) ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
      (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d)
      (SyntaxPolynomial.constructors π d) (mapCoefficients_constructors E.inverse.obj π d)
      (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d)).hom ≫
      SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (SyntaxPolynomial.constructors π d) ≫
        (constantFamilyFunctor P₁).map S₁.relationSubstitutionPair := by
  exact pureSubstitutionParameter_structure E V σ π d S₀ S₁ c
    (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d)
    (SyntaxPolynomial.constructors π d) (mapCoefficients_constructors E.inverse.obj π d)
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d) f
    S₀.relationSubstitutionPair S₁.relationSubstitutionPair
    (map_relationSubstitutionPair E V σ π d S₀ S₁ c)

theorem negationSubstitutionParameter_structure :
    (H).functor.map ((constantFamilyFunctor P₀).map S₀.negationSubstitutionPair) ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
      .formula .formula .formula rfl rfl).hom ≫
        (constantFamilyFunctor P₁).map S₁.negationSubstitutionPair := by
  have hn : substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      .formula .formula .formula rfl rfl = f :=
    Iso.ext (normalizedPolynomialIso_formula E S₀.substitutionCarriers S₁.substitutionCarriers a)
  have hroot : E.functor.map S₀.negationSubstitutionPair ≫ (f).hom =
      (substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
        .formula .formula .formula rfl rfl).hom ≫ S₁.negationSubstitutionPair := by
    rw [hn]
    exact map_negationSubstitutionPair E V σ π d S₀ S₁ c
  simpa only [SyntaxPolynomial.parameterComparison,Category.id_comp] using
    pureSubstitutionParameter_structure E V σ π d S₀ S₁ c
      .formula .formula .formula rfl rfl f
      S₀.negationSubstitutionPair S₁.negationSubstitutionPair hroot

theorem implicationSubstitutionParameter_structure :
    (H).functor.map
      (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers (SyntaxPolynomial.power .formula 2) ≫
        (constantFamilyFunctor P₀).map S₀.implicationSubstitutionPair) ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
      (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
      (SyntaxPolynomial.power .formula 2) rfl rfl).hom ≫
      SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (SyntaxPolynomial.power .formula 2) ≫
        (constantFamilyFunctor P₁).map S₁.implicationSubstitutionPair := by
  have hn : normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      .formula .formula .formula rfl rfl = f :=
    Iso.ext (normalizedPolynomialIso_formula E S₀.substitutionCarriers S₁.substitutionCarriers a)
  have hp : (substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
      (SyntaxPolynomial.power .formula 2) rfl rfl).hom =
      (SyntaxOptionTransport.productIso E f f).hom := by
    simpa only [substitutionNormalizedInputIso,SyntaxPolynomial.power,hn] using
      normalizedPolynomialIso_product E S₀.substitutionCarriers S₁.substitutionCarriers a
        .formula .formula .formula .formula .formula .formula rfl rfl rfl rfl
  have hroot : E.functor.map S₀.implicationSubstitutionPair ≫ (f).hom =
      (substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
        (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
        (SyntaxPolynomial.power .formula 2) rfl rfl).hom ≫ S₁.implicationSubstitutionPair := by
    rw [hp]
    exact map_implicationSubstitutionPair E V σ π d S₀ S₁ c
  exact pureSubstitutionParameter_structure E V σ π d S₀ S₁ c
    (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
    (SyntaxPolynomial.power .formula 2) rfl rfl f
    S₀.implicationSubstitutionPair S₁.implicationSubstitutionPair hroot

variable (ℓ : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hnil : E.functor.map S₀.lists.algebra.nil ≫ ℓ.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)
variable (hsingleton : E.functor.map S₀.lists.singleton ≫ ℓ.hom =
  (E.counitIso.app V).hom ≫ S₁.lists.singleton)
variable (happend : E.functor.map S₀.lists.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ S₁.lists.append)
variable (hdeletion : E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.deletion S₁.decidableVariables)
variable (hmembership : E.functor.map (S₀.lists.membership S₀.decidableVariables) ≫
  (DecidableVariables.Transport.booleanIso E).hom =
    (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
      S₁.lists.membership S₁.decidableVariables)

include hnil hsingleton happend hdeletion hmembership in
theorem quantifierSubstitutionParameter_structure :
    (H).functor.map
      (SyntaxPolynomial.parameterComparison P₀ S₀.substitutionCarriers
        (.product (.coefficient (E.inverse.obj V)) .formula) ≫ parameterHom S₀.quantifierSubstitutionPair) ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (substitutionNormalizedParameterInputIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
      (.product (.coefficient V) .formula) (.product (.coefficient (E.inverse.obj V)) .formula)
      (.product (.coefficient V) .formula) rfl rfl).hom ≫
      SyntaxPolynomial.parameterComparison P₁ S₁.substitutionCarriers (.product (.coefficient V) .formula) ≫
        parameterHom S₁.quantifierSubstitutionPair := by
  have hv : normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl = E.counitIso.app V :=
    Iso.ext (normalizedPolynomialIso_coefficient E S₀.substitutionCarriers S₁.substitutionCarriers a V)
  have hf : normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      .formula .formula .formula rfl rfl = f :=
    Iso.ext (normalizedPolynomialIso_formula E S₀.substitutionCarriers S₁.substitutionCarriers a)
  have hi : substitutionNormalizedInputIso E S₀.substitutionCarriers S₁.substitutionCarriers a
      (.product (.coefficient V) .formula) (.product (.coefficient (E.inverse.obj V)) .formula)
      (.product (.coefficient V) .formula) rfl rfl =
      SyntaxOptionTransport.productIso E (E.counitIso.app V) f := by
    apply Iso.ext
    simpa only [substitutionNormalizedInputIso,hv,hf] using
      normalizedPolynomialIso_product E S₀.substitutionCarriers S₁.substitutionCarriers a
        (.coefficient V) .formula (.coefficient (E.inverse.obj V)) .formula
        (.coefficient V) .formula rfl rfl rfl rfl
  have hroot : E.functor.map S₀.quantifierSubstitutionPair ≫ (f).hom =
      (SyntaxOptionTransport.productIso E b (substitutionNormalizedInputIso E
        S₀.substitutionCarriers S₁.substitutionCarriers a
        (.product (.coefficient V) .formula) (.product (.coefficient (E.inverse.obj V)) .formula)
        (.product (.coefficient V) .formula) rfl rfl)).hom ≫ S₁.quantifierSubstitutionPair := by
    rw [hi]
    exact map_quantifierSubstitutionPair E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership
  exact map_substitution_normalizedParameterOperation E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (.product (.coefficient V) .formula) (.product (.coefficient (E.inverse.obj V)) .formula)
    (.product (.coefficient V) .formula) rfl rfl f
    S₀.quantifierSubstitutionPair S₁.quantifierSubstitutionPair hroot

include hnil hsingleton happend hdeletion hmembership in
/-- All five formula summands are combined by genuine coproduct
universality. The quantifier equation has already accounted for both
success and failure branches. -/
theorem substitutionTargetFormula_structure :
    (H).functor.map S₀.substitutionAlgebra.str.2 ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2 f).hom =
    (syntaxParameterFormulaInputIso E b V π d S₀.substitutionCarriers S₁.substitutionCarriers a).hom ≫
      S₁.substitutionAlgebra.str.2 := by
  have he := equalitySubstitutionParameter_structure E V σ π d S₀ S₁ c
  have hr := relationSubstitutionParameter_structure E V σ π d S₀ S₁ c
  have hn := negationSubstitutionParameter_structure E V σ π d S₀ S₁ c
  have hi := implicationSubstitutionParameter_structure E V σ π d S₀ S₁ c
  have hq := quantifierSubstitutionParameter_structure E V σ π d S₀ S₁ c
    ℓ hnil hsingleton happend hdeletion hmembership
  have hatoms := substitutionNormalizedParameterCopair_square E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl
    (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d)
    (SyntaxPolynomial.constructors π d) (mapCoefficients_constructors E.inverse.obj π d)
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d) f
    _ _ _ _ he hr
  have hunary := substitutionNormalizedParameterCopair_square E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (substitutionFormulaAtoms π d) (substitutionFormulaAtoms (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaAtoms π d) (mapCoefficients_substitutionFormulaAtoms E.inverse.obj π d)
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaAtoms (id : D → D) π d)
    .formula .formula .formula rfl rfl f _ _ _ _ hatoms hn
  have hnon := substitutionNormalizedParameterCopair_square E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (substitutionFormulaUnary π d) (substitutionFormulaUnary (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaUnary π d) (mapCoefficients_substitutionFormulaUnary E.inverse.obj π d)
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaUnary (id : D → D) π d)
    (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
    (SyntaxPolynomial.power .formula 2) rfl rfl f _ _ _ _ hunary hi
  have hfull := substitutionNormalizedParameterCopair_square E b
    S₀.substitutionCarriers S₁.substitutionCarriers a
    (substitutionFormulaNonQuantifier π d) (substitutionFormulaNonQuantifier (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaNonQuantifier π d) (mapCoefficients_substitutionFormulaNonQuantifier E.inverse.obj π d)
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaNonQuantifier (id : D → D) π d)
    (.product (.coefficient V) .formula) (.product (.coefficient (E.inverse.obj V)) .formula)
    (.product (.coefficient V) .formula) rfl rfl f _ _ _ _ hnon hq
  simpa only [CategoricalSyntax.substitutionAlgebra,syntaxParameterFormulaInputIso,
    SyntaxPolynomial.formulaExpression,substitutionFormulaNonQuantifier,substitutionFormulaUnary,
    substitutionFormulaAtoms,SyntaxPolynomial.power] using hfull

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
