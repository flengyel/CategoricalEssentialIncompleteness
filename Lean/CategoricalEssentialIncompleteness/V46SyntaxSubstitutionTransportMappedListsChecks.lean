/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportMappedLists


/-! # Statement checks in `V46SyntaxSubstitutionTransportMappedListsChecks` -/

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
variable (hLists : S₁.lists = mappedStableListAlgebra E (E.inverse.obj V) V
  (E.counitIso.app V) S₀.lists)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)


include hLists in
example :
    E.functor.map S₀.termSubstitution ≫ (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.1) (Y := S₀.substitutionParameters)
        (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c)
        (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.termSubstitution :=
  (termSubstitutionComparison_iff E V σ π d S₀ S₁ c).mp
    (mapped_termSubstitution_comparison E V σ π d S₀ S₁ hLists c)

include hLists in
example :
    E.functor.map S₀.formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso E (X := S₀.algebra.a.2)
          (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)).hom =
      (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.2) (Y := S₀.substitutionParameters)
        (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)
        (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.formulaSubstitutionOption :=
  (formulaSubstitutionOptionComparison_iff E V σ π d S₀ S₁ c).mp
    (mapped_formulaSubstitutionOption_comparison E V σ π d S₀ S₁ hLists c)

include hLists c in
example : E.functor.obj S₀.admissibleSubstitution ≅ S₁.admissibleSubstitution :=
  mappedAdmissibleSubstitutionIso E V σ π d S₀ S₁ hLists c

example :
    (mappedAdmissibleSubstitutionIso E V σ π d S₀ S₁ hLists c).hom ≫ S₁.admissibleInclusion =
      E.functor.map S₀.admissibleInclusion ≫
        (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.2) (Y := S₀.substitutionParameters)
          (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)
          (substitutionParameterIso E V σ π d S₀ S₁ c)).hom :=
  mappedAdmissibleSubstitutionIso_inclusion E V σ π d S₀ S₁ hLists c

example :
    (mappedAdmissibleSubstitutionIso E V σ π d S₀ S₁ hLists c).hom ≫ S₁.formulaSubstitution =
      E.functor.map S₀.formulaSubstitution ≫ (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c).hom :=
  mappedAdmissibleSubstitutionIso_result E V σ π d S₀ S₁ hLists c

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
