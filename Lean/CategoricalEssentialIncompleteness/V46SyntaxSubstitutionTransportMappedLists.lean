/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportValues
public import CategoricalEssentialIncompleteness.V46SyntaxMappedListOccurrenceComparison

/-!
The complete intrinsic substitution comparison from the mapped stable-list record
equality. No list-operation or fold equality is an additional hypothesis at this
endpoint.
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
variable (hLists : S₁.lists = mappedStableListAlgebra E (E.inverse.obj V) V
  (E.counitIso.app V) S₀.lists)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

/-- This predicate is exactly the intrinsic term-substitution diagram. -/
def termSubstitutionComparison : Prop :=
  E.functor.map S₀.termSubstitution ≫ (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom =
    (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.1) (Y := S₀.substitutionParameters)
      (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c)
      (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.termSubstitution

/-- This predicate is exactly the intrinsic option-valued formula diagram. -/
def formulaSubstitutionOptionComparison : Prop :=
  E.functor.map S₀.formulaSubstitutionOption ≫
      (SyntaxOptionTransport.optionIso E (X := S₀.algebra.a.2)
        (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)).hom =
    (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.2) (Y := S₀.substitutionParameters)
      (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)
      (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.formulaSubstitutionOption

include hLists in
theorem mapped_termSubstitution_comparison : termSubstitutionComparison E V σ π d S₀ S₁ c :=
  map_termSubstitution E V σ π d S₀ S₁ c (syntaxListIso E V σ π d S₀ S₁ hLists)
    (syntaxList_nil_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_singleton_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_append_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_deletion_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_membership_comparison E V σ π d S₀ S₁ hLists)

include hLists in
theorem mapped_formulaSubstitutionOption_comparison :
    formulaSubstitutionOptionComparison E V σ π d S₀ S₁ c :=
  map_formulaSubstitutionOption E V σ π d S₀ S₁ c (syntaxListIso E V σ π d S₀ S₁ hLists)
    (syntaxList_nil_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_singleton_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_append_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_deletion_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_membership_comparison E V σ π d S₀ S₁ hLists)

def mappedAdmissibleSubstitutionIso : E.functor.obj S₀.admissibleSubstitution ≅ S₁.admissibleSubstitution :=
  admissibleSubstitutionIso E V σ π d S₀ S₁ c (syntaxListIso E V σ π d S₀ S₁ hLists)
    (syntaxList_nil_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_singleton_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_append_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_deletion_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_membership_comparison E V σ π d S₀ S₁ hLists)

@[reassoc] theorem mappedAdmissibleSubstitutionIso_inclusion :
    (mappedAdmissibleSubstitutionIso E V σ π d S₀ S₁ hLists c).hom ≫ S₁.admissibleInclusion =
      E.functor.map S₀.admissibleInclusion ≫
        (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.2) (Y := S₀.substitutionParameters)
          (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)
          (substitutionParameterIso E V σ π d S₀ S₁ c)).hom :=
  admissibleSubstitutionIso_inclusion E V σ π d S₀ S₁ c (syntaxListIso E V σ π d S₀ S₁ hLists)
    (syntaxList_nil_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_singleton_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_append_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_deletion_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_membership_comparison E V σ π d S₀ S₁ hLists)

@[reassoc] theorem mappedAdmissibleSubstitutionIso_result :
    (mappedAdmissibleSubstitutionIso E V σ π d S₀ S₁ hLists c).hom ≫ S₁.formulaSubstitution =
      E.functor.map S₀.formulaSubstitution ≫ (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c).hom :=
  admissibleSubstitutionIso_result E V σ π d S₀ S₁ c (syntaxListIso E V σ π d S₀ S₁ hLists)
    (syntaxList_nil_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_singleton_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_append_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_deletion_comparison E V σ π d S₀ S₁ hLists)
    (syntaxList_membership_comparison E V σ π d S₀ S₁ hLists)

theorem termSubstitutionComparison_iff : termSubstitutionComparison E V σ π d S₀ S₁ c ↔
    E.functor.map S₀.termSubstitution ≫ (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.1) (Y := S₀.substitutionParameters)
        (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c)
        (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.termSubstitution := Iff.rfl

theorem formulaSubstitutionOptionComparison_iff : formulaSubstitutionOptionComparison E V σ π d S₀ S₁ c ↔
    E.functor.map S₀.formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso E (X := S₀.algebra.a.2)
          (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)).hom =
      (SyntaxOptionTransport.productIso E (X := S₀.algebra.a.2) (Y := S₀.substitutionParameters)
        (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c)
        (substitutionParameterIso E V σ π d S₀ S₁ c)).hom ≫ S₁.formulaSubstitutionOption := Iff.rfl

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
