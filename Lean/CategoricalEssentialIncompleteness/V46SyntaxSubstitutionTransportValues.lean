/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportAlgebra
public import CategoricalEssentialIncompleteness.V46SyntaxOptionPullbackTransport

/-!
Intrinsic term substitution and option-valued formula substitution commute with the
input and output comparisons. Their admissibility objects are then compared by the
option-success pullback.
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
section FamilyValues
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
private theorem substitutionValueFamilyMap_left {A B : Over P} (f : A ⟶ B) :
    ((sliceEquivalence E b).functor.map f).left = E.functor.map f.left := rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- An equality of constant-family morphisms gives the corresponding ordinary value square
after applying the second product projection. -/
theorem substitutionFamilyValue_square {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : constantFamily P X ⟶ constantFamily P Y)
    (f' : constantFamily Q X' ⟶ constantFamily Q Y')
    (h : (sliceEquivalence E b).functor.map f ≫ (coefficientComparison E b Y Y' j).hom =
      (coefficientComparison E b X X' i).hom ≫ f') :
    E.functor.map ((f).left ≫ prod.snd) ≫ j.hom =
      (SyntaxOptionTransport.productIso E b i).hom ≫ f'.left ≫ prod.snd := by
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simp only [Over.comp_left,substitutionValueFamilyMap_left,Category.assoc] at hh
  rw [coefficientComparison_snd,← Category.assoc,← E.functor.map_comp,
    substitutionFamilyComparison_left] at hh
  exact hh

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- A map into the product comparison can be projected without assuming either source or
target product has numerical coordinates. -/
theorem substitutionValue_snd_square {X Y Z : C} {X' Y' Z' : D}
    (k : E.functor.obj X ≅ X') (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z')
    (f : X ⟶ Y ⨯ Z) (f' : X' ⟶ Y' ⨯ Z')
    (h : E.functor.map f ≫ (SyntaxOptionTransport.productIso E i j).hom = k.hom ≫ f') :
    E.functor.map (f ≫ prod.snd) ≫ j.hom = k.hom ≫ f' ≫ prod.snd := by
  have hh := congrArg (fun v => v ≫ prod.snd) h
  rw [Category.assoc,SyntaxOptionTransport.productIso_snd] at hh
  rw [← Category.assoc,← E.functor.map_comp] at hh
  simpa only [Category.assoc] using hh

end FamilyValues

section Substitution
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
theorem map_termSubstitution :
    E.functor.map S₀.termSubstitution ≫ (syntaxTermIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c) b).hom ≫
        S₁.termSubstitution := by
  have h := congrArg Prod.fst (substitutionFold_comparison E V σ π d S₀ S₁ c
    ℓ hnil hsingleton happend hdeletion hmembership)
  have hfamily : (H).functor.map S₀.substitutionFold.1 ≫
      (coefficientComparison E b S₀.substitutionCarriers.1 S₁.substitutionCarriers.1
        (substitutionTermStateIso E V σ π d S₀ S₁ c)).hom =
      (coefficientComparison E b S₀.algebra.a.1 S₁.algebra.a.1
        (syntaxTermIso E V σ π d S₀ c)).hom ≫ S₁.substitutionFold.1 := h
  have hv := substitutionFamilyValue_square E b (syntaxTermIso E V σ π d S₀ c)
    (substitutionTermStateIso E V σ π d S₀ S₁ c) S₀.substitutionFold.1 S₁.substitutionFold.1 hfamily
  have hr := substitutionValue_snd_square E
    (SyntaxOptionTransport.productIso E b (syntaxTermIso E V σ π d S₀ c))
    (syntaxTermIso E V σ π d S₀ c) (syntaxTermIso E V σ π d S₀ c)
    (S₀.substitutionFold.1.left ≫ prod.snd) (S₁.substitutionFold.1.left ≫ prod.snd) hv
  have hr' : E.functor.map (S₀.substitutionFold.1.left ≫ prod.snd ≫ prod.snd) ≫
      (syntaxTermIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E b (syntaxTermIso E V σ π d S₀ c)).hom ≫
        S₁.substitutionFold.1.left ≫ prod.snd ≫ prod.snd := by
    simpa only [Category.assoc] using hr
  dsimp only [CategoricalSyntax.termSubstitution]
  rw [E.functor.map_comp,Category.assoc,hr',← Category.assoc,
    substitutionProductIso_braiding,Category.assoc]

include hnil hsingleton happend hdeletion hmembership in
theorem map_formulaSubstitutionOption :
    E.functor.map S₀.formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c)).hom =
      (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b).hom ≫
        S₁.formulaSubstitutionOption := by
  have h := congrArg Prod.snd (substitutionFold_comparison E V σ π d S₀ S₁ c
    ℓ hnil hsingleton happend hdeletion hmembership)
  have hfamily : (H).functor.map S₀.substitutionFold.2 ≫
      (coefficientComparison E b S₀.substitutionCarriers.2 S₁.substitutionCarriers.2
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c)).hom =
      (coefficientComparison E b S₀.algebra.a.2 S₁.algebra.a.2
        (syntaxFormulaIso E V σ π d S₀ c)).hom ≫ S₁.substitutionFold.2 := h
  have hv := substitutionFamilyValue_square E b (syntaxFormulaIso E V σ π d S₀ c)
    (substitutionFormulaStateIso E V σ π d S₀ S₁ c) S₀.substitutionFold.2 S₁.substitutionFold.2 hfamily
  have hr := substitutionValue_snd_square E
    (SyntaxOptionTransport.productIso E b (syntaxFormulaIso E V σ π d S₀ c))
    (syntaxFormulaIso E V σ π d S₀ c)
    (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c))
    (S₀.substitutionFold.2.left ≫ prod.snd) (S₁.substitutionFold.2.left ≫ prod.snd) hv
  have hr' : E.functor.map (S₀.substitutionFold.2.left ≫ prod.snd ≫ prod.snd) ≫
      (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c)).hom =
      (SyntaxOptionTransport.productIso E b (syntaxFormulaIso E V σ π d S₀ c)).hom ≫
        S₁.substitutionFold.2.left ≫ prod.snd ≫ prod.snd := by
    simpa only [Category.assoc] using hr
  dsimp only [CategoricalSyntax.formulaSubstitutionOption]
  rw [E.functor.map_comp,Category.assoc,hr',← Category.assoc,
    substitutionProductIso_braiding,Category.assoc]

include hnil hsingleton happend hdeletion hmembership in
def admissibleSubstitutionIso : E.functor.obj S₀.admissibleSubstitution ≅ S₁.admissibleSubstitution :=
  SyntaxOptionTransport.successIso E
    (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b)
    (syntaxFormulaIso E V σ π d S₀ c)
    S₀.formulaSubstitutionOption S₁.formulaSubstitutionOption
    (map_formulaSubstitutionOption E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership)

include hnil hsingleton happend hdeletion hmembership in
@[reassoc] theorem admissibleSubstitutionIso_inclusion :
    (admissibleSubstitutionIso E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership).hom ≫
      S₁.admissibleInclusion = E.functor.map S₀.admissibleInclusion ≫
        (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b).hom :=
  SyntaxOptionTransport.successIso_fst E
    (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b)
    (syntaxFormulaIso E V σ π d S₀ c) S₀.formulaSubstitutionOption S₁.formulaSubstitutionOption
    (map_formulaSubstitutionOption E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership)

include hnil hsingleton happend hdeletion hmembership in
@[reassoc] theorem admissibleSubstitutionIso_result :
    (admissibleSubstitutionIso E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership).hom ≫
      S₁.formulaSubstitution = E.functor.map S₀.formulaSubstitution ≫
        (syntaxFormulaIso E V σ π d S₀ c).hom :=
  SyntaxOptionTransport.successIso_snd E
    (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b)
    (syntaxFormulaIso E V σ π d S₀ c) S₀.formulaSubstitutionOption S₁.formulaSubstitutionOption
    (map_formulaSubstitutionOption E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership)

end Substitution
end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
