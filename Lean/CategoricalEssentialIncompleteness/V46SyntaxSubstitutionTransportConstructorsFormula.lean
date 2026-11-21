/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsCore

/-!
Formula constructor comparisons obtained from the algebra isomorphism, with explicit
coefficient-template normalization.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport

def substitutionFormulaAtoms {I : Type w₁} (π : ℕ → I) (d : ℕ) : SyntaxPolynomial I :=
  .sum (.product .term .term) (SyntaxPolynomial.constructors π d)
def substitutionFormulaUnary {I : Type w₁} (π : ℕ → I) (d : ℕ) : SyntaxPolynomial I :=
  .sum (substitutionFormulaAtoms π d) .formula
def substitutionFormulaNonQuantifier {I : Type w₁} (π : ℕ → I) (d : ℕ) : SyntaxPolynomial I :=
  .sum (substitutionFormulaUnary π d) (.product .formula .formula)

theorem mapCoefficients_substitutionFormulaAtoms {I : Type w₁} {J : Type w₂}
    (f : I → J) (π : ℕ → I) (d : ℕ) :
    (substitutionFormulaAtoms π d).mapCoefficients f = substitutionFormulaAtoms (fun n => f (π n)) d := by
  simp only [substitutionFormulaAtoms,SyntaxPolynomial.mapCoefficients,mapCoefficients_constructors]
theorem mapCoefficients_substitutionFormulaUnary {I : Type w₁} {J : Type w₂}
    (f : I → J) (π : ℕ → I) (d : ℕ) :
    (substitutionFormulaUnary π d).mapCoefficients f = substitutionFormulaUnary (fun n => f (π n)) d := by
  simp only [substitutionFormulaUnary,SyntaxPolynomial.mapCoefficients,mapCoefficients_substitutionFormulaAtoms]
theorem mapCoefficients_substitutionFormulaNonQuantifier {I : Type w₁} {J : Type w₂}
    (f : I → J) (π : ℕ → I) (d : ℕ) :
    (substitutionFormulaNonQuantifier π d).mapCoefficients f =
      substitutionFormulaNonQuantifier (fun n => f (π n)) d := by
  simp only [substitutionFormulaNonQuantifier,SyntaxPolynomial.mapCoefficients,
    mapCoefficients_substitutionFormulaUnary]

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def syntaxFormulaAtomsInputIso :
    E.functor.obj ((substitutionFormulaAtoms (fun n => E.inverse.obj (π n)) d).eval.obj S₀.algebra.a) ≅
      (substitutionFormulaAtoms π d).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaAtoms π d) (substitutionFormulaAtoms (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaAtoms π d)
    (mapCoefficients_substitutionFormulaAtoms E.inverse.obj π d).symm
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaAtoms (id : D → D) π d)
def syntaxFormulaUnaryInputIso :
    E.functor.obj ((substitutionFormulaUnary (fun n => E.inverse.obj (π n)) d).eval.obj S₀.algebra.a) ≅
      (substitutionFormulaUnary π d).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaUnary π d) (substitutionFormulaUnary (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaUnary π d)
    (mapCoefficients_substitutionFormulaUnary E.inverse.obj π d).symm
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaUnary (id : D → D) π d)
def syntaxFormulaNonQuantifierInputIso :
    E.functor.obj ((substitutionFormulaNonQuantifier (fun n => E.inverse.obj (π n)) d).eval.obj S₀.algebra.a) ≅
      (substitutionFormulaNonQuantifier π d).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaNonQuantifier π d) (substitutionFormulaNonQuantifier (fun n => E.inverse.obj (π n)) d)
    (substitutionFormulaNonQuantifier π d)
    (mapCoefficients_substitutionFormulaNonQuantifier E.inverse.obj π d).symm
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaNonQuantifier (id : D → D) π d)

theorem syntax_formula_nonQuantifier_structure :
    E.functor.map (coprod.inl ≫ S₀.algebra.str.2) ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxFormulaNonQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ coprod.inl ≫ S₁.algebra.str.2 := by
  exact normalizedConstructorSummand_inl E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaNonQuantifier π d) (.product (.coefficient V) .formula)
    (substitutionFormulaNonQuantifier (fun n => E.inverse.obj (π n)) d)
    (.product (.coefficient (E.inverse.obj V)) .formula)
    (substitutionFormulaNonQuantifier π d) (.product (.coefficient V) .formula)
    (mapCoefficients_substitutionFormulaNonQuantifier E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaNonQuantifier (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) S₀.algebra.str.2 S₁.algebra.str.2
    (syntax_formula_structure E V σ π d S₀ S₁ c)

theorem syntax_formula_unary_structure :
    E.functor.map (coprod.inl ≫ coprod.inl ≫ S₀.algebra.str.2) ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxFormulaUnaryInputIso E V σ π d S₀ S₁ c).hom ≫ coprod.inl ≫ coprod.inl ≫ S₁.algebra.str.2 := by
  exact normalizedConstructorSummand_inl E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaUnary π d) (.product .formula .formula)
    (substitutionFormulaUnary (fun n => E.inverse.obj (π n)) d) (.product .formula .formula)
    (substitutionFormulaUnary π d) (.product .formula .formula)
    (mapCoefficients_substitutionFormulaUnary E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaUnary (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) _ _
    (syntax_formula_nonQuantifier_structure E V σ π d S₀ S₁ c)

theorem syntax_formula_atoms_structure :
    E.functor.map (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ S₀.algebra.str.2) ≫
        (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxFormulaAtomsInputIso E V σ π d S₀ S₁ c).hom ≫
        coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ S₁.algebra.str.2 := by
  exact normalizedConstructorSummand_inl E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaAtoms π d) .formula
    (substitutionFormulaAtoms (fun n => E.inverse.obj (π n)) d) .formula
    (substitutionFormulaAtoms π d) .formula
    (mapCoefficients_substitutionFormulaAtoms E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaAtoms (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) _ _ (syntax_formula_unary_structure E V σ π d S₀ S₁ c)

theorem syntax_equality_constructor :
    E.functor.map S₀.equalityConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c)
        (syntaxTermIso E V σ π d S₀ c)).hom ≫ S₁.equalityConstructor := by
  let i := syntaxCarrierIso E V σ π d S₀ c
  have ht : normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i .term .term .term rfl rfl =
      syntaxTermIso E V σ π d S₀ c := Iso.ext (normalizedPolynomialIso_term E _ _ i)
  have h := normalizedConstructorSummand_inl E S₀.algebra.a S₁.algebra.a i
    (.product .term .term) (SyntaxPolynomial.constructors π d)
    (.product .term .term) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d)
    (.product .term .term) (SyntaxPolynomial.constructors π d) rfl
    (mapCoefficients_constructors E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d)
    (syntaxFormulaIso E V σ π d S₀ c) _ _ (syntax_formula_atoms_structure E V σ π d S₀ S₁ c)
  have hp := normalizedPolynomialIso_product E S₀.algebra.a S₁.algebra.a i
    .term .term .term .term .term .term rfl rfl rfl rfl
  rw [ht] at hp
  erw [hp] at h
  dsimp only [SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,CategoryTheory.Prod.fst] at h
  dsimp only [CategoricalSyntax.equalityConstructor]
  exact h

theorem syntax_relation_constructors :
    E.functor.map S₀.relationConstructors ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxConstructorsInputIso E V σ π d S₀ S₁ c π d).hom ≫ S₁.relationConstructors := by
  have h := normalizedConstructorSummand_inr E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (.product .term .term) (SyntaxPolynomial.constructors π d)
    (.product .term .term) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d)
    (.product .term .term) (SyntaxPolynomial.constructors π d) rfl
    (mapCoefficients_constructors E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d)
    (syntaxFormulaIso E V σ π d S₀ c) _ _ (syntax_formula_atoms_structure E V σ π d S₀ S₁ c)
  dsimp only [CategoricalSyntax.relationConstructors,syntaxConstructorsInputIso]
  exact h

theorem syntax_negation_constructor :
    E.functor.map S₀.negationConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxFormulaIso E V σ π d S₀ c).hom ≫ S₁.negationConstructor := by
  have h := normalizedConstructorSummand_inr E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (substitutionFormulaAtoms π d) .formula
    (substitutionFormulaAtoms (fun n => E.inverse.obj (π n)) d) .formula
    (substitutionFormulaAtoms π d) .formula
    (mapCoefficients_substitutionFormulaAtoms E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaAtoms (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) _ _ (syntax_formula_unary_structure E V σ π d S₀ S₁ c)
  rw [normalizedPolynomialIso_formula] at h
  dsimp only [SyntaxPolynomial.eval,CategoryTheory.Prod.snd] at h
  have hi : (syntaxCarrierIso E V σ π d S₀ c).hom.2 =
      (syntaxFormulaIso E V σ π d S₀ c).hom := rfl
  rw [hi] at h
  dsimp only [CategoricalSyntax.negationConstructor,CategoricalSyntax.negationInjection]
  simp only [Category.assoc]
  exact h

theorem syntax_implication_constructor :
    E.functor.map S₀.implicationConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c)
        (syntaxFormulaIso E V σ π d S₀ c)).hom ≫ S₁.implicationConstructor := by
  let i := syntaxCarrierIso E V σ π d S₀ c
  have hf : normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i .formula .formula .formula rfl rfl =
      syntaxFormulaIso E V σ π d S₀ c := Iso.ext (normalizedPolynomialIso_formula E _ _ i)
  have h := normalizedConstructorSummand_inr E S₀.algebra.a S₁.algebra.a i
    (substitutionFormulaUnary π d) (.product .formula .formula)
    (substitutionFormulaUnary (fun n => E.inverse.obj (π n)) d) (.product .formula .formula)
    (substitutionFormulaUnary π d) (.product .formula .formula)
    (mapCoefficients_substitutionFormulaUnary E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaUnary (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) _ _ (syntax_formula_nonQuantifier_structure E V σ π d S₀ S₁ c)
  have hp := normalizedPolynomialIso_product E S₀.algebra.a S₁.algebra.a i
    .formula .formula .formula .formula .formula .formula rfl rfl rfl rfl
  rw [hf] at hp
  erw [hp] at h
  dsimp only [SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,CategoryTheory.Prod.snd] at h
  dsimp only [CategoricalSyntax.implicationConstructor]
  exact h

theorem syntax_quantifier_constructor :
    E.functor.map S₀.quantifierConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (E.counitIso.app V)
        (syntaxFormulaIso E V σ π d S₀ c)).hom ≫ S₁.quantifierConstructor := by
  let i := syntaxCarrierIso E V σ π d S₀ c
  have hf : normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i .formula .formula .formula rfl rfl =
      syntaxFormulaIso E V σ π d S₀ c := Iso.ext (normalizedPolynomialIso_formula E _ _ i)
  have hv : normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i
      (.coefficient V) (.coefficient (E.inverse.obj V)) (.coefficient V) rfl rfl = E.counitIso.app V :=
    Iso.ext (normalizedPolynomialIso_coefficient E _ _ i V)
  have h := normalizedConstructorSummand_inr E S₀.algebra.a S₁.algebra.a i
    (substitutionFormulaNonQuantifier π d) (.product (.coefficient V) .formula)
    (substitutionFormulaNonQuantifier (fun n => E.inverse.obj (π n)) d)
    (.product (.coefficient (E.inverse.obj V)) .formula)
    (substitutionFormulaNonQuantifier π d) (.product (.coefficient V) .formula)
    (mapCoefficients_substitutionFormulaNonQuantifier E.inverse.obj π d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_substitutionFormulaNonQuantifier (id : D → D) π d) rfl
    (syntaxFormulaIso E V σ π d S₀ c) S₀.algebra.str.2 S₁.algebra.str.2
    (syntax_formula_structure E V σ π d S₀ S₁ c)
  have hp := normalizedPolynomialIso_product E S₀.algebra.a S₁.algebra.a i
    (.coefficient V) .formula (.coefficient (E.inverse.obj V)) .formula (.coefficient V) .formula
    rfl rfl rfl rfl
  rw [hv,hf] at hp
  erw [hp] at h
  dsimp only [SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,CategoryTheory.Prod.snd,Functor.const] at h
  dsimp only [CategoricalSyntax.quantifierConstructor]
  exact h

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
