/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFunction
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsFormula

/-! The equality, relation, negation and implication substitution
operations inherit their comparisons from the actual ordinary constructors
and actual option operations. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem substitution_product_square {A B X Y : C} {A' B' X' Y' : D}
    (a : E.functor.obj A ≅ A') (b : E.functor.obj B ≅ B')
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : A ⟶ X) (g : B ⟶ Y) (f' : A' ⟶ X') (g' : B' ⟶ Y')
    (hf : E.functor.map f ≫ i.hom = (a).hom ≫ f')
    (hg : E.functor.map g ≫ j.hom = (b).hom ≫ g') :
    E.functor.map (prod.map f g) ≫ (SyntaxOptionTransport.productIso E i j).hom =
      (SyntaxOptionTransport.productIso E a b).hom ≫ prod.map f' g' := by
  change E.functor.map (prod.map f g) ≫
    (prodComparison E.functor X Y ≫ prod.map i.hom j.hom) =
    (prodComparison E.functor A B ≫ prod.map (a).hom (b).hom) ≫ prod.map f' g'
  rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,
    hf,hg,← prod.map_map,Category.assoc]

variable (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

/-- An ordinary constructor fed only term results always succeeds.
The two recursive projection squares are proved independently of it. -/
theorem substitution_positive_square (p : SyntaxPolynomial D)
    (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hp₁ : p.mapCoefficients id = p₁)
    (h : (p₀).eval.obj S₀.algebra.a ⟶ S₀.algebra.a.2)
    (h' : (p₁).eval.obj S₁.algebra.a ⟶ S₁.algebra.a.2)
    (hh : E.functor.map h ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a
        (syntaxCarrierIso E V σ π d S₀ c) p p₀ p₁ hp₀ hp₁).hom ≫ h') :
    E.functor.map (prod.lift
        ((p₀).eval.map S₀.originalProjection ≫ h)
        ((p₀).eval.map S₀.termResultProjection ≫ h ≫ coprod.inr)) ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
        (substitutionStateIso E V σ π d S₀ S₁ c) p p₀ p₁ hp₀ hp₁).hom ≫ prod.lift
        ((p₁).eval.map S₁.originalProjection ≫ h')
        ((p₁).eval.map S₁.termResultProjection ≫ h' ≫ coprod.inr) := by
  let f := syntaxFormulaIso E V σ π d S₀ c
  have ho := substitutionNormalizedPolynomial_natural E
    (substitutionStateIso E V σ π d S₀ S₁ c) (syntaxCarrierIso E V σ π d S₀ c)
    S₀.originalProjection S₁.originalProjection
    (substitutionOriginal_comparison E V σ π d S₀ S₁ c) p p₀ p₁ hp₀ hp₁
  have hr := substitutionNormalizedPolynomial_natural E
    (substitutionStateIso E V σ π d S₀ S₁ c) (syntaxCarrierIso E V σ π d S₀ c)
    S₀.termResultProjection S₁.termResultProjection
    (substitutionTermResult_comparison E V σ π d S₀ S₁ c) p p₀ p₁ hp₀ hp₁
  have h₀ : E.functor.map ((p₀).eval.map
        S₀.originalProjection ≫ h) ≫ (f).hom =
      (normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
        (substitutionStateIso E V σ π d S₀ S₁ c) p p₀ p₁ hp₀ hp₁).hom ≫
        ((p₁).eval.map S₁.originalProjection ≫ h') := by
    rw [E.functor.map_comp,Category.assoc,hh,← Category.assoc,ho,Category.assoc]
  have h₁ : E.functor.map ((p₀).eval.map
        S₀.termResultProjection ≫ h) ≫ (f).hom =
      (normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
        (substitutionStateIso E V σ π d S₀ S₁ c) p p₀ p₁ hp₀ hp₁).hom ≫
        ((p₁).eval.map S₁.termResultProjection ≫ h') := by
    rw [E.functor.map_comp,Category.assoc,hh,← Category.assoc,hr,Category.assoc]
  change E.functor.map (prod.lift _ _) ≫
    (SyntaxOptionTransport.productIso E f (SyntaxOptionTransport.optionIso E f)).hom =
    _ ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  apply congrArg₂ (fun a b => prod.lift a b)
  · exact h₀
  · rw [← Category.assoc,SyntaxOptionTransport.map_some,h₁,Category.assoc]
    simp only [Category.assoc]

theorem map_equalitySubstitutionPair :
    E.functor.map S₀.equalitySubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
        (substitutionStateIso E V σ π d S₀ S₁ c) (SyntaxPolynomial.power .term 2)
        (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl).hom ≫
        S₁.equalitySubstitutionPair := by
  let i := syntaxCarrierIso E V σ π d S₀ c
  have ht : normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i .term .term .term rfl rfl =
      syntaxTermIso E V σ π d S₀ c := Iso.ext (normalizedPolynomialIso_term E _ _ i)
  have hp : (normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i (SyntaxPolynomial.power .term 2)
      (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl).hom =
      (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c)
        (syntaxTermIso E V σ π d S₀ c)).hom := by
    simpa only [SyntaxPolynomial.power,ht] using
      normalizedPolynomialIso_product E S₀.algebra.a S₁.algebra.a i
        .term .term .term .term .term .term rfl rfl rfl rfl
  have hc : E.functor.map S₀.equalityConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a i (SyntaxPolynomial.power .term 2)
        (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl).hom ≫
        S₁.equalityConstructor := by
    rw [hp]
    exact syntax_equality_constructor E V σ π d S₀ S₁ c
  simpa only [CategoricalSyntax.equalitySubstitutionPair] using
    substitution_positive_square E V σ π d S₀ S₁ c (SyntaxPolynomial.power .term 2)
      (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl
      S₀.equalityConstructor S₁.equalityConstructor hc

theorem map_relationSubstitutionPair :
    E.functor.map S₀.relationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c π d).hom ≫
        S₁.relationSubstitutionPair := by
  simpa only [substitutionStateConstructorsInputIso,CategoricalSyntax.relationSubstitutionPair] using
    substitution_positive_square E V σ π d S₀ S₁ c (SyntaxPolynomial.constructors π d)
      (SyntaxPolynomial.constructors (fun n => E.inverse.obj (π n)) d) (SyntaxPolynomial.constructors π d)
      (mapCoefficients_constructors E.inverse.obj π d).symm
      (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) π d)
      S₀.relationConstructors S₁.relationConstructors
      (syntax_relation_constructors E V σ π d S₀ S₁ c)

theorem map_negationSubstitutionPair :
    E.functor.map S₀.negationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom ≫ S₁.negationSubstitutionPair := by
  let f := syntaxFormulaIso E V σ π d S₀ c
  let o := SyntaxOptionTransport.optionIso E f
  let s := substitutionFormulaStateIso E V σ π d S₀ S₁ c
  have h₀ : E.functor.map ((prod.fst : S₀.substitutionCarriers.2 ⟶ _) ≫
      S₀.negationConstructor) ≫ (f).hom = s.hom ≫ prod.fst ≫ S₁.negationConstructor := by
    rw [E.functor.map_comp,Category.assoc,syntax_negation_constructor,← Category.assoc,
      ← SyntaxOptionTransport.productIso_fst E f o,Category.assoc]
    rfl
  have h₁ : E.functor.map ((prod.snd : S₀.substitutionCarriers.2 ⟶ _) ≫
      OptionSyntax.map S₀.negationConstructor) ≫ o.hom =
      s.hom ≫ prod.snd ≫ OptionSyntax.map S₁.negationConstructor := by
    rw [E.functor.map_comp,Category.assoc,
      SyntaxOptionTransport.map_option_map E f f S₀.negationConstructor S₁.negationConstructor
        (syntax_negation_constructor E V σ π d S₀ S₁ c),
      ← Category.assoc,← SyntaxOptionTransport.productIso_snd E f o,Category.assoc]
    rfl
  change E.functor.map (prod.lift _ _) ≫ (SyntaxOptionTransport.productIso E f o).hom =
    s.hom ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  exact congrArg₂ (fun a b => prod.lift a b) h₀ h₁

theorem map_implicationSubstitutionPair :
    E.functor.map S₀.implicationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (SyntaxOptionTransport.productIso E
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c)
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c)).hom ≫ S₁.implicationSubstitutionPair := by
  let f := syntaxFormulaIso E V σ π d S₀ c
  let o := SyntaxOptionTransport.optionIso E f
  let s := substitutionFormulaStateIso E V σ π d S₀ S₁ c
  have hp := substitution_product_square E s s f f
    (prod.fst : S₀.substitutionCarriers.2 ⟶ _) prod.fst prod.fst prod.fst
    (SyntaxOptionTransport.productIso_fst E f o).symm
    (SyntaxOptionTransport.productIso_fst E f o).symm
  have hq := substitution_product_square E s s o o
    (prod.snd : S₀.substitutionCarriers.2 ⟶ _) prod.snd prod.snd prod.snd
    (SyntaxOptionTransport.productIso_snd E f o).symm
    (SyntaxOptionTransport.productIso_snd E f o).symm
  have h₀ : E.functor.map (prod.map prod.fst prod.fst ≫ S₀.implicationConstructor) ≫ (f).hom =
      (SyntaxOptionTransport.productIso E s s).hom ≫
        (prod.map prod.fst prod.fst ≫ S₁.implicationConstructor) := by
    rw [E.functor.map_comp,Category.assoc,syntax_implication_constructor,
      ← Category.assoc,hp,Category.assoc]
  have h₁ : E.functor.map (prod.map prod.snd prod.snd ≫ OptionSyntax.binary S₀.implicationConstructor) ≫
      o.hom = (SyntaxOptionTransport.productIso E s s).hom ≫
        (prod.map prod.snd prod.snd ≫ OptionSyntax.binary S₁.implicationConstructor) := by
    rw [E.functor.map_comp,Category.assoc,
      SyntaxOptionTransport.map_binary E f f S₀.implicationConstructor S₁.implicationConstructor
        (syntax_implication_constructor E V σ π d S₀ S₁ c),
      ← Category.assoc,hq,Category.assoc]
  change E.functor.map (prod.lift _ _) ≫ (SyntaxOptionTransport.productIso E f o).hom =
    _ ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  exact congrArg₂ (fun a b => prod.lift a b) h₀ h₁

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
