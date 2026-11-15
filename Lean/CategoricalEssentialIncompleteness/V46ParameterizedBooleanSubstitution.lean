/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanSubstitutionInvariant
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionValues

/-! # Admissible substitution preserves a parameter-dependent Boolean value -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable {R : D} (s : R ⟶ P) (r : R ⟶ S.substitutionParameters)

theorem constructor_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a)
    (hm : m ≫ invariantResult S P d s r = m ≫ invariantMask S P d s r) :
    ((SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters R)
      ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters R)).map m ≫
        (ParameterizedSubstitution.algebra S r).str) ≫ invariantResult S P d s r =
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters R)
        ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters R)).map m ≫
          (ParameterizedSubstitution.algebra S r).str) ≫ invariantMask S P d s r := by
  apply Prod.ext
  · rfl
  · change (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters R).eval.map m ≫
        (ParameterizedSubstitution.algebra S r).str.2) ≫ (invariantResult S P d s r).2 =
      (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters R).eval.map m ≫
        (ParameterizedSubstitution.algebra S r).str.2) ≫ (invariantMask S P d s r).2
    rw [ParameterizedSubstitution.formula_structure]
    dsimp only [SyntaxPolynomial.formulaExpression]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
              SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
              Category.assoc] using equality_closed S P d s r m
          · simpa only [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, coprod.inl_map_assoc, coprod.inr_map_assoc,
              coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
                relation_closed S P d s r m
        · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
            SyntaxPolynomial.sumFunctor, SyntaxPolynomial.parameterComparison,
            Category.assoc] using negation_closed S P d s r m hm
      · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
          Category.assoc] using implication_closed S P d s r m hm
    · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        SyntaxPolynomial.parameterComparison, CategoryTheory.Functor.const,
        CategoryTheory.Prod.snd, Category.assoc] using quantifier_closed S P d s r m hm

theorem fold_invariant :
    ParameterizedSubstitution.fold S r ≫ invariantResult S P d s r =
      ParameterizedSubstitution.fold S r ≫ invariantMask S P d s r := by
  have := AlgebraInvariant.pairEqualizers (Over R)
  exact AlgebraInvariant.fold_equalizes
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
      (SyntaxPolynomial.formulaExpression V (fun _ => X) 0) S.algebra R)
    (ParameterizedSubstitution.algebra S r) (S.stable R)
    (invariantResult S P d s r) (invariantMask S P d s r) (constructor_closed S P d s r)

/-- The invariant applies to the original computed substitution state,
with independent support and binder/replacement morphisms. -/
theorem substitution_pair_good {W : D} (p : W ⟶ P)
    (q : W ⟶ S.substitutionParameters) (f : W ⟶ S.algebra.a.2) :
    PairGood S P d p (prod.lift q f ≫ S.substitutionFold.2.left ≫ prod.snd) := by
  have h := (invariant_equation S P d p q (ParameterizedSubstitution.fold S q).2).mp
    (congrArg Prod.snd (fold_invariant S P d p q))
  have hk := pairGood_precomp S P d _ _ h (prod.lift (𝟙 W) f)
  simpa only [Category.assoc, prod.lift_fst_assoc, Category.id_comp,
    ParameterizedSubstitution.formula_value, prod.lift_map_assoc, Category.comp_id,
    constantFamily, Over.mk_hom] using hk

/-- The full Option result has the original formula's value on success
and retains failure, uniformly over the support parameter. -/
theorem substitution_option_value {W : D} (p : W ⟶ P)
    (q : W ⟶ S.substitutionParameters) (f : W ⟶ S.algebra.a.2) :
    ParameterizedOption.map (value S P d) p
      (prod.lift f q ≫ S.formulaSubstitutionOption) =
        OptionSyntax.mask (evaluate S P d p f)
          (prod.lift f q ≫ S.formulaSubstitutionOption) := by
  have h := substitution_pair_good S P d p q f
  dsimp only [PairGood] at h
  have ho := S.formula_fold_original_value q f
  simp only [Category.assoc, ho] at h
  have hb : prod.lift f q ≫ (prod.braiding S.algebra.a.2 S.substitutionParameters).hom =
      prod.lift q f := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  simpa only [CategoricalSyntax.formulaSubstitutionOption, ← Category.assoc, hb] using h

/-- Every admissible substitution preserves the Boolean value at the
same internal support. No value equation is assumed. -/
theorem substitution_value {W : D} (p : W ⟶ P) (i : W ⟶ S.admissibleSubstitution) :
    evaluate S P d p (i ≫ S.formulaSubstitution) =
      evaluate S P d p (i ≫ S.admissibleInclusion ≫ prod.fst) := by
  let f := i ≫ S.admissibleInclusion ≫ prod.fst
  let q := i ≫ S.admissibleInclusion ≫ prod.snd
  have h := substitution_option_value S P d p q f
  have hi : prod.lift f q = i ≫ S.admissibleInclusion := by
    simp only [f, q, ← Category.assoc, parameterPair_eta]
  have hr : prod.lift f q ≫ S.formulaSubstitutionOption =
      (i ≫ S.formulaSubstitution) ≫ coprod.inr := by
    rw [hi, Category.assoc, S.formulaSubstitution_square, ← Category.assoc]
  rw [hr, ParameterizedOption.map_ok, OptionSyntax.mask_ok] at h
  exact (cancel_mono (coprod.inr : Two D ⟶ OptionSyntax.obj (Two D))).mp (by
    simpa only [evaluate, Category.assoc, f] using h)

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
