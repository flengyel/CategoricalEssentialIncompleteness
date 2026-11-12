/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitutionInvariant

/-! # Successful substitution preserves Boolean value -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)

theorem constructor_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d = m ≫ invariantResult S d) :
    ((SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters
        S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
        S.substitutionParameters)).map m ≫ S.substitutionAlgebra.str) ≫ invariantMask S d =
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters
          S.substitutionParameters)
        ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
          S.substitutionParameters)).map m ≫ S.substitutionAlgebra.str) ≫ invariantResult S d := by
  apply Prod.ext
  · rfl
  · change (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
        S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
          (invariantMask S d).2 =
        (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
          S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
            (invariantResult S d).2
    dsimp only [CategoricalSyntax.substitutionAlgebra, SyntaxPolynomial.formulaExpression]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
              SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
              Category.assoc] using equality_closed S d m
          · simpa only [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, coprod.inl_map_assoc, coprod.inr_map_assoc,
              coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
                relation_closed S d m
        · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
            SyntaxPolynomial.sumFunctor, SyntaxPolynomial.parameterComparison,
            Category.assoc] using negation_closed S d m hm
      · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
          Category.assoc] using implication_closed S d m hm
    · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        SyntaxPolynomial.parameterComparison, CategoryTheory.Functor.const,
        CategoryTheory.Prod.snd, Category.assoc] using quantifier_closed S d m hm

theorem fold_invariant :
    S.substitutionFold ≫ invariantMask S d = S.substitutionFold ≫ invariantResult S d := by
  have := AlgebraInvariant.pairEqualizers (Over S.substitutionParameters)
  exact AlgebraInvariant.fold_equalizes
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
      (SyntaxPolynomial.formulaExpression V (fun _ => X) 0) S.algebra S.substitutionParameters)
    S.substitutionAlgebra (S.stable S.substitutionParameters)
    (invariantMask S d) (invariantResult S d) (constructor_closed S d)

theorem substitution_option_value :
    S.formulaSubstitutionOption ≫ OptionSyntax.map (valuation S d) =
      OptionSyntax.mask (prod.fst ≫ valuation S d) S.formulaSubstitutionOption := by
  have hg := (invariant_equation S d S.substitutionFold.2).mp
    (congrArg Prod.snd (fold_invariant S d))
  have h := pairGood_precomp S d (S.substitutionFold.2.left ≫ prod.snd) hg
    (prod.braiding S.algebra.a.2 S.substitutionParameters).hom
  dsimp only [PairGood] at h
  have ho := congrArg (fun f => f ≫ valuation S d) S.formulaSubstitution_original
  simp only [Category.assoc] at h ho
  rw [ho] at h
  simpa only [CategoricalSyntax.formulaSubstitutionOption, Category.assoc] using h

@[reassoc] theorem substitution_value :
    S.formulaSubstitution ≫ valuation S d =
      S.admissibleInclusion ≫ prod.fst ≫ valuation S d := by
  have h := congrArg (fun f => S.admissibleInclusion ≫ f) (substitution_option_value S d)
  rw [← Category.assoc, S.formulaSubstitution_square, Category.assoc,
    OptionSyntax.map_ok, OptionSyntax.mask_precomp, S.formulaSubstitution_square,
    OptionSyntax.mask_ok] at h
  exact (cancel_mono (coprod.inr : Two D ⟶ OptionSyntax.obj (Two D))).mp (by
    simpa only [Category.assoc] using h)

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
