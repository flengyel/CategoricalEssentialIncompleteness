/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryErasureSubstitutionInvariant

/-! # Successful substitution preserves propositional erasure -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X Y : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Y)
variable (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ D ⟶ Y)

theorem constructor_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d neg imp truth = m ≫ invariantResult S d neg imp truth) :
    ((SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters
        S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
        S.substitutionParameters)).map m ≫ S.substitutionAlgebra.str) ≫ invariantMask S d neg imp
          truth =
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters
          S.substitutionParameters)
        ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
          S.substitutionParameters)).map m ≫ S.substitutionAlgebra.str) ≫ invariantResult S d neg
            imp truth := by
  apply Prod.ext
  · rfl
  · change (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
        S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
          (invariantMask S d neg imp truth).2 =
        (((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
          S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
            (invariantResult S d neg imp truth).2
    dsimp only [CategoricalSyntax.substitutionAlgebra, SyntaxPolynomial.formulaExpression]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
              SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
              Category.assoc] using equality_closed S d neg imp truth m
          · simpa only [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, coprod.inl_map_assoc, coprod.inr_map_assoc,
              coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
                relation_closed S d neg imp truth m
        · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
            SyntaxPolynomial.sumFunctor, SyntaxPolynomial.parameterComparison,
            Category.assoc] using negation_closed S d neg imp truth m hm
      · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
          Category.assoc] using implication_closed S d neg imp truth m hm
    · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        SyntaxPolynomial.parameterComparison, CategoryTheory.Functor.const,
        CategoryTheory.Prod.snd, Category.assoc] using quantifier_closed S d neg imp truth m hm

theorem fold_invariant :
    S.substitutionFold ≫ invariantMask S d neg imp truth = S.substitutionFold ≫ invariantResult S
      d neg imp truth := by
  have := AlgebraInvariant.pairEqualizers (Over S.substitutionParameters)
  exact AlgebraInvariant.fold_equalizes
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
      (SyntaxPolynomial.formulaExpression V (fun _ => X) 0) S.algebra S.substitutionParameters)
    S.substitutionAlgebra (S.stable S.substitutionParameters)
    (invariantMask S d neg imp truth) (invariantResult S d neg imp truth) (constructor_closed S d
      neg imp truth)

theorem substitution_option_value :
    S.formulaSubstitutionOption ≫ OptionSyntax.map (erase S d neg imp truth) =
      OptionSyntax.mask (prod.fst ≫ erase S d neg imp truth) S.formulaSubstitutionOption := by
  have hg := (invariant_equation S d neg imp truth S.substitutionFold.2).mp
    (congrArg Prod.snd (fold_invariant S d neg imp truth))
  have h := pairGood_precomp S d neg imp truth (S.substitutionFold.2.left ≫ prod.snd) hg
    (prod.braiding S.algebra.a.2 S.substitutionParameters).hom
  dsimp only [PairGood] at h
  have ho := congrArg (fun f => f ≫ erase S d neg imp truth) S.formulaSubstitution_original
  simp only [Category.assoc] at h ho
  rw [ho] at h
  simpa only [CategoricalSyntax.formulaSubstitutionOption, Category.assoc] using h

@[reassoc] theorem substitution_value :
    S.formulaSubstitution ≫ erase S d neg imp truth =
      S.admissibleInclusion ≫ prod.fst ≫ erase S d neg imp truth := by
  have h := congrArg (fun f => S.admissibleInclusion ≫ f) (substitution_option_value S d neg imp
    truth)
  rw [← Category.assoc, S.formulaSubstitution_square, Category.assoc,
    OptionSyntax.map_ok, OptionSyntax.mask_precomp, S.formulaSubstitution_square,
    OptionSyntax.mask_ok] at h
  exact (cancel_mono (coprod.inr : Y ⟶ OptionSyntax.obj (Y))).mp (by
    simpa only [Category.assoc] using h)

end CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure
