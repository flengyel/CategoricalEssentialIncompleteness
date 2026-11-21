/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentCore
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentConstructors

/-! The equalizer invariant is closed under every substitution constructor. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

omit [FinitaryExtensive D] in
/-- Value coordinates of a product step in the parameter slice. -/
theorem absence_product_step_value {P U W Y : D} {A B : Over P}
    (f : A ⟶ constantFamily P U) (g : B ⟶ constantFamily P W) (h : U ⨯ W ⟶ Y) :
    (prod.map f g ≫ constantProductComparison P U W ≫
      (constantFamilyFunctor P).map h).left ≫ prod.snd =
      prod.lift ((prod.fst ≫ f).left ≫ prod.snd)
        ((prod.snd ≫ g).left ≫ prod.snd) ≫ h := by
  have hv := AbsentTuples.product_comparison_value f g
  simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd] using congrArg (fun v => v ≫ h) hv

omit [FinitaryExtensive D] in
/-- A coefficient-recursion product step retains the shared parameter. -/
theorem absence_parameter_step_value {P U W Y : D} {A B : Over P}
    (f : A ⟶ constantFamily P U) (g : B ⟶ constantFamily P W)
    (h : P ⨯ (U ⨯ W) ⟶ Y) :
    (prod.map f g ≫ constantProductComparison P U W ≫ parameterHom h).left ≫ prod.snd =
      prod.lift (A ⨯ B).hom
        (prod.lift ((prod.fst ≫ f).left ≫ prod.snd)
          ((prod.snd ≫ g).left ≫ prod.snd)) ≫ h := by
  let c := prod.map f g ≫ constantProductComparison P U W
  have he : c.left = prod.lift (A ⨯ B).hom
      (prod.lift ((prod.fst ≫ f).left ≫ prod.snd)
        ((prod.snd ≫ g).left ≫ prod.snd)) := by
    apply prod.hom_ext
    · simpa only [constantFamily, Over.mk_left, Over.mk_hom, prod.lift_fst] using Over.w c
    · simpa only [c, Over.comp_left, Category.assoc, prod.lift_snd] using
        AbsentTuples.product_comparison_value f g
  simpa only [c, Over.comp_left, parameterHom, Over.homMk_left, Category.assoc,
    prod.lift_snd] using congrArg (fun k => k ≫ h) he

variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
variable {A : Over S.substitutionParameters × Over S.substitutionParameters}
variable (m : A ⟶ S.substitutionAlgebra.a)
variable (hm : m ≫ S.absenceMask = m ≫ S.absenceResult)

theorem absence_variable_closed :
    parameterHom S.variableSubstitutionPair ≫ S.absenceMask.1 =
      parameterHom S.variableSubstitutionPair ≫ S.absenceResult.1 := by
  apply (S.absence_equation_term _).mpr
  simpa only [constantFamily, Over.mk_left, Over.mk_hom, parameterHom_value, prod.lift_fst_snd, Category.id_comp] using
    S.variable_pair_good (prod.fst : S.substitutionParameters ⨯ V ⟶ _) prod.snd

include hm in
theorem absence_function_closed :
    ((SyntaxPolynomial.constructors σ d).withParameters S.substitutionParameters).eval.map m ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.functionSubstitutionPair) ≫
            S.absenceMask.1 =
      ((SyntaxPolynomial.constructors σ d).withParameters S.substitutionParameters).eval.map m ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.functionSubstitutionPair) ≫
            S.absenceResult.1 := by
  let f := m ≫ S.absenceOriginalFamilies
  let g := m ≫ S.absenceComputedFamilies
  have hc := AbsentConstructors.constructors_invariant
    (T := S.algebra.a.1) (Z := S.algebra.a.2) (U := S.algebra.a.1) (Y := S.algebra.a.1)
    A S.lists S.decidableVariables (prod.fst : S.substitutionParameters ⟶ V)
    (S.termOccurrences,S.formulaOccurrences) S.termOccurrences (𝟙 _) f g
    (S.absence_arguments_fixed m hm) σ d S.functionConstructors S.function_occurrences
  have he := AbsentConstructors.paired_step
    (B := S.substitutionCarriers) (C := S.algebra.a) A m
    S.originalProjection S.termResultProjection (SyntaxPolynomial.constructors σ d)
    S.functionConstructors (𝟙 S.algebra.a.1)
  have he' :
      ((SyntaxPolynomial.constructors σ d).withParameters S.substitutionParameters).eval.map m ≫
        SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.functionSubstitutionPair =
      AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors σ d)
        S.functionConstructors (𝟙 _) := by
    simpa only [functionSubstitutionPair, Category.comp_id,
      absenceOriginalFamilies, absenceComputedFamilies, f, g] using he
  have hc' : AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors σ d)
        S.functionConstructors (𝟙 _) ≫ S.absenceMask.1 =
      AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors σ d)
        S.functionConstructors (𝟙 _) ≫ S.absenceResult.1 := by
    simpa only [absenceMask, absenceResult] using hc
  have hl := congrArg (fun j => j ≫ S.absenceMask.1) he'
  have hr := congrArg (fun j => j ≫ S.absenceResult.1) he'
  simpa only [Category.assoc] using hl.trans (hc'.trans hr.symm)

include hm in
theorem absence_equality_closed :
    (prod.map m.1 m.1 ≫ constantProductComparison S.substitutionParameters
      S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair) ≫
          S.absenceMask.2 =
      (prod.map m.1 m.1 ≫ constantProductComparison S.substitutionParameters
        S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
          (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair) ≫
            S.absenceResult.2 := by
  apply (S.absence_equation_formula _).mpr
  rw [absence_product_step_value]
  exact S.equality_pair_good (A.1 ⨯ A.1).hom _ _
    (S.absence_recursive_term_precomp m hm prod.fst)
    (S.absence_recursive_term_precomp m hm prod.snd)

include hm in
theorem absence_relation_closed :
    ((SyntaxPolynomial.constructors π d).withParameters S.substitutionParameters).eval.map m ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors π d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair) ≫
            S.absenceMask.2 =
      ((SyntaxPolynomial.constructors π d).withParameters S.substitutionParameters).eval.map m ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors π d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair) ≫
            S.absenceResult.2 := by
  let f := m ≫ S.absenceOriginalFamilies
  let g := m ≫ S.absenceComputedFamilies
  have hc := AbsentConstructors.constructors_invariant
    (T := S.algebra.a.1) (Z := S.algebra.a.2) (U := S.algebra.a.2)
    (Y := OptionSyntax.obj S.algebra.a.2)
    A S.lists S.decidableVariables (prod.fst : S.substitutionParameters ⟶ V)
    (S.termOccurrences,S.formulaOccurrences) S.formulaOccurrences coprod.inr f g
    (S.absence_arguments_fixed m hm) π d S.relationConstructors S.relation_occurrences
  have he := AbsentConstructors.paired_step
    (B := S.substitutionCarriers) (C := S.algebra.a) A m
    S.originalProjection S.termResultProjection (SyntaxPolynomial.constructors π d)
    S.relationConstructors (coprod.inr : S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2)
  have he' :
      ((SyntaxPolynomial.constructors π d).withParameters S.substitutionParameters).eval.map m ≫
        SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors π d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair =
      AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors π d)
        S.relationConstructors coprod.inr := by
    simpa only [relationSubstitutionPair,
      absenceOriginalFamilies, absenceComputedFamilies, f, g] using he
  have hc' : AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors π d)
        S.relationConstructors coprod.inr ≫ S.absenceMask.2 =
      AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors π d)
        S.relationConstructors coprod.inr ≫ S.absenceResult.2 := by
    simpa only [absenceMask, absenceResult] using hc
  have hl := congrArg (fun j => j ≫ S.absenceMask.2) he'
  have hr := congrArg (fun j => j ≫ S.absenceResult.2) he'
  simpa only [Category.assoc] using hl.trans (hc'.trans hr.symm)

include hm in
theorem absence_negation_closed :
    (m.2 ≫ (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair) ≫
        S.absenceMask.2 =
      (m.2 ≫ (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair) ≫
        S.absenceResult.2 := by
  apply (S.absence_equation_formula _).mpr
  simpa [constantFamilyFunctor, Over.comp_left, Category.assoc] using
    S.negation_pair_good A.2.hom (m.2.left ≫ prod.snd) (S.absence_recursive_good m hm).2

include hm in
theorem absence_implication_closed :
    (prod.map m.2 m.2 ≫ constantProductComparison S.substitutionParameters
      S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair) ≫
          S.absenceMask.2 =
      (prod.map m.2 m.2 ≫ constantProductComparison S.substitutionParameters
        S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
          (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair) ≫
            S.absenceResult.2 := by
  apply (S.absence_equation_formula _).mpr
  rw [absence_product_step_value]
  exact S.implication_pair_good (A.2 ⨯ A.2).hom _ _
    (S.absence_recursive_formula_precomp m hm prod.fst)
    (S.absence_recursive_formula_precomp m hm prod.snd)

include hm in
theorem absence_quantifier_closed :
    (prod.map (𝟙 (constantFamily S.substitutionParameters V)) m.2 ≫
      constantProductComparison S.substitutionParameters V S.substitutionCarriers.2 ≫
        parameterHom S.quantifierSubstitutionPair) ≫ S.absenceMask.2 =
      (prod.map (𝟙 (constantFamily S.substitutionParameters V)) m.2 ≫
        constantProductComparison S.substitutionParameters V S.substitutionCarriers.2 ≫
          parameterHom S.quantifierSubstitutionPair) ≫ S.absenceResult.2 := by
  apply (S.absence_equation_formula _).mpr
  rw [absence_parameter_step_value]
  simpa only [Category.comp_id] using
    S.quantifier_pair_good ((constantFamily S.substitutionParameters V) ⨯ A.2).hom
      ((prod.fst : constantFamily S.substitutionParameters V ⨯ A.2 ⟶ _).left ≫ prod.snd)
      ((prod.snd ≫ m.2).left ≫ prod.snd)
      (S.absence_recursive_formula_precomp m hm prod.snd)

include hm in
/-- Constructor closure is proved for the substitution algebra, with arbitrary coefficient
objects and arbitrary parameter families. -/
theorem absence_constructor_closed :
    ((SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map m ≫
        S.substitutionAlgebra.str) ≫ S.absenceMask =
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
        ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map m ≫
          S.substitutionAlgebra.str) ≫ S.absenceResult := by
  apply Prod.ext
  · change (((SyntaxPolynomial.termExpression V σ d).withParameters
        S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.1) ≫
          S.absenceMask.1 =
        (((SyntaxPolynomial.termExpression V σ d).withParameters
          S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.1) ≫
            S.absenceResult.1
    dsimp only [substitutionAlgebra, SyntaxPolynomial.termExpression]
    apply coprod.hom_ext
    · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, CategoryTheory.Functor.const, Category.assoc] using
          S.absence_variable_closed
    · simpa only [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, coprod.inr_map_assoc, coprod.inr_desc_assoc,
        Category.assoc] using S.absence_function_closed m hm
  · change (((SyntaxPolynomial.formulaExpression V π d).withParameters
        S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
          S.absenceMask.2 =
        (((SyntaxPolynomial.formulaExpression V π d).withParameters
          S.substitutionParameters).eval.map m ≫ S.substitutionAlgebra.str.2) ≫
            S.absenceResult.2
    dsimp only [substitutionAlgebra, SyntaxPolynomial.formulaExpression]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
              SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
              Category.assoc] using S.absence_equality_closed m hm
          · simpa only [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, coprod.inl_map_assoc, coprod.inr_map_assoc,
              coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
                S.absence_relation_closed m hm
        · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
            SyntaxPolynomial.sumFunctor, SyntaxPolynomial.parameterComparison,
            Category.assoc] using S.absence_negation_closed m hm
      · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          SyntaxPolynomial.power, SyntaxPolynomial.parameterComparison,
          Category.assoc] using S.absence_implication_closed m hm
    · simpa [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        SyntaxPolynomial.parameterComparison, CategoryTheory.Functor.const,
        CategoryTheory.Prod.snd, Category.assoc] using S.absence_quantifier_closed m hm

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
