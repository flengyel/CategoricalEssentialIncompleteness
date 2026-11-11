/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionQuantifier
public import CategoricalEssentialIncompleteness.V46SliceProductCoordinates

/-! # The algebra morphism induced by the substitution comparison -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

theorem atom_pair_comparison :
    prod.lift (𝟙 X) (terminal.from X) ≫ S.relationSubstitutionPair ≫
        (substitutionCarrierMap S Q f).2 = targetAtomPair Q f := by
  have ha : atomFormula S ≫ (interpretation S Q f).2 ≫
      (coprod.inr : Q.algebra.a.2 ⟶ OptionSyntax.obj Q.algebra.a.2) =
      f ≫ Q.sentenceInclusion ≫ coprod.inr := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ coprod.inr) (atom S Q f)
  have ho := atom S Q f
  dsimp only [atomFormula] at ho ha
  apply prod.hom_ext
  · simpa [CategoricalSyntax.relationSubstitutionPair, substitutionCarrierMap, targetAtomPair,
      SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
      SyntaxPolynomial.productFunctor, OptionSyntax.map, Category.assoc] using ho
  · simpa [CategoricalSyntax.relationSubstitutionPair, substitutionCarrierMap, targetAtomPair,
      SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
      SyntaxPolynomial.productFunctor, OptionSyntax.map, Category.assoc] using ha

def substitutionComparisonHom : S.substitutionAlgebra ⟶ targetSubstitutionAlgebra S Q f := by
  refine NullarySyntaxAlgebra.homOfConstructorsOfInitial
    (NullarySyntaxAlgebra.constantInitial S.substitutionParameters)
    ((constantFamilyFunctor S.substitutionParameters).map (substitutionCarrierMap S Q f).1,
      (constantFamilyFunctor S.substitutionParameters).map (substitutionCarrierMap S Q f).2)
    ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [NullarySyntaxAlgebra.variableConstructor, CategoricalSyntax.substitutionAlgebra,
      targetSubstitutionAlgebra, coprod.inl_desc]
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [parameterHom, constantFamilyFunctor, variable_pair_comparison S Q f]
  · simp only [NullarySyntaxAlgebra.equalityConstructor,
      CategoricalSyntax.substitutionAlgebra, targetSubstitutionAlgebra,
      Category.assoc, coprod.inl_desc]
    dsimp only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.power,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, CategoryTheory.Prod.fst]
    simp only [prod.map_id_id, Category.id_comp, Category.assoc]
    have hn := congrArg (fun k => k ≫ (constantFamilyFunctor S.substitutionParameters).map
      Q.equalitySubstitutionPair) (constantProductComparison_natural
        (P := S.substitutionParameters) (substitutionCarrierMap S Q f).1
        (substitutionCarrierMap S Q f).1)
    simp only [Category.assoc] at hn
    rw [hn]
    simp only [← CategoryTheory.Functor.map_comp, equality_pair_comparison S Q f]
  · simp only [NullarySyntaxAlgebra.atomConstructor, CategoricalSyntax.substitutionAlgebra,
      targetSubstitutionAlgebra, Category.assoc, coprod.inl_desc, coprod.inr_desc]
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp only [constantFamily, Over.mk_left, SyntaxPolynomial.constructors,
        SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
        Functor.const_obj_obj, prod_Hom, Functor.const_obj_map,
        SyntaxPolynomial.parameterComparison, SyntaxPolynomial.withParameters,
        constantUnitComparison, constantProductComparison, constantFamilyFunctor,
        Category.assoc, prod.lift_map_assoc, Category.comp_id, Over.comp_left,
        Over.homMk_left, prod.map_map, prod.lift_map, prod.comp_lift, Over.w, Over.mk_hom,
        prod.comp_lift_assoc, SliceProductCoordinates.lift_fst_assoc, Over.id_left,
        Category.id_comp, SliceProductCoordinates.lift_snd_assoc, terminal.comp_from,
        limit.lift_π, BinaryFan.mk_pt, BinaryFan.mk_snd, BinaryFan.mk_fst,
        limit.lift_π_assoc, pair_obj_left, prod.map_fst, prod.map_snd]
    have hp : prod.lift (prod.snd : S.substitutionParameters ⨯ X ⟶ X)
        (terminal.from (S.substitutionParameters ⨯ X)) =
        prod.snd ≫ prod.lift (𝟙 X) (terminal.from X) := by
      apply prod.hom_ext <;> simp
    rw [hp, Category.assoc, atom_pair_comparison S Q f]
  · simp only [NullarySyntaxAlgebra.negationConstructor,
      CategoricalSyntax.substitutionAlgebra, targetSubstitutionAlgebra,
      coprod.inr_desc, coprod.inl_desc]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      negation_pair_comparison S Q f]
  · simp only [NullarySyntaxAlgebra.implicationConstructor,
      CategoricalSyntax.substitutionAlgebra, targetSubstitutionAlgebra,
      Category.assoc, coprod.inr_desc, coprod.inl_desc]
    dsimp only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.power,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, CategoryTheory.Prod.snd]
    simp only [prod.map_id_id, Category.id_comp, Category.assoc]
    have hn := congrArg (fun k => k ≫ (constantFamilyFunctor S.substitutionParameters).map
      Q.implicationSubstitutionPair) (constantProductComparison_natural
        (P := S.substitutionParameters) (substitutionCarrierMap S Q f).2
        (substitutionCarrierMap S Q f).2)
    simp only [Category.assoc] at hn
    rw [hn]
    simp only [← CategoryTheory.Functor.map_comp, implication_pair_comparison S Q f]
  · simp only [NullarySyntaxAlgebra.quantifierConstructor,
      CategoricalSyntax.substitutionAlgebra, targetSubstitutionAlgebra,
      Category.assoc, coprod.inr_desc]
    dsimp only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.withParameters,
      SyntaxPolynomial.eval, CategoryTheory.Prod.snd, CategoryTheory.Functor.const]
    simp only [prod.map_id_id, Category.id_comp, Category.assoc]
    have hn := congrArg (fun k => k ≫ parameterHom (targetQuantifierPair S Q f))
      (constantProductComparison_natural (P := S.substitutionParameters)
        (𝟙 V) (substitutionCarrierMap S Q f).2)
    simp only [CategoryTheory.Functor.map_id, Category.assoc] at hn
    change prod.map (𝟙 (constantFamily S.substitutionParameters V))
        ((constantFamilyFunctor S.substitutionParameters).map (substitutionCarrierMap S Q f).2) ≫
        constantProductComparison S.substitutionParameters V Q.substitutionCarriers.2 ≫
        parameterHom (targetQuantifierPair S Q f) = _ at hn
    rw [hn]
    apply congrArg (fun k => constantProductComparison S.substitutionParameters V
      S.substitutionCarriers.2 ≫ k)
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [parameterHom, constantFamilyFunctor, targetQuantifierPair,
        quantifierInputMap, quantifier_pair_comparison S Q f, Category.comp_id]
    rfl

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
