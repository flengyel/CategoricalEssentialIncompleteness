/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionValues


/-! # Statement checks in `V46NumericalArithmeticDistributionValuesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionValues.Checks
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => NumericalNamed.literalSourceSyntax V σ π d
local notation "S₁" => NumericalNamed.literalCategoricalSyntax V σ π d
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ
example (q : NumericalTuples.Point (targetBase V σ π d)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (sourceBase V σ π d) (NumericalCoordinates.codedPredicate V))
      ((basePresentation V σ π d).hom.toFun q)).val =
      NumericalTuples.code V.dimension ((prod.fst : targetBase V σ π d ⟶ V).toFun q).val :=
  base_name_value V σ π d q

example (q : NumericalTuples.Point (targetBase V σ π d)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) (S₀).algebra.a.2)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        (sourceBase V σ π d)
        (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2))
          ((basePresentation V σ π d).hom.toFun q))).val =
      ((NumericalNamed.literalFormulaPresentationIso V σ π d).hom.toFun
        ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun
          ((prod.snd : targetBase V σ π d ⟶ (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2).toFun q))).val :=
  base_formula_value V σ π d q

example (q : NumericalTuples.Point (targetBase V σ π d)) :
    let q₀ := (basePresentation V σ π d).hom.toFun q
    (∃ a, (S₁).distributionInclusion.toFun a = q) ↔
      ConcreteNamedSubstitution.member
        (((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
          (sourceBase V σ π d) (NumericalCoordinates.codedPredicate V))) q₀).val
        (ConcreteNamedSubstitution.freeVariables (M := ℕ) (NumericalCoordinates.codedPredicate V)
          (fun k => NumericalCoordinates.codedPredicate (σ k))
          (fun k => NumericalCoordinates.codedPredicate (π k)) d
          (((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
            (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) (S₀).algebra.a.2))
            (((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
              (sourceBase V σ π d)
              (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2))) q₀)).val) = 0 :=
  parameter_image_iff V σ π d q

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionValues.Checks
