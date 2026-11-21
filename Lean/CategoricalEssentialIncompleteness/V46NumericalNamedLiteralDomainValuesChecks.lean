/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralDomainValues


/-! # The numerical substitution domain is the independent free-for flag -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralDomainValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S" => literalCategoricalSyntax V σ π d
local notation "S₀" => literalSourceSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V

example : (S).admissibleInclusion ≫ (literalFormulaInputPresentationIso V σ π d).hom =
    (literalAdmissiblePresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).admissibleInclusion :=
  literal_admissibleInclusion_code_square V σ π d
example (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    let q₀ := (literalFormulaInputPresentationIso V σ π d).hom.toFun q
    (∃ a, (S).admissibleInclusion.toFun a = q) ↔
    ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) (NumericalCoordinates.codedPredicate V)
      (fun n => NumericalCoordinates.codedPredicate (σ n))
      (fun n => NumericalCoordinates.codedPredicate (π n)) d
      (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
      (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
      (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)) q₀).val = 1 :=
  literal_admissible_iff V σ π d q

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralDomainValuesChecks
