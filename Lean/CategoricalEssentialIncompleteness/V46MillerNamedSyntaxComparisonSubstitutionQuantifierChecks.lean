import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionQuantifier
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "S₀" => NamedSyntaxComparison.sourceSyntax V σ π d
local notation "S₁" => NamedSyntaxComparison.presentedSyntax P V σ π d
example : (F).map (S₀).quantifierSubstitutionPair ≫
    (NamedSyntaxComparison.substitutionFormulaStateIso P V σ π d).hom=
      (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
        (S₁).quantifierSubstitutionPair :=
  NamedSyntaxComparison.map_quantifierSubstitutionPair P V σ π d
example : Two.fiberι (S₁).quantifierEquality true ≫ (S₁).quantifierSubstitutionResult=
    Two.fiberι (S₁).quantifierEquality true ≫ (S₁).quantifierOriginal ≫ coprod.inr :=
  NamedSyntaxComparison.equal_name_keeps_original P V σ π d


example : (F).map (S₀).quantifierEquality ≫ (Derivation.booleanIso (F)).hom =
    (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
      (S₁).quantifierEquality :=
  NamedSyntaxComparison.map_quantifierEquality P V σ π d
example : (F).map (S₀).captureAllowed ≫ (Derivation.booleanIso (F)).hom =
    (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).captureAllowed :=
  NamedSyntaxComparison.map_captureAllowed P V σ π d
example : (F).map (S₀).quantifierOriginal ≫ ((NamedSyntaxComparison.formulaIso P V σ π d).symm).hom =
    (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫ (S₁).quantifierOriginal :=
  NamedSyntaxComparison.map_quantifierOriginal P V σ π d
example : (F).map (S₀).quantifierSubstitutionResult ≫
    (NamedSyntaxComparison.Options.optionIso (F)
      ((NamedSyntaxComparison.formulaIso P V σ π d).symm)).hom =
    (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
      (S₁).quantifierSubstitutionResult :=
  NamedSyntaxComparison.map_quantifierSubstitutionResult P V σ π d

-- The recursive None value is supplied explicitly, with no success or
-- capture-avoidance assumption on the original body's recursion.
example {X : Total.TotalCategory P} (p : X ⟶ (S₁).substitutionParameters)
    (body : X ⟶ (S₁).algebra.a.2) :
    prod.lift p (prod.lift (p ≫ prod.fst)
      (prod.lift body (OptionSyntax.fail : X ⟶ OptionSyntax.obj (S₁).algebra.a.2))) ≫
        (S₁).quantifierSubstitutionResult =
      prod.lift (p ≫ prod.fst) body ≫ (S₁).quantifierConstructor ≫ coprod.inr :=
  NamedSyntaxComparison.equal_name_keeps_original_with_recursive_failure P V σ π d p body

example {X : Total.TotalCategory P}
    (k : X ⟶ (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2))
    (he : k ≫ (S₁).quantifierEquality = Two.constant X false)
    (hc : k ≫ (S₁).captureAllowed = Two.constant X true) :
    k ≫ (S₁).quantifierSubstitutionResult =
      k ≫ prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd) ≫
        OptionSyntax.coefficient (S₁).quantifierConstructor :=
  (S₁).quantifierSubstitution_distinct_allowed k he hc
example {X : Total.TotalCategory P}
    (k : X ⟶ (S₁).substitutionParameters ⨯ ((F).obj V ⨯ (S₁).substitutionCarriers.2))
    (he : k ≫ (S₁).quantifierEquality = Two.constant X false)
    (hc : k ≫ (S₁).captureAllowed = Two.constant X false) :
    k ≫ (S₁).quantifierSubstitutionResult = OptionSyntax.fail :=
  (S₁).quantifierSubstitution_distinct_capture k he hc
