/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionState


/-! # Concrete named-substitution parameters and recursive state charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "S₀" => NamedSyntaxComparison.sourceSyntax V σ π d
local notation "S₁" => NamedSyntaxComparison.presentedSyntax P V σ π d
example : (F).obj (S₀).substitutionParameters ≅ (S₁).substitutionParameters :=
  NamedSyntaxComparison.substitutionParameterIso P V σ π d
example : ((F).prod (F)).map (S₀).originalProjection ≫
    (NamedSyntaxComparison.sourcePairIso P V σ π d).inv=
      (NamedSyntaxComparison.substitutionStateIso P V σ π d).hom ≫ (S₁).originalProjection :=
  NamedSyntaxComparison.substitutionOriginal_comparison P V σ π d
example : ((F).prod (F)).map (S₀).termResultProjection ≫
    (NamedSyntaxComparison.sourcePairIso P V σ π d).inv=
      (NamedSyntaxComparison.substitutionStateIso P V σ π d).hom ≫ (S₁).termResultProjection :=
  NamedSyntaxComparison.substitutionTermResult_comparison P V σ π d


-- All five quantifier-input coordinates, including independent original
-- Body and option-valued recursive body, retain their charts.
example : (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
    prod.snd ≫ prod.fst =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ V ⨯ (S₀).substitutionCarriers.2) ≫ prod.fst) ≫
          (Iso.refl ((F).obj V)).hom :=
  NamedSyntaxComparison.substitutionQuantifierInput_binder P V σ π d
example : (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
    prod.fst ≫ prod.fst =
      (F).map ((prod.fst : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ (S₀).substitutionParameters) ≫ prod.fst) ≫
          (Iso.refl ((F).obj V)).hom :=
  NamedSyntaxComparison.substitutionQuantifierInput_query P V σ π d
example : (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
    prod.fst ≫ prod.snd =
      (F).map ((prod.fst : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ (S₀).substitutionParameters) ≫ prod.snd) ≫
          ((NamedSyntaxComparison.termIso P V σ π d).symm).hom :=
  NamedSyntaxComparison.substitutionQuantifierInput_replacement P V σ π d
example : (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
    prod.snd ≫ prod.snd ≫ prod.fst =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ V ⨯ (S₀).substitutionCarriers.2) ≫
          prod.snd ≫ prod.fst) ≫ ((NamedSyntaxComparison.formulaIso P V σ π d).symm).hom :=
  NamedSyntaxComparison.substitutionQuantifierInput_originalBody P V σ π d
example : (NamedSyntaxComparison.substitutionQuantifierInputIso P V σ π d).hom ≫
    prod.snd ≫ prod.snd ≫ prod.snd =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ V ⨯ (S₀).substitutionCarriers.2) ≫
          prod.snd ≫ prod.snd) ≫
        (NamedSyntaxComparison.Options.optionIso (F)
          ((NamedSyntaxComparison.formulaIso P V σ π d).symm)).hom :=
  NamedSyntaxComparison.substitutionQuantifierInput_bodyResult P V σ π d
