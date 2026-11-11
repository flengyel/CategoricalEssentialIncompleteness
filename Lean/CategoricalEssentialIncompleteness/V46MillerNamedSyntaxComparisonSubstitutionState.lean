/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonConstructors
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptionConstructors
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportDeletion

/-! # Concrete named-substitution parameters and recursive state charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d

def substitutionParameterIso : (F).obj (S₀).substitutionParameters ≅ (S₁).substitutionParameters :=
  Options.productIso (F) (Iso.refl ((F).obj V)) (termIso P V σ π d).symm

def substitutionTermStateIso : (F).obj (S₀).substitutionCarriers.1 ≅ (S₁).substitutionCarriers.1 :=
  Options.productIso (F) (termIso P V σ π d).symm (termIso P V σ π d).symm

def substitutionFormulaStateIso : (F).obj (S₀).substitutionCarriers.2 ≅ (S₁).substitutionCarriers.2 :=
  Options.productIso (F) (formulaIso P V σ π d).symm
    (Options.optionIso (F) (formulaIso P V σ π d).symm)

def substitutionStateIso : (FP).obj (S₀).substitutionCarriers ≅ (S₁).substitutionCarriers where
  hom := ((substitutionTermStateIso P V σ π d).hom,(substitutionFormulaStateIso P V σ π d).hom)
  inv := ((substitutionTermStateIso P V σ π d).inv,(substitutionFormulaStateIso P V σ π d).inv)
  hom_inv_id := Prod.ext (Iso.hom_inv_id (substitutionTermStateIso P V σ π d))
    (Iso.hom_inv_id (substitutionFormulaStateIso P V σ π d))
  inv_hom_id := Prod.ext (Iso.inv_hom_id (substitutionTermStateIso P V σ π d))
    (Iso.inv_hom_id (substitutionFormulaStateIso P V σ π d))

theorem substitutionOriginal_comparison :
    (FP).map (S₀).originalProjection ≫ (sourcePairIso P V σ π d).inv=
      (substitutionStateIso P V σ π d).hom ≫ (S₁).originalProjection := by
  apply Prod.ext
  · change (F).map (prod.fst : (S₀).algebra.a.1 ⨯ (S₀).algebra.a.1 ⟶ (S₀).algebra.a.1) ≫
      (termIso P V σ π d).inv = (substitutionTermStateIso P V σ π d).hom ≫ prod.fst
    exact (Options.productIso_fst (F) (termIso P V σ π d).symm (termIso P V σ π d).symm).symm
  · change (F).map (prod.fst : (S₀).algebra.a.2 ⨯ OptionSyntax.obj (S₀).algebra.a.2 ⟶
      (S₀).algebra.a.2) ≫ (formulaIso P V σ π d).inv =
      (substitutionFormulaStateIso P V σ π d).hom ≫ prod.fst
    exact (Options.productIso_fst (F) (formulaIso P V σ π d).symm
      (Options.optionIso (F) (formulaIso P V σ π d).symm)).symm

theorem substitutionTermResult_comparison :
    (FP).map (S₀).termResultProjection ≫ (sourcePairIso P V σ π d).inv=
      (substitutionStateIso P V σ π d).hom ≫ (S₁).termResultProjection := by
  apply Prod.ext
  · change (F).map (prod.snd : (S₀).algebra.a.1 ⨯ (S₀).algebra.a.1 ⟶ (S₀).algebra.a.1) ≫
      (termIso P V σ π d).inv = (substitutionTermStateIso P V σ π d).hom ≫ prod.snd
    exact (Options.productIso_snd (F) (termIso P V σ π d).symm (termIso P V σ π d).symm).symm
  · change (F).map (prod.fst : (S₀).algebra.a.2 ⨯ OptionSyntax.obj (S₀).algebra.a.2 ⟶
      (S₀).algebra.a.2) ≫ (formulaIso P V σ π d).inv =
      (substitutionFormulaStateIso P V σ π d).hom ≫ prod.fst
    exact (Options.productIso_fst (F) (formulaIso P V σ π d).symm
      (Options.optionIso (F) (formulaIso P V σ π d).symm)).symm

def substitutionConstructorsInputIso (τ : ℕ → PredicateCategory 𝗣𝗔) :
    (F).obj ((SyntaxPolynomial.constructors τ d).eval.obj (S₀).substitutionCarriers) ≅
      (SyntaxPolynomial.constructors (fun n => (F).obj (τ n)) d).eval.obj (S₁).substitutionCarriers :=
  constructorInput P (S₀).substitutionCarriers (S₁).substitutionCarriers (substitutionStateIso P V σ π d)
    (SyntaxPolynomial.constructors τ d) (SyntaxPolynomial.constructors (fun n => (F).obj (τ n)) d)
      (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj τ d)

def substitutionPowerInputIso (r : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (n : ℕ) :
    (F).obj ((SyntaxPolynomial.power r n).eval.obj (S₀).substitutionCarriers) ≅
      (SyntaxPolynomial.power (r.mapCoefficients (F).obj) n).eval.obj (S₁).substitutionCarriers :=
  constructorInput P (S₀).substitutionCarriers (S₁).substitutionCarriers (substitutionStateIso P V σ π d)
    (SyntaxPolynomial.power r n) (SyntaxPolynomial.power (r.mapCoefficients (F).obj) n)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj r n)

def substitutionTermInputIso :
    (F).obj ((SyntaxPolynomial.termExpression V σ d).eval.obj (S₀).substitutionCarriers) ≅
      (SyntaxPolynomial.termExpression ((F).obj V) (fun n => (F).obj (σ n)) d).eval.obj
        (S₁).substitutionCarriers :=
  constructorInput P (S₀).substitutionCarriers (S₁).substitutionCarriers (substitutionStateIso P V σ π d)
    (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.termExpression ((F).obj V) (fun n => (F).obj (σ n)) d) (termExpression_mapped P V σ d)

def substitutionFormulaInputIso :
    (F).obj ((SyntaxPolynomial.formulaExpression V π d).eval.obj (S₀).substitutionCarriers) ≅
      (SyntaxPolynomial.formulaExpression ((F).obj V) (fun n => (F).obj (π n)) d).eval.obj
        (S₁).substitutionCarriers :=
  constructorInput P (S₀).substitutionCarriers (S₁).substitutionCarriers (substitutionStateIso P V σ π d)
    (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.formulaExpression ((F).obj V) (fun n => (F).obj (π n)) d) (formulaExpression_mapped P V π d)

def substitutionQuantifierInputIso :
    (F).obj ((S₀).substitutionParameters ⨯ (V ⨯ (S₀).substitutionCarriers.2)) ≅
      (S₁).substitutionParameters ⨯ (((F).obj V) ⨯ (S₁).substitutionCarriers.2) :=
  Options.productIso (F) (substitutionParameterIso P V σ π d)
    (Options.productIso (F) (Iso.refl ((F).obj V))
      (substitutionFormulaStateIso P V σ π d))

theorem substitutionQuantifierInput_binder :
    (substitutionQuantifierInputIso P V σ π d).hom ≫ prod.snd ≫ prod.fst =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.fst) ≫
          (Iso.refl ((F).obj V)).hom := by
  simp only [substitutionQuantifierInputIso,
    Options.productIso_snd_assoc,Options.productIso_fst,
    ← CategoryTheory.Functor.map_comp_assoc]

theorem substitutionQuantifierInput_query :
    (substitutionQuantifierInputIso P V σ π d).hom ≫ prod.fst ≫ prod.fst =
      (F).map ((prod.fst : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.fst) ≫
          (Iso.refl ((F).obj V)).hom := by
  simp only [substitutionQuantifierInputIso,substitutionParameterIso,
    Options.productIso_fst_assoc,Options.productIso_fst,
    ← CategoryTheory.Functor.map_comp_assoc]

theorem substitutionQuantifierInput_replacement :
    (substitutionQuantifierInputIso P V σ π d).hom ≫ prod.fst ≫ prod.snd =
      (F).map ((prod.fst : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.snd) ≫
          ((termIso P V σ π d).symm).hom := by
  simp only [substitutionQuantifierInputIso,substitutionParameterIso,
    Options.productIso_fst_assoc,Options.productIso_snd,
    ← CategoryTheory.Functor.map_comp_assoc]

theorem substitutionQuantifierInput_originalBody :
    (substitutionQuantifierInputIso P V σ π d).hom ≫
        prod.snd ≫ prod.snd ≫ prod.fst =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.fst) ≫
          ((formulaIso P V σ π d).symm).hom := by
  simp only [substitutionQuantifierInputIso,substitutionFormulaStateIso,
    Options.productIso_snd_assoc,Options.productIso_fst,
    ← CategoryTheory.Functor.map_comp_assoc]

theorem substitutionQuantifierInput_bodyResult :
    (substitutionQuantifierInputIso P V σ π d).hom ≫
        prod.snd ≫ prod.snd ≫ prod.snd =
      (F).map ((prod.snd : (S₀).substitutionParameters ⨯
        (V ⨯ (S₀).substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.snd) ≫
          (Options.optionIso (F) ((formulaIso P V σ π d).symm)).hom := by
  simp only [substitutionQuantifierInputIso,substitutionFormulaStateIso,
    Options.productIso_snd_assoc,Options.productIso_snd,
    ← CategoryTheory.Functor.map_comp_assoc]


end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
