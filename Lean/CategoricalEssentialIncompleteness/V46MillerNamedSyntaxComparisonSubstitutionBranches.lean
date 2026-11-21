/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionQuantifier

/-! # Every nonquantified branch of the named substitution fold

The two recursive term results are transported separately. Formula failures
are transported by the constructed option comparison, rather than being
replaced by a total substitution operation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)

/-- Ordered binary inputs commute whenever their two coordinate squares do. -/
theorem substitution_product_square
    {X Y A B : PredicateCategory 𝗣𝗔} {X' Y' A' B' : Total.TotalCategory P}
    (k : (F).obj X ≅ X') (l : (F).obj Y ≅ Y')
    (i : (F).obj A ≅ A') (j : (F).obj B ≅ B')
    (f : X ⟶ A) (g : Y ⟶ B) (f' : X' ⟶ A') (g' : Y' ⟶ B')
    (hf : (F).map f ≫ i.hom=k.hom ≫ f')
    (hg : (F).map g ≫ j.hom=l.hom ≫ g') :
    (F).map (prod.map f g) ≫ (Options.productIso (F) i j).hom=
      (Options.productIso (F) k l).hom ≫ prod.map f' g' := by
  apply prod.hom_ext
  · simp only [Category.assoc,Options.productIso_fst (F) i j,prod.map_fst]
    rw [← Category.assoc,← CategoryTheory.Functor.map_comp,prod.map_fst,CategoryTheory.Functor.map_comp,Category.assoc,hf]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun u => u ≫ f') (Options.productIso_fst (F) k l).symm).trans
        (Category.assoc _ _ _))
  · simp only [Category.assoc,Options.productIso_snd (F) i j,prod.map_snd]
    rw [← Category.assoc,← CategoryTheory.Functor.map_comp,prod.map_snd,CategoryTheory.Functor.map_comp,Category.assoc,hg]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun u => u ≫ g') (Options.productIso_snd (F) k l).symm).trans
        (Category.assoc _ _ _))

/-- Naturality of the recursive polynomial, followed by its constructor comparison, gives
the whole substituted-constructor square. -/
theorem substitution_polynomial_constructor
    {X X0 : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    {Y Y0 : Total.TotalCategory P × Total.TotalCategory P}
    (c : (FP).obj X ≅ Y) (c0 : (FP).obj X0 ≅ Y0)
    (f : X ⟶ X0) (g : Y ⟶ Y0)
    (hc : (FP).map f ≫ c0.hom=c.hom ≫ g)
    (a : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r)
    {Z : PredicateCategory 𝗣𝗔} {Z' : Total.TotalCategory P}
    (j : (F).obj Z ≅ Z') (s : a.eval.obj X0 ⟶ Z) (t : r.eval.obj Y0 ⟶ Z')
    (hst : (F).map s ≫ j.hom=(constructorInput P X0 Y0 c0 a r ha).hom ≫ t) :
    (F).map (a.eval.map f ≫ s) ≫ j.hom=
      (constructorInput P X Y c a r ha).hom ≫ r.eval.map g ≫ t := by
  exact substitution_composite_square P
    (X := a.eval.obj X) (Y := a.eval.obj X0) (Z := Z)
    (X' := r.eval.obj Y) (Y' := r.eval.obj Y0) (Z' := Z')
    (constructorInput P X Y c a r ha) (constructorInput P X0 Y0 c0 a r ha) j
    (a.eval.map f) s (r.eval.map g) t
    (constructorInput_natural P c c0 f g hc a r ha) hst

private theorem substitution_termSquare_chart
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (k : (FP).obj X ≅ Y) :
    (constructorInput P X Y k (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)).hom =
      prodComparison (F) X.1 X.1 ≫ prod.map k.hom.1 k.hom.1 := by
  simp only [constructorInput,normalizedComponent,Syntax.Polynomial.component,
    SyntaxPolynomial.power,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,CategoryTheory.Prod.fst,
    Iso.trans_hom,prod.mapIso_hom,CategoryTheory.Functor.mapIso_hom,
    eqToIso_refl,Iso.refl_hom,asIso_hom,prod.map_id_id,Category.comp_id]

private theorem substitution_formulaSquare_chart
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (k : (FP).obj X ≅ Y) :
    (constructorInput P X Y k (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2)).hom =
      prodComparison (F) X.2 X.2 ≫ prod.map k.hom.2 k.hom.2 := by
  simp only [constructorInput,normalizedComponent,Syntax.Polynomial.component,
    SyntaxPolynomial.power,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,CategoryTheory.Prod.snd,
    Iso.trans_hom,prod.mapIso_hom,CategoryTheory.Functor.mapIso_hom,
    eqToIso_refl,Iso.refl_hom,asIso_hom,prod.map_id_id,Category.comp_id]

variable (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d
local notation "t" => Iso.symm (termIso P V σ π d)
local notation "f" => Iso.symm (formulaIso P V σ π d)
local notation "b" => substitutionParameterIso P V σ π d
local notation "c" => substitutionStateIso P V σ π d
local notation "c0" => Iso.symm (sourcePairIso P V σ π d)

def substitutionVariableInputIso :
    (F).obj ((S₀).substitutionParameters ⨯ V) ≅
      (S₁).substitutionParameters ⨯ (F).obj V :=
  Options.productIso (F) (b) (Iso.refl ((F).obj V))

theorem map_variableSubstitutionPair :
    (F).map (S₀).variableSubstitutionPair ≫
        (substitutionTermStateIso P V σ π d).hom=
      (substitutionVariableInputIso P V σ π d).hom ≫ (S₁).variableSubstitutionPair := by
  let k : (F).obj ((S₀).substitutionParameters ⨯ V) ≅
      (S₁).substitutionParameters ⨯ (F).obj V := substitutionVariableInputIso P V σ π d
  let v : (F).obj V ≅ (F).obj V := Iso.refl ((F).obj V)
  have hv : (F).map (prod.snd : (S₀).substitutionParameters ⨯ V ⟶ V) ≫ v.hom=
      k.hom ≫ prod.snd := (Options.productIso_snd (F) (b) v).symm
  have hq : (F).map ((prod.fst : (S₀).substitutionParameters ⨯ V ⟶ _) ≫ prod.fst) ≫ v.hom=
      k.hom ≫ prod.fst ≫ prod.fst := by
    simp only [k,v,substitutionVariableInputIso,substitutionParameterIso,
      Options.productIso_fst_assoc,Options.productIso_fst,← CategoryTheory.Functor.map_comp_assoc]
  have hr : (F).map ((prod.fst : (S₀).substitutionParameters ⨯ V ⟶ _) ≫ prod.snd) ≫ (t).hom=
      k.hom ≫ prod.fst ≫ prod.snd := by
    simp only [k,substitutionVariableInputIso,substitutionParameterIso,
      Options.productIso_fst_assoc,Options.productIso_snd,← CategoryTheory.Functor.map_comp_assoc]
  have he : (F).map (S₀).decidableVariables.test ≫ (Derivation.booleanIso (F)).hom=
      (Options.productIso (F) v v).hom ≫ (S₁).decidableVariables.test := by
    simp only [v,Options.productIso,Iso.trans_hom,prod.mapIso_hom,Iso.refl_hom,
      prod.map_id_id,Category.comp_id,asIso_hom]
    change (F).map (S₀).decidableVariables.test ≫ (Derivation.booleanIso (F)).hom =
      prodComparison (F) V V ≫ (Derivation.mappedEquality (F) (S₀).decidableVariables).test
    exact ListTransport.map_decidable_test (F) (S₀).decidableVariables
  have hχ := substitution_membership_square P k v v prod.snd (prod.fst ≫ prod.fst)
    prod.snd (prod.fst ≫ prod.fst) (S₀).decidableVariables.test (S₁).decidableVariables.test hv hq he
  have ho : (F).map ((prod.snd : (S₀).substitutionParameters ⨯ V ⟶ V) ≫
      (S₀).variableConstructor) ≫ (t).hom=k.hom ≫ prod.snd ≫ (S₁).variableConstructor := by
    have hc : (F).map (S₀).variableConstructor ≫ (t).hom =
        v.hom ≫ (S₁).variableConstructor := by
      simpa only [v,Iso.refl_hom,Iso.symm_hom,Category.id_comp] using variable_constructor P V σ π d
    exact substitution_composite_square P
      (X := (S₀).substitutionParameters ⨯ V) (Y := V) (Z := (S₀).algebra.a.1)
      (X' := (S₁).substitutionParameters ⨯ (F).obj V)
      (Y' := (F).obj V) (Z' := (S₁).algebra.a.1) k v (t)
      (prod.snd : (S₀).substitutionParameters ⨯ V ⟶ V) (S₀).variableConstructor
      (prod.snd : (S₁).substitutionParameters ⨯ (F).obj V ⟶ (F).obj V)
      (S₁).variableConstructor hv hc
  have hb := substitution_branch_square P k (t)
    (prod.lift (prod.snd : (S₀).substitutionParameters ⨯ V ⟶ V)
      (prod.fst ≫ prod.fst) ≫ (S₀).decidableVariables.test)
    (prod.lift (prod.snd : (S₁).substitutionParameters ⨯ (F).obj V ⟶ (F).obj V)
      (prod.fst ≫ prod.fst) ≫ (S₁).decidableVariables.test)
    (prod.snd ≫ (S₀).variableConstructor) (prod.fst ≫ prod.snd)
    (prod.snd ≫ (S₁).variableConstructor) (prod.fst ≫ prod.snd) hχ ho hr
  change (F).map (prod.lift _ _) ≫ (Options.productIso (F) (t) (t)).hom=
    k.hom ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hb

theorem map_functionSubstitutionPair :
    (F).map (S₀).functionSubstitutionPair ≫
        (substitutionTermStateIso P V σ π d).hom=
      (substitutionConstructorsInputIso P V σ π d σ).hom ≫ (S₁).functionSubstitutionPair := by
  have ho := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).originalProjection (S₁).originalProjection
    (substitutionOriginal_comparison P V σ π d)
    (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
    (t) (S₀).functionConstructors (S₁).functionConstructors (function_constructors P V σ π d)
  have hr := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).termResultProjection (S₁).termResultProjection
    (substitutionTermResult_comparison P V σ π d)
    (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
    (t) (S₀).functionConstructors (S₁).functionConstructors (function_constructors P V σ π d)
  change (F).map (prod.lift _ _) ≫ (Options.productIso (F) (t) (t)).hom=_ ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hr

theorem map_equalitySubstitutionPair :
    (F).map (S₀).equalitySubstitutionPair ≫
        (substitutionFormulaStateIso P V σ π d).hom=
      (substitutionPowerInputIso P V σ π d .term 2).hom ≫ (S₁).equalitySubstitutionPair := by
  have hc : (F).map (S₀).equalityConstructor ≫ (f).hom=
      (constructorInput P (S₀).algebra.a (S₁).algebra.a (c0)
        (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
        (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)).hom ≫
          (S₁).equalityConstructor := by
    have hi := substitution_termSquare_chart P (S₀).algebra.a (S₁).algebra.a (c0)
    exact (equality_constructor P V σ π d).trans
      (congrArg (fun u => u ≫ (S₁).equalityConstructor) hi.symm)
  have ho := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).originalProjection (S₁).originalProjection (substitutionOriginal_comparison P V σ π d)
    (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
    (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)
    (f) (S₀).equalityConstructor (S₁).equalityConstructor hc
  have hr := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).termResultProjection (S₁).termResultProjection (substitutionTermResult_comparison P V σ π d)
    (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
    (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)
    (f) (S₀).equalityConstructor (S₁).equalityConstructor hc
  have hs : (F).map ((SyntaxPolynomial.power .term 2).eval.map (S₀).termResultProjection ≫
      (S₀).equalityConstructor ≫ (coprod.inr : (S₀).algebra.a.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)) ≫
        (Options.optionIso (F) (f)).hom =
      (substitutionPowerInputIso P V σ π d .term 2).hom ≫
        (SyntaxPolynomial.power .term 2).eval.map (S₁).termResultProjection ≫
          (S₁).equalityConstructor ≫
            (coprod.inr : (S₁).algebra.a.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2) := by
    simpa only [Category.assoc] using substitution_composite_square P
      (X := (SyntaxPolynomial.power .term 2).eval.obj (S₀).substitutionCarriers)
      (Y := (S₀).algebra.a.2) (Z := OptionSyntax.obj (S₀).algebra.a.2)
      (X' := (SyntaxPolynomial.power .term 2).eval.obj (S₁).substitutionCarriers)
      (Y' := (S₁).algebra.a.2) (Z' := OptionSyntax.obj (S₁).algebra.a.2)
      (substitutionPowerInputIso P V σ π d .term 2) (f) (Options.optionIso (F) (f))
      ((SyntaxPolynomial.power .term 2).eval.map (S₀).termResultProjection ≫ (S₀).equalityConstructor)
      (coprod.inr : (S₀).algebra.a.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)
      ((SyntaxPolynomial.power .term 2).eval.map (S₁).termResultProjection ≫ (S₁).equalityConstructor)
      (coprod.inr : (S₁).algebra.a.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2)
      hr (Options.optionIso_inr (F) (f))
  change (F).map (prod.lift _ _) ≫
    (Options.productIso (F) (f) (Options.optionIso (F) (f))).hom=_ ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hs

theorem map_relationSubstitutionPair :
    (F).map (S₀).relationSubstitutionPair ≫
        (substitutionFormulaStateIso P V σ π d).hom=
      (substitutionConstructorsInputIso P V σ π d π).hom ≫ (S₁).relationSubstitutionPair := by
  have ho := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).originalProjection (S₁).originalProjection (substitutionOriginal_comparison P V σ π d)
    (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d)
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d)
    (f) (S₀).relationConstructors (S₁).relationConstructors (relation_constructors P V σ π d)
  have hr := substitution_polynomial_constructor P
    (X := (S₀).substitutionCarriers) (X0 := (S₀).algebra.a)
    (Y := (S₁).substitutionCarriers) (Y0 := (S₁).algebra.a) (c) (c0)
    (S₀).termResultProjection (S₁).termResultProjection (substitutionTermResult_comparison P V σ π d)
    (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d)
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d)
    (f) (S₀).relationConstructors (S₁).relationConstructors (relation_constructors P V σ π d)
  have hs : (F).map ((SyntaxPolynomial.constructors π d).eval.map (S₀).termResultProjection ≫
      (S₀).relationConstructors ≫ (coprod.inr : (S₀).algebra.a.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)) ≫
        (Options.optionIso (F) (f)).hom =
      (substitutionConstructorsInputIso P V σ π d π).hom ≫
        (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d).eval.map (S₁).termResultProjection ≫
          (S₁).relationConstructors ≫
            (coprod.inr : (S₁).algebra.a.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2) := by
    simpa only [Category.assoc] using substitution_composite_square P
      (X := (SyntaxPolynomial.constructors π d).eval.obj (S₀).substitutionCarriers)
      (Y := (S₀).algebra.a.2) (Z := OptionSyntax.obj (S₀).algebra.a.2)
      (X' := (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d).eval.obj (S₁).substitutionCarriers)
      (Y' := (S₁).algebra.a.2) (Z' := OptionSyntax.obj (S₁).algebra.a.2)
      (substitutionConstructorsInputIso P V σ π d π) (f) (Options.optionIso (F) (f))
      ((SyntaxPolynomial.constructors π d).eval.map (S₀).termResultProjection ≫ (S₀).relationConstructors)
      (coprod.inr : (S₀).algebra.a.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)
      ((SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d).eval.map (S₁).termResultProjection ≫
        (S₁).relationConstructors)
      (coprod.inr : (S₁).algebra.a.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2)
      hr (Options.optionIso_inr (F) (f))
  change (F).map (prod.lift _ _) ≫
    (Options.productIso (F) (f) (Options.optionIso (F) (f))).hom=_ ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hs

theorem map_negationSubstitutionPair :
    (F).map (S₀).negationSubstitutionPair ≫
        (substitutionFormulaStateIso P V σ π d).hom=
      (substitutionFormulaStateIso P V σ π d).hom ≫ (S₁).negationSubstitutionPair := by
  let o := Options.optionIso (F) (f)
  have hn := negation_constructor P V σ π d
  have ho : (F).map (prod.fst ≫ (S₀).negationConstructor) ≫ (f).hom=
      (substitutionFormulaStateIso P V σ π d).hom ≫ prod.fst ≫ (S₁).negationConstructor := by
    exact substitution_composite_square P
      (X := (S₀).substitutionCarriers.2) (Y := (S₀).algebra.a.2) (Z := (S₀).algebra.a.2)
      (X' := (S₁).substitutionCarriers.2) (Y' := (S₁).algebra.a.2) (Z' := (S₁).algebra.a.2)
      (substitutionFormulaStateIso P V σ π d) (f) (f)
      (prod.fst : (S₀).substitutionCarriers.2 ⟶ (S₀).algebra.a.2) (S₀).negationConstructor
      (prod.fst : (S₁).substitutionCarriers.2 ⟶ (S₁).algebra.a.2) (S₁).negationConstructor
      (Options.productIso_fst (F) (f) o).symm hn
  have hr : (F).map (prod.snd ≫ OptionSyntax.map (S₀).negationConstructor) ≫ o.hom=
      (substitutionFormulaStateIso P V σ π d).hom ≫ prod.snd ≫ OptionSyntax.map (S₁).negationConstructor := by
    exact substitution_composite_square P
      (X := (S₀).substitutionCarriers.2) (Y := OptionSyntax.obj (S₀).algebra.a.2)
      (Z := OptionSyntax.obj (S₀).algebra.a.2)
      (X' := (S₁).substitutionCarriers.2) (Y' := OptionSyntax.obj (S₁).algebra.a.2)
      (Z' := OptionSyntax.obj (S₁).algebra.a.2)
      (substitutionFormulaStateIso P V σ π d) o o
      (prod.snd : (S₀).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)
      (OptionSyntax.map (S₀).negationConstructor)
      (prod.snd : (S₁).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2)
      (OptionSyntax.map (S₁).negationConstructor)
      (Options.productIso_snd (F) (f) o).symm
      (Options.map_option_map (F) (f) (f) (S₀).negationConstructor (S₁).negationConstructor hn)
  change (F).map (prod.lift _ _) ≫ (Options.productIso (F) (f) o).hom=_ ≫ prod.lift _ _
  rw [Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hr

theorem map_implicationSubstitutionPair :
    (F).map (S₀).implicationSubstitutionPair ≫
        (substitutionFormulaStateIso P V σ π d).hom=
      (substitutionPowerInputIso P V σ π d .formula 2).hom ≫ (S₁).implicationSubstitutionPair := by
  let j := substitutionFormulaStateIso P V σ π d
  let o := Options.optionIso (F) (f)
  have hj : (substitutionPowerInputIso P V σ π d .formula 2).hom=
      (Options.productIso (F) j j).hom := by
    exact substitution_formulaSquare_chart P (S₀).substitutionCarriers (S₁).substitutionCarriers (c)
  have hp := substitution_product_square P j j (f) (f) prod.fst prod.fst prod.fst prod.fst
    (Options.productIso_fst (F) (f) o).symm (Options.productIso_fst (F) (f) o).symm
  have hs := substitution_product_square P j j o o prod.snd prod.snd prod.snd prod.snd
    (Options.productIso_snd (F) (f) o).symm (Options.productIso_snd (F) (f) o).symm
  have ho : (F).map (prod.map prod.fst prod.fst ≫ (S₀).implicationConstructor) ≫ (f).hom=
      (Options.productIso (F) j j).hom ≫ prod.map prod.fst prod.fst ≫ (S₁).implicationConstructor := by
    exact substitution_composite_square P
      (X := (S₀).substitutionCarriers.2 ⨯ (S₀).substitutionCarriers.2)
      (Y := (S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) (Z := (S₀).algebra.a.2)
      (X' := (S₁).substitutionCarriers.2 ⨯ (S₁).substitutionCarriers.2)
      (Y' := (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2) (Z' := (S₁).algebra.a.2)
      (Options.productIso (F) j j) (Options.productIso (F) (f) (f)) (f)
      (prod.map (prod.fst : (S₀).substitutionCarriers.2 ⟶ (S₀).algebra.a.2)
        (prod.fst : (S₀).substitutionCarriers.2 ⟶ (S₀).algebra.a.2)) (S₀).implicationConstructor
      (prod.map (prod.fst : (S₁).substitutionCarriers.2 ⟶ (S₁).algebra.a.2)
        (prod.fst : (S₁).substitutionCarriers.2 ⟶ (S₁).algebra.a.2)) (S₁).implicationConstructor
      hp (implication_constructor P V σ π d)
  have hr : (F).map (prod.map prod.snd prod.snd ≫ OptionSyntax.binary (S₀).implicationConstructor) ≫ o.hom=
      (Options.productIso (F) j j).hom ≫ prod.map prod.snd prod.snd ≫ OptionSyntax.binary (S₁).implicationConstructor := by
    exact substitution_composite_square P
      (X := (S₀).substitutionCarriers.2 ⨯ (S₀).substitutionCarriers.2)
      (Y := OptionSyntax.obj (S₀).algebra.a.2 ⨯ OptionSyntax.obj (S₀).algebra.a.2)
      (Z := OptionSyntax.obj (S₀).algebra.a.2)
      (X' := (S₁).substitutionCarriers.2 ⨯ (S₁).substitutionCarriers.2)
      (Y' := OptionSyntax.obj (S₁).algebra.a.2 ⨯ OptionSyntax.obj (S₁).algebra.a.2)
      (Z' := OptionSyntax.obj (S₁).algebra.a.2)
      (Options.productIso (F) j j) (Options.productIso (F) o o) o
      (prod.map (prod.snd : (S₀).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)
        (prod.snd : (S₀).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2))
      (OptionSyntax.binary (S₀).implicationConstructor)
      (prod.map (prod.snd : (S₁).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2)
        (prod.snd : (S₁).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₁).algebra.a.2))
      (OptionSyntax.binary (S₁).implicationConstructor) hs
      (Options.map_binary (F) (f) (f) (S₀).implicationConstructor (S₁).implicationConstructor
        (implication_constructor P V σ π d))
  change (F).map (prod.lift _ _) ≫ (Options.productIso (F) (f) o).hom=_ ≫ prod.lift _ _
  rw [hj,Options.map_lift,prod.comp_lift]
  exact congrArg₂ (fun u v => prod.lift u v) ho hr

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
