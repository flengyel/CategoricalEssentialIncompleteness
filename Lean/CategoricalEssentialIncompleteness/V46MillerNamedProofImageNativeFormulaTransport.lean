/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaInputs

/-! # Native formula substitution and the actual full option output

Every branch is evaluated on the existing standard PA state and then
transported by its proved morphism square. The actual slice fold is
compared by native induction. Failure remains part of the formula state.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "b" => SyntaxPolynomial.formulaExpression (variableCarrier : PredicateCategory 𝗣𝗔) π d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "c" => NamedSyntaxComparison.substitutionStateIso P (V) σ π d
local notation "e" => NamedSyntaxComparison.substitutionParameterIso P (V) σ π d
local notation "j" => NamedSyntaxComparison.substitutionFormulaStateIso P (V) σ π d

/-- Each branch uses its frozen actual state square; the quantifier
square carries its full option input, including a failed recursive child. -/
theorem formula_step_transport (r₀ : (N).obj (R₀))
    (z : Standard.Data (S₀).substitutionCarriers (b)) :
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((U).map (S).substitutionAlgebra.str.2.left
        ((U).map (PointFrame.realize (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
          (S).substitutionAlgebra.a (q)
          (formulaStateInputData P σ π d ((U).map (e).hom (sourcePoint P (R₀) r₀)) z)).left ⟨0,rfl⟩))=
      (U).map (j).hom (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)
          ((N).map (S₀).substitutionAlgebra.str.2.left
            (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers (b) z).val))) := by
  let r₁ : (U).obj (R) := (U).map (e).hom (sourcePoint P (R₀) r₀)
  let Tp0 : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.power .term 2
  let TA0 : Over (R) := (Tp0.withParameters (R)).eval.obj
    (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
  let Tp1 : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d
  let TA1 : Over (R) := (Tp1.withParameters (R)).eval.obj
    (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
  let Tp2 : SyntaxPolynomial (Total.TotalCategory P) := .formula
  let TA2 : Over (R) := (Tp2.withParameters (R)).eval.obj
    (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
  let Tp3 : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.power .formula 2
  let TA3 : Over (R) := (Tp3.withParameters (R)).eval.obj
    (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
  let Tp4 : SyntaxPolynomial (Total.TotalCategory P) := (.product (.coefficient ((F).obj (V))) .formula)
  let TA4 : Over (R) := (Tp4.withParameters (R)).eval.obj
    (constantFamily (R) (S).substitutionCarriers.1,constantFamily (R) (S).substitutionCarriers.2)
  let Tf0 : TA0 ⟶ constantFamily (R) (S).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers Tp0 ≫
    (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).equalitySubstitutionPair
  let Tf1 : TA1 ⟶ constantFamily (R) (S).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers Tp1 ≫
    (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).relationSubstitutionPair
  let Tf2 : TA2 ⟶ constantFamily (R) (S).substitutionCarriers.2 := (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).negationSubstitutionPair
  let Tf3 : TA3 ⟶ constantFamily (R) (S).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers Tp3 ≫
    (constantFamilyFunctor (D := Total.TotalCategory P) (R)).map (S).implicationSubstitutionPair
  let Tf4 : TA4 ⟶ constantFamily (R) (S).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R) (S).substitutionCarriers Tp4 ≫ parameterHom (S).quantifierSubstitutionPair
  let Bp0 : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.power .term 2
  let BA0 : Over (R₀) := (Bp0.withParameters (R₀)).eval.obj
    (constantFamily (R₀) (S₀).substitutionCarriers.1,constantFamily (R₀) (S₀).substitutionCarriers.2)
  let Bp1 : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.constructors π d
  let BA1 : Over (R₀) := (Bp1.withParameters (R₀)).eval.obj
    (constantFamily (R₀) (S₀).substitutionCarriers.1,constantFamily (R₀) (S₀).substitutionCarriers.2)
  let Bp2 : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := .formula
  let BA2 : Over (R₀) := (Bp2.withParameters (R₀)).eval.obj
    (constantFamily (R₀) (S₀).substitutionCarriers.1,constantFamily (R₀) (S₀).substitutionCarriers.2)
  let Bp3 : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.power .formula 2
  let BA3 : Over (R₀) := (Bp3.withParameters (R₀)).eval.obj
    (constantFamily (R₀) (S₀).substitutionCarriers.1,constantFamily (R₀) (S₀).substitutionCarriers.2)
  let Bp4 : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := (.product (.coefficient (V)) .formula)
  let BA4 : Over (R₀) := (Bp4.withParameters (R₀)).eval.obj
    (constantFamily (R₀) (S₀).substitutionCarriers.1,constantFamily (R₀) (S₀).substitutionCarriers.2)
  let Bf0 : BA0 ⟶ constantFamily (R₀) (S₀).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers Bp0 ≫
    (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).equalitySubstitutionPair
  let Bf1 : BA1 ⟶ constantFamily (R₀) (S₀).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers Bp1 ≫
    (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).relationSubstitutionPair
  let Bf2 : BA2 ⟶ constantFamily (R₀) (S₀).substitutionCarriers.2 := (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).negationSubstitutionPair
  let Bf3 : BA3 ⟶ constantFamily (R₀) (S₀).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers Bp3 ≫
    (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).implicationSubstitutionPair
  let Bf4 : BA4 ⟶ constantFamily (R₀) (S₀).substitutionCarriers.2 := SyntaxPolynomial.parameterComparison (R₀) (S₀).substitutionCarriers Bp4 ≫ parameterHom (S₀).quantifierSubstitutionPair
  rcases z with (((eqInput | relInput) | negInput) | impInput) | quantInput
  · have ht := Standard.pure_operation_transport_normalized P (R₀) (R) (e) r₀
      (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2) (j)
      (S₀).equalitySubstitutionPair (S).equalitySubstitutionPair
      (NamedSyntaxComparison.map_equalitySubstitutionPair P (V) σ π d) eqInput
    have hs := Standard.pure_operation_value (R₀) r₀ (S₀).substitutionCarriers
      (SyntaxPolynomial.power .term 2) (S₀).equalitySubstitutionPair eqInput
    have hsource := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2 v)) hs.symm
    have hh := ht.trans hsource
    let yt : (U).obj TA0.left := (U).map
      (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a Tp0
        (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)
        (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c) Bp0 eqInput))).left ⟨0,rfl⟩
    let ys : (N).obj BA0.left := (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers Bp0 eqInput).val
    have htarget := over_five_value (U) Tf0 Tf1 Tf2 Tf3 Tf4 (Sum.inl (Sum.inl (Sum.inl (Sum.inl (yt)))))
    have hsourceInput := over_five_value (N) Bf0 Bf1 Bf2 Bf3 Bf4 (Sum.inl (Sum.inl (Sum.inl (Sum.inl (ys)))))
    have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)) htarget
    have hsproj := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _) v))) hsourceInput
    dsimp only [Tf0,Tf1,Tf2,Tf3,Tf4,Bf0,Bf1,Bf2,Bf3,Bf4,
      Tp0,Tp1,Tp2,Tp3,Tp4,Bp0,Bp1,Bp2,Bp3,Bp4,yt,ys] at htproj hsproj
    simp only [fivePoint,overSumPoint,Sum.map,Sum.elim,Function.comp_apply,
      Over.comp_left,Functor.map_comp_apply] at htproj hsproj
    simp only [formulaStateInputData,PointFrame.realize,Standard.liftData,Standard.fiberInl,
      CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.formulaExpression,
      Over.comp_left,Functor.map_comp_apply] at hh ⊢
    convert htproj.trans (hh.trans hsproj.symm) using 1
    all_goals rfl

  · have ht := Standard.pure_operation_transport_normalized P (R₀) (R) (e) r₀
      (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d)
      (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d) (j)
      (S₀).relationSubstitutionPair (S).relationSubstitutionPair
      (NamedSyntaxComparison.map_relationSubstitutionPair P (V) σ π d) relInput
    have hs := Standard.pure_operation_value (R₀) r₀ (S₀).substitutionCarriers
      (SyntaxPolynomial.constructors π d) (S₀).relationSubstitutionPair relInput
    have hsource := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2 v)) hs.symm
    have hh := ht.trans hsource
    let yt : (U).obj TA1.left := (U).map
      (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a Tp1
        (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d)
        (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c) Bp1 relInput))).left ⟨0,rfl⟩
    let ys : (N).obj BA1.left := (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers Bp1 relInput).val
    have htarget := over_five_value (U) Tf0 Tf1 Tf2 Tf3 Tf4 (Sum.inl (Sum.inl (Sum.inl (Sum.inr (yt)))))
    have hsourceInput := over_five_value (N) Bf0 Bf1 Bf2 Bf3 Bf4 (Sum.inl (Sum.inl (Sum.inl (Sum.inr (ys)))))
    have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)) htarget
    have hsproj := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _) v))) hsourceInput
    dsimp only [Tf0,Tf1,Tf2,Tf3,Tf4,Bf0,Bf1,Bf2,Bf3,Bf4,
      Tp0,Tp1,Tp2,Tp3,Tp4,Bp0,Bp1,Bp2,Bp3,Bp4,yt,ys] at htproj hsproj
    simp only [fivePoint,overSumPoint,Sum.map,Sum.elim,Function.comp_apply,
      Over.comp_left,Functor.map_comp_apply] at htproj hsproj
    simp only [formulaStateInputData,PointFrame.realize,Standard.liftData,Standard.fiberInl,Standard.fiberInr,
      CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.formulaExpression,
      Over.comp_left,Functor.map_comp_apply] at hh ⊢
    convert htproj.trans (hh.trans hsproj.symm) using 1
    all_goals rfl

  · have hsq : (F).map (S₀).negationSubstitutionPair ≫ (j).hom=
        (NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers
          (S).substitutionCarriers (c) .formula .formula rfl).hom ≫ (S).negationSubstitutionPair := by
      rw [formula_leaf_chart]
      exact NamedSyntaxComparison.map_negationSubstitutionPair P (V) σ π d
    have ht := Standard.pure_operation_transport_normalized P (R₀) (R) (e) r₀
      (S₀).substitutionCarriers (S).substitutionCarriers (c) .formula .formula rfl (j)
      (S₀).negationSubstitutionPair (S).negationSubstitutionPair hsq negInput
    have hs := Standard.pure_operation_value (R₀) r₀ (S₀).substitutionCarriers
      .formula (S₀).negationSubstitutionPair negInput
    have hsource := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2 v)) hs.symm
    have hh := ht.trans hsource
    let yt : (U).obj TA2.left := (U).map
      (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a Tp2
        (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c) Bp2 negInput)).left ⟨0,rfl⟩
    let ys : (N).obj BA2.left := (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers Bp2 negInput).val
    have htarget := over_five_value (U) Tf0 Tf1 Tf2 Tf3 Tf4 (Sum.inl (Sum.inl (Sum.inr (yt))))
    have hsourceInput := over_five_value (N) Bf0 Bf1 Bf2 Bf3 Bf4 (Sum.inl (Sum.inl (Sum.inr (ys))))
    have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)) htarget
    have hsproj := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _) v))) hsourceInput
    dsimp only [Tf0,Tf1,Tf2,Tf3,Tf4,Bf0,Bf1,Bf2,Bf3,Bf4,
      Tp0,Tp1,Tp2,Tp3,Tp4,Bp0,Bp1,Bp2,Bp3,Bp4,yt,ys] at htproj hsproj
    simp only [fivePoint,overSumPoint,Sum.map,Sum.elim,Function.comp_apply,
      ] at htproj hsproj
    simp only [formulaStateInputData,PointFrame.realize,Standard.liftData,Standard.fiberInl,Standard.fiberInr,
      CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.parameterComparison,Standard.castFrameData,
      Category.id_comp,Over.comp_left,Functor.map_comp_apply] at hh ⊢
    convert htproj.trans (hh.trans hsproj.symm) using 1
    all_goals rfl

  · have ht := Standard.pure_operation_transport_normalized P (R₀) (R) (e) r₀
      (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2) (j)
      (S₀).implicationSubstitutionPair (S).implicationSubstitutionPair
      (NamedSyntaxComparison.map_implicationSubstitutionPair P (V) σ π d) impInput
    have hs := Standard.pure_operation_value (R₀) r₀ (S₀).substitutionCarriers
      (SyntaxPolynomial.power .formula 2) (S₀).implicationSubstitutionPair impInput
    have hsource := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2 v)) hs.symm
    have hh := ht.trans hsource
    let yt : (U).obj TA3.left := (U).map
      (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a Tp3
        (Standard.castFrameData P (SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2)
        (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c) Bp3 impInput))).left ⟨0,rfl⟩
    let ys : (N).obj BA3.left := (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers Bp3 impInput).val
    have htarget := over_five_value (U) Tf0 Tf1 Tf2 Tf3 Tf4 (Sum.inl (Sum.inr (yt)))
    have hsourceInput := over_five_value (N) Bf0 Bf1 Bf2 Bf3 Bf4 (Sum.inl (Sum.inr (ys)))
    have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)) htarget
    have hsproj := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _) v))) hsourceInput
    dsimp only [Tf0,Tf1,Tf2,Tf3,Tf4,Bf0,Bf1,Bf2,Bf3,Bf4,
      Tp0,Tp1,Tp2,Tp3,Tp4,Bp0,Bp1,Bp2,Bp3,Bp4,yt,ys] at htproj hsproj
    simp only [fivePoint,overSumPoint,Sum.map,Sum.elim,Function.comp_apply,
      Over.comp_left,Functor.map_comp_apply] at htproj hsproj
    simp only [formulaStateInputData,PointFrame.realize,Standard.liftData,Standard.fiberInl,Standard.fiberInr,
      CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.formulaExpression,
      Over.comp_left,Functor.map_comp_apply] at hh ⊢
    convert htproj.trans (hh.trans hsproj.symm) using 1
    all_goals rfl

  · have hsq : (F).map (S₀).quantifierSubstitutionPair ≫ (j).hom=
        (NamedSyntaxComparison.Options.productIso (F) (e)
          (NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers (S).substitutionCarriers (c)
            (.product (.coefficient (V)) .formula) (.product (.coefficient ((F).obj (V))) .formula) rfl)).hom ≫
          (S).quantifierSubstitutionPair := by
      rw [quantifier_input_chart]
      exact NamedSyntaxComparison.map_quantifierSubstitutionPair P (V) σ π d
    have ht := Standard.framed_operation_transport_normalized P (R₀) (R) (e) r₀
      (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (.product (.coefficient (V)) .formula) (.product (.coefficient ((F).obj (V))) .formula) rfl (j)
      (S₀).quantifierSubstitutionPair (S).quantifierSubstitutionPair hsq quantInput
    have hs := Standard.operation_value (R₀) r₀ (S₀).substitutionCarriers
      (.product (.coefficient (V)) .formula) (S₀).quantifierSubstitutionPair quantInput
    have hsource := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2 v)) hs.symm
    have hh := ht.trans hsource
    let yt : (U).obj TA4.left := (U).map
      (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a Tp4
        (Standard.mappedFrameData P (R) r₁ (S₀).substitutionCarriers (S).substitutionCarriers (c) Bp4 quantInput)).left ⟨0,rfl⟩
    let ys : (N).obj BA4.left := (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers Bp4 quantInput).val
    have htarget := over_five_value (U) Tf0 Tf1 Tf2 Tf3 Tf4 (Sum.inr (yt))
    have hsourceInput := over_five_value (N) Bf0 Bf1 Bf2 Bf3 Bf4 (Sum.inr (ys))
    have htproj := congrArg ((U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)) htarget
    have hsproj := congrArg (fun v => (U).map (j).hom
      (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _) v))) hsourceInput
    dsimp only [Tf0,Tf1,Tf2,Tf3,Tf4,Bf0,Bf1,Bf2,Bf3,Bf4,
      Tp0,Tp1,Tp2,Tp3,Tp4,Bp0,Bp1,Bp2,Bp3,Bp4,yt,ys] at htproj hsproj
    simp only [fivePoint,overSumPoint,Sum.map,Sum.elim,Function.comp_apply,
      Over.comp_left,Functor.map_comp_apply] at htproj hsproj
    simp only [formulaStateInputData,PointFrame.realize,Standard.liftData,Standard.fiberInr,
      CategoricalSyntax.substitutionAlgebra,SyntaxPolynomial.formulaExpression,
      Over.comp_left,Functor.map_comp_apply] at hh ⊢
    convert htproj.trans (hh.trans hsproj.symm) using 1
    all_goals rfl

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
