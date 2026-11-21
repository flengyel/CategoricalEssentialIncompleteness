/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeStandard
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitution
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionValues
public import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

/-! # Source PA substitution states at named points

The old standard-model algorithm determines the full option state. Uniform state
charts transport these points without changing binder names.
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

section PAValues
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d

def paParameterPoint (x : ℕ) (t : Tm) : (N).obj (S₀).substitutionParameters :=
  SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.namePoint x) (SyntacticNamedHilbert.termPoint σ π d t)

def paTermInput (x : ℕ) (t r : Tm) : (N).obj ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) :=
  SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.termPoint σ π d r) (paParameterPoint σ π d x t)

def paOptionPoint : Option Fm → (N).obj (OptionSyntax.obj (S₀).algebra.a.2)
  | none => (N).map coprod.inl (SyntacticSyntax.modelTerminalPoint 𝗣𝗔 ℕ)
  | some φ => (N).map coprod.inr (SyntacticNamedHilbert.formulaPoint σ π d φ)

theorem paOptionPoint_code (v : Option Fm) :
    ConcreteNamedComparison.optionCode 𝗣𝗔 ℕ (S₀).algebra.a.2 (paOptionPoint σ π d v)=
      NamedPostfixEncoding.optionCode v := by
  cases v with
  | none => exact ConcreteNamedComparison.optionCode_inl 𝗣𝗔 ℕ _ _
  | some φ =>
      exact (ConcreteNamedComparison.optionCode_inr 𝗣𝗔 ℕ _ _).trans
        (congrArg (fun n => Arithmetic.pair n 1) (SyntacticNamedHilbert.formulaPoint_value σ π d φ))

theorem pa_term_value (x : ℕ) (t r : Tm) :
    (N).map (S₀).termSubstitution (paTermInput σ π d x t r)=
      SyntacticNamedHilbert.termPoint σ π d (r.substitute x t) := by
  apply Subtype.ext
  have h := ConcreteNamedComparison.plain_termSubstitution_value 𝗣𝗔 (V) σ π d ℕ
    (paTermInput σ π d x t r)
  have hv : ((N).map (S₀).termSubstitution (paTermInput σ π d x t r)).val=
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) (V) σ π d x (termCode t) (termCode r) := by
    simp only [paTermInput,paParameterPoint,SyntacticLists.pairPoint_fst,SyntacticLists.pairPoint_snd,
      SyntacticNamedHilbert.termPoint_value,SyntacticNamedHilbert.namePoint] at h
    convert h using 1
    all_goals rfl
  exact hv.trans ((NamedPostfixEncoding.substitutionResult_termCode π r t x).trans
    (SyntacticNamedHilbert.termPoint_value σ π d (r.substitute x t)).symm)

/-- The old source correctness supplies the complete option output, including failure, at
the standard source input point. -/
theorem pa_formula_option_value (x : ℕ) (t : Tm) (φ : Fm) :
    (N).map (S₀).formulaSubstitutionOption (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)=
      paOptionPoint σ π d (φ.substitute x t) := by
  apply ConcreteNamedComparison.optionCode_injective 𝗣𝗔 ℕ (S₀).algebra.a.2
  have hv := ConcreteNamedComparison.plain_formulaSubstitutionOption_value 𝗣𝗔 (V) σ π d ℕ
    (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)
  have hs := SyntacticNamedHilbert.substitutionInput_scalar σ π d
    (ConcreteNamedSubstitution.substitutionResult (M := ℕ) (V) σ π d) x φ t
  exact (hv.trans hs).trans ((NamedPostfixEncoding.substitutionResult_formulaCode φ t x).trans
    (paOptionPoint_code σ π d (φ.substitute x t)).symm)

def paTermState (x : ℕ) (t r : Tm) : (N).obj (S₀).substitutionCarriers.1 :=
  (N).map ((prod.braiding (S₀).algebra.a.1 (S₀).substitutionParameters).hom ≫
    (S₀).substitutionFold.1.left ≫ prod.snd) (paTermInput σ π d x t r)

def paFormulaState (x : ℕ) (t : Tm) (φ : Fm) : (N).obj (S₀).substitutionCarriers.2 :=
  (N).map ((prod.braiding (S₀).algebra.a.2 (S₀).substitutionParameters).hom ≫
    (S₀).substitutionFold.2.left ≫ prod.snd) (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)

theorem paTermState_native (x : ℕ) (t r : Tm) :
    paTermState σ π d x t r=SyntacticLists.pairPoint 𝗣𝗔 ℕ
      (SyntacticNamedHilbert.termPoint σ π d r) (SyntacticNamedHilbert.termPoint σ π d (r.substitute x t)) := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · have h := congrArg (fun f => (N).map f (paTermInput σ π d x t r)) (S₀).termSubstitution_original
    simp only [Functor.map_comp_apply] at h
    have hp : (N).map (prod.fst : (S₀).substitutionCarriers.1 ⟶ (S₀).algebra.a.1)
        (paTermState σ π d x t r)=SyntacticNamedHilbert.termPoint σ π d r := by
      unfold paTermState
      simp only [Functor.map_comp_apply]
      exact h.trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _)
    exact hp.trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _).symm
  · have h := pa_term_value σ π d x t r
    simp only [CategoricalSyntax.termSubstitution,Functor.map_comp_apply] at h
    have hp : (N).map (prod.snd : (S₀).substitutionCarriers.1 ⟶ (S₀).algebra.a.1)
        (paTermState σ π d x t r)=SyntacticNamedHilbert.termPoint σ π d (r.substitute x t) := by
      unfold paTermState
      simp only [Functor.map_comp_apply]
      exact h
    exact hp.trans (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _).symm

theorem paFormulaState_native (x : ℕ) (t : Tm) (φ : Fm) :
    paFormulaState σ π d x t φ=SyntacticLists.pairPoint 𝗣𝗔 ℕ
      (SyntacticNamedHilbert.formulaPoint σ π d φ) (paOptionPoint σ π d (φ.substitute x t)) := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · have h := congrArg (fun f => (N).map f
      (SyntacticNamedHilbert.substitutionPoint σ π d x φ t)) (S₀).formulaSubstitution_original
    simp only [Functor.map_comp_apply] at h
    have hp : (N).map (prod.fst : (S₀).substitutionCarriers.2 ⟶ (S₀).algebra.a.2)
        (paFormulaState σ π d x t φ)=SyntacticNamedHilbert.formulaPoint σ π d φ := by
      unfold paFormulaState
      simp only [Functor.map_comp_apply]
      exact h.trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _)
    exact hp.trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _).symm
  · have h := pa_formula_option_value σ π d x t φ
    simp only [CategoricalSyntax.formulaSubstitutionOption,Functor.map_comp_apply] at h
    have hp : (N).map (prod.snd : (S₀).substitutionCarriers.2 ⟶ OptionSyntax.obj (S₀).algebra.a.2)
        (paFormulaState σ π d x t φ)=paOptionPoint σ π d (φ.substitute x t) := by
      unfold paFormulaState
      simp only [Functor.map_comp_apply]
      exact h
    exact hp.trans (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _).symm

end PAValues

section SourceNodes
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d
local notation "a" => SyntaxPolynomial.termExpression (D := PredicateCategory 𝗣𝗔)
  (variableCarrier : PredicateCategory 𝗣𝗔) (σ : ℕ → PredicateCategory 𝗣𝗔) d
local notation "b" => SyntaxPolynomial.formulaExpression (D := PredicateCategory 𝗣𝗔)
  (variableCarrier : PredicateCategory 𝗣𝗔) (π : ℕ → PredicateCategory 𝗣𝗔) d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "A₀" => SyntaxPolynomial.algebraWithParameters (D := PredicateCategory 𝗣𝗔) a b
  (CategoricalSyntax.algebra (NamedSyntaxComparison.sourceSyntax
    (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)) R₀

def paTermNodeData : Tm → Standard.Data (S₀).algebra.a (a)
  | .var x => .inl (SyntacticNamedHilbert.namePoint x)
  | .app k c children => .inr (Standard.arityData (S₀).algebra.a σ d k c
      (fun i => SyntacticNamedHilbert.termPoint σ π d (children i)))

def paFormulaNodeData : Fm → Standard.Data (S₀).algebra.a (b)
  | .equal u v => .inl (.inl (.inl (.inl
      (SyntacticNamedHilbert.termPoint σ π d u,SyntacticNamedHilbert.termPoint σ π d v))))
  | .relation k c children => .inl (.inl (.inl (.inr
      (Standard.arityData (S₀).algebra.a π d k c
        (fun i => SyntacticNamedHilbert.termPoint σ π d (children i))))))
  | .neg body => .inl (.inl (.inr (SyntacticNamedHilbert.formulaPoint σ π d body)))
  | .imp left right => .inl (.inr
      (SyntacticNamedHilbert.formulaPoint σ π d left,SyntacticNamedHilbert.formulaPoint σ π d right))
  | .all x body => .inr (SyntacticNamedHilbert.namePoint x,SyntacticNamedHilbert.formulaPoint σ π d body)

private theorem paTermNodeData_code (t : Tm) :
    SyntacticSyntax.Coding.constructor false (a)
      (Standard.rawCode (S₀).algebra.a (a) (paTermNodeData σ π d t))=termCode t := by
  cases t with
  | var x => rfl
  | app k c children =>
      simp only [paTermNodeData, SyntaxPolynomial.termExpression, Standard.rawCode,
        Standard.arityData_rawCode, SyntacticNamedHilbert.termPoint_value, termCode]
      rfl

private theorem paFormulaNodeData_code (φ : Fm) :
    SyntacticSyntax.Coding.constructor true (b)
      (Standard.rawCode (S₀).algebra.a (b) (paFormulaNodeData σ π d φ))=formulaCode φ := by
  cases φ with
  | equal u v =>
      simp only [paFormulaNodeData,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,Standard.rawCode,SyntacticNamedHilbert.termPoint_value,
        formulaCode,equalInput]
      rfl
  | relation k c children =>
      simp only [paFormulaNodeData,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,Standard.rawCode,Standard.arityData_rawCode,
        SyntacticNamedHilbert.termPoint_value,formulaCode,relationInput]
      rfl
  | neg body =>
      simp only [paFormulaNodeData,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,Standard.rawCode,SyntacticNamedHilbert.formulaPoint_value,
        formulaCode,negInput]
      rfl
  | imp left right =>
      simp only [paFormulaNodeData,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,Standard.rawCode,SyntacticNamedHilbert.formulaPoint_value,
        formulaCode,impInput]
      rfl
  | all x body =>
      simp only [paFormulaNodeData,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,Standard.rawCode,SyntacticNamedHilbert.formulaPoint_value,
        SyntacticNamedHilbert.namePoint,formulaCode,allInput]
      rfl

theorem pa_term_node_base (t : Tm) :
    (N).map (S₀).algebra.str.1 (Standard.realize (S₀).algebra.a (a) (paTermNodeData σ π d t))=
      SyntacticNamedHilbert.termPoint σ π d t := by
  apply Subtype.ext
  have h := NamedPlainConstructorModels.plainTerm_value 𝗣𝗔 ℕ (a) (b)
    (Standard.rawCode (S₀).algebra.a (a) (paTermNodeData σ π d t))
    (Standard.realize (S₀).algebra.a (a) (paTermNodeData σ π d t))
    (Standard.rawCode_represents (S₀).algebra.a (a) (paTermNodeData σ π d t))
  exact h.trans ((paTermNodeData_code σ π d t).trans (SyntacticNamedHilbert.termPoint_value σ π d t).symm)

theorem pa_formula_node_base (φ : Fm) :
    (N).map (S₀).algebra.str.2 (Standard.realize (S₀).algebra.a (b) (paFormulaNodeData σ π d φ))=
      SyntacticNamedHilbert.formulaPoint σ π d φ := by
  apply Subtype.ext
  have h := NamedPlainConstructorModels.plainFormula_value 𝗣𝗔 ℕ (a) (b)
    (Standard.rawCode (S₀).algebra.a (b) (paFormulaNodeData σ π d φ))
    (Standard.realize (S₀).algebra.a (b) (paFormulaNodeData σ π d φ))
    (Standard.rawCode_represents (S₀).algebra.a (b) (paFormulaNodeData σ π d φ))
  exact h.trans ((paFormulaNodeData_code σ π d φ).trans (SyntacticNamedHilbert.formulaPoint_value σ π d φ).symm)

theorem pa_term_node_realizes (r₀ : (N).obj (R₀)) (t : Tm) :
    (N).map (A₀).str.1.left
      (Standard.liftData (R₀) r₀ (S₀).algebra.a (a) (paTermNodeData σ π d t)).val=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (SyntacticNamedHilbert.termPoint σ π d t) := by
  change (N).map ((SyntaxPolynomial.parameterComparison (R₀) (S₀).algebra.a (a) ≫
    (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).algebra.str.1).left) _=_
  rw [Over.comp_left,Functor.map_comp_apply,Standard.liftData_comparison]
  change (N).map (prod.map (𝟙 (R₀)) (S₀).algebra.str.1) _=_
  rw [Standard.map_pair,Functor.map_id_apply,pa_term_node_base]

theorem pa_formula_node_realizes (r₀ : (N).obj (R₀)) (φ : Fm) :
    (N).map (A₀).str.2.left
      (Standard.liftData (R₀) r₀ (S₀).algebra.a (b) (paFormulaNodeData σ π d φ)).val=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ r₀ (SyntacticNamedHilbert.formulaPoint σ π d φ) := by
  change (N).map ((SyntaxPolynomial.parameterComparison (R₀) (S₀).algebra.a (b) ≫
    (constantFamilyFunctor (D := PredicateCategory 𝗣𝗔) (R₀)).map (S₀).algebra.str.2).left) _=_
  rw [Over.comp_left,Functor.map_comp_apply,Standard.liftData_comparison]
  change (N).map (prod.map (𝟙 (R₀)) (S₀).algebra.str.2) _=_
  rw [Standard.map_pair,Functor.map_id_apply,pa_formula_node_base]

theorem paTermState_leaf (x : ℕ) (t r : Tm) :
    Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1
      (SyntacticNamedHilbert.termPoint σ π d r)=paTermState σ π d x t r := by
  simp only [Standard.leafValue,paTermState,paTermInput,Functor.map_comp_apply,Standard.braid_pair]
  rfl

theorem paFormulaState_leaf (x : ℕ) (t : Tm) (φ : Fm) :
    Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2
      (SyntacticNamedHilbert.formulaPoint σ π d φ)=paFormulaState σ π d x t φ := by
  simp only [Standard.leafValue,paFormulaState,SyntacticNamedHilbert.substitutionPoint,
    paParameterPoint,Functor.map_comp_apply,Standard.braid_pair]
  rfl

theorem paTermState_step (x : ℕ) (t r : Tm) :
    paTermState σ π d x t r=
      (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _)
        ((N).map (S₀).substitutionAlgebra.str.1.left
          (Standard.liftData (R₀) (paParameterPoint σ π d x t) (S₀).substitutionCarriers (a)
            (Standard.mapData
              (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
              (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
              (a) (paTermNodeData σ π d r))).val) := by
  let z := Standard.liftData (R₀) (paParameterPoint σ π d x t) (S₀).algebra.a (a) (paTermNodeData σ π d r)
  have h := congrArg (fun k => (N).map k.1.left z.val) (S₀).substitutionFold_commutes
  change (N).map ((((a).withParameters (R₀)).eval.map (S₀).substitutionFold).left ≫
      (S₀).substitutionAlgebra.str.1.left) z.val=
    (N).map ((A₀).str.1.left ≫ (S₀).substitutionFold.1.left) z.val at h
  simp only [Functor.map_comp_apply] at h
  have hn := Standard.liftData_natural (paParameterPoint σ π d x t)
    (S₀).substitutionFold (a) (paTermNodeData σ π d r)
  have hs := congrArg ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _)) h.symm
  dsimp only [z] at hs
  have hl := congrArg (fun w =>
    (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _)
      ((N).map (S₀).substitutionFold.1.left w))
        (pa_term_node_realizes σ π d (paParameterPoint σ π d x t) r)
  have hr := congrArg (fun w =>
    (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.1 ⟶ _)
      ((N).map (S₀).substitutionAlgebra.str.1.left w)) hn
  exact (paTermState_leaf σ π d x t r).symm.trans
    (hl.symm.trans (hs.trans hr))

theorem paFormulaState_step (x : ℕ) (t : Tm) (φ : Fm) :
    paFormulaState σ π d x t φ=
      (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)
        ((N).map (S₀).substitutionAlgebra.str.2.left
          (Standard.liftData (R₀) (paParameterPoint σ π d x t) (S₀).substitutionCarriers (b)
            (Standard.mapData
              (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
              (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
              (b) (paFormulaNodeData σ π d φ))).val) := by
  let z := Standard.liftData (R₀) (paParameterPoint σ π d x t) (S₀).algebra.a (b) (paFormulaNodeData σ π d φ)
  have h := congrArg (fun k => (N).map k.2.left z.val) (S₀).substitutionFold_commutes
  change (N).map ((((b).withParameters (R₀)).eval.map (S₀).substitutionFold).left ≫
      (S₀).substitutionAlgebra.str.2.left) z.val=
    (N).map ((A₀).str.2.left ≫ (S₀).substitutionFold.2.left) z.val at h
  simp only [Functor.map_comp_apply] at h
  have hn := Standard.liftData_natural (paParameterPoint σ π d x t)
    (S₀).substitutionFold (b) (paFormulaNodeData σ π d φ)
  have hs := congrArg ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)) h.symm
  dsimp only [z] at hs
  have hl := congrArg (fun w =>
    (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)
      ((N).map (S₀).substitutionFold.2.left w))
        (pa_formula_node_realizes σ π d (paParameterPoint σ π d x t) φ)
  have hr := congrArg (fun w =>
    (N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)
      ((N).map (S₀).substitutionAlgebra.str.2.left w)) hn
  exact (paFormulaState_leaf σ π d x t φ).symm.trans
    (hl.symm.trans (hs.trans hr))

end SourceNodes

section PointCharts
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d

theorem paParameterPoint_chart (x : ℕ) (t : Tm) :
    (U).map (NamedSyntaxComparison.substitutionParameterIso P (V) σ π d).hom
      (sourcePoint P (S₀).substitutionParameters (paParameterPoint σ π d x t))=
        parameterPoint P σ π d x t := by
  exact Points.mapped_pair P (Iso.refl ((F).obj (V)))
    (NamedSyntaxComparison.termIso P (V) σ π d).symm
    (SyntacticNamedHilbert.namePoint x) (SyntacticNamedHilbert.termPoint σ π d t)

theorem paOptionPoint_chart (v : Option Fm) :
    (U).map (NamedSyntaxComparison.Options.optionIso (F)
      (NamedSyntaxComparison.formulaIso P (V) σ π d).symm).hom
        (sourcePoint P (OptionSyntax.obj (S₀).algebra.a.2) (paOptionPoint σ π d v))=
      optionPoint P σ π d v := by
  let i := (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
  cases v with
  | none =>
      let x := SyntacticSyntax.modelTerminalPoint 𝗣𝗔 ℕ
      have h := congrArg (fun f => (U).map f (sourcePoint P (⊤_ (PredicateCategory 𝗣𝗔)) x))
        (NamedSyntaxComparison.Options.optionIso_inl (F) i)
      have ht : (U).map (asIso (terminalComparison (F))).hom
          (sourcePoint P (⊤_ (PredicateCategory 𝗣𝗔)) x)=terminalPoint P :=
        terminalPoint_unique P _
      simpa only [Functor.map_comp_apply,map_sourcePoint,ht,paOptionPoint,optionPoint] using h
  | some φ =>
      have h := congrArg (fun f => (U).map f (sourceFormulaPoint P σ π d φ))
        (NamedSyntaxComparison.Options.optionIso_inr (F) i)
      simpa only [Functor.map_comp_apply,map_sourcePoint,paOptionPoint,optionPoint,
        sourceFormulaPoint,formulaPoint,i,Iso.symm_hom] using h

def expectedTermState (x : ℕ) (t r : Tm) : (U).obj (S).substitutionCarriers.1 :=
  (U).map (NamedSyntaxComparison.substitutionTermStateIso P (V) σ π d).hom
    (sourcePoint P (S₀).substitutionCarriers.1 (paTermState σ π d x t r))

def expectedFormulaState (x : ℕ) (t : Tm) (φ : Fm) : (U).obj (S).substitutionCarriers.2 :=
  (U).map (NamedSyntaxComparison.substitutionFormulaStateIso P (V) σ π d).hom
    (sourcePoint P (S₀).substitutionCarriers.2 (paFormulaState σ π d x t φ))

theorem expectedTermState_native (x : ℕ) (t r : Tm) :
    expectedTermState P σ π d x t r=Points.pairPoint (termPoint P σ π d r)
      (termPoint P σ π d (r.substitute x t)) := by
  unfold expectedTermState
  rw [paTermState_native]
  exact Points.mapped_pair P (NamedSyntaxComparison.termIso P (V) σ π d).symm
    (NamedSyntaxComparison.termIso P (V) σ π d).symm
    (SyntacticNamedHilbert.termPoint σ π d r) (SyntacticNamedHilbert.termPoint σ π d (r.substitute x t))

theorem expectedFormulaState_native (x : ℕ) (t : Tm) (φ : Fm) :
    expectedFormulaState P σ π d x t φ=Points.pairPoint (formulaPoint P σ π d φ)
      (optionPoint P σ π d (φ.substitute x t)) := by
  unfold expectedFormulaState
  rw [paFormulaState_native]
  have h := Points.mapped_pair P (NamedSyntaxComparison.formulaIso P (V) σ π d).symm
    (NamedSyntaxComparison.Options.optionIso (F) (NamedSyntaxComparison.formulaIso P (V) σ π d).symm)
    (SyntacticNamedHilbert.formulaPoint σ π d φ) (paOptionPoint σ π d (φ.substitute x t))
  exact h.trans (congrArg (Points.pairPoint (formulaPoint P σ π d φ))
    (paOptionPoint_chart P σ π d (φ.substitute x t)))

end PointCharts

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
