import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaTransport

/-! # Native formula substitution and the actual full option output

Every branch is evaluated on the existing standard PA state and then
transported by its proved morphism square. The actual slice fold is
compared by native induction. Failure remains part of the formula state.
-/
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

private theorem braid_point {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.braiding X Y).hom (Points.pairPoint x y)=Points.pairPoint y x := by
  apply Points.product_ext
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_fst,
      Points.pairPoint_snd,Points.pairPoint_fst]
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_snd,
      Points.pairPoint_fst,Points.pairPoint_snd]

theorem formulaState_frame_value (x : ℕ) (t : Tm) (φ : Fm) :
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((U).map (S).substitutionFold.2.left
        (Points.pairPoint (parameterPoint P σ π d x t) (formulaPoint P σ π d φ)))=
      formulaState P σ π d x t φ := by
  simp only [formulaState,formulaInput,Points.substitutionPoint,parameterPoint,
    Functor.map_comp_apply,braid_point]
  rfl

theorem formulaLeaf_fold (x : ℕ) (t : Tm) (φ : Fm) :
    formulaLeaf P σ π d (parameterPoint P σ π d x t) φ ≫ (S).substitutionFold.2=
      PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.2
        (formulaState P σ π d x t φ) := by
  exact (frame_constant_comp P (parameterPoint P σ π d x t) (S).substitutionFold.2
    (formulaPoint P σ π d φ)).trans
      (congrArg (PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.2)
        (formulaState_frame_value P σ π d x t φ))

def formulaStepValue (x : ℕ) (t : Tm)
    (z : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q)) :
    (U).obj (S).substitutionCarriers.2 :=
  (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
    ((U).map (S).substitutionAlgebra.str.2.left
      ((U).map (PointFrame.realize (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q) z).left
        ⟨0,rfl⟩))

theorem formulaState_step (x : ℕ) (t : Tm) (φ : Fm) :
    formulaState P σ π d x t φ=formulaStepValue P σ π d x t
      (PointFrame.mapData (R) (parameterPoint P σ π d x t) (S).substitutionFold (q)
        (formulaNodeInput P σ π d (parameterPoint P σ π d x t) φ)) := by
  have h := formula_root_framed P σ π d (parameterPoint P σ π d x t)
    (formulaNodeInput P σ π d (parameterPoint P σ π d x t) φ)
  rw [← Category.assoc,formula_node_realizes_hom P σ π d (parameterPoint P σ π d x t) φ] at h
  have hv := congrArg (fun k : PointFrame.source (R) (parameterPoint P σ π d x t) ⟶
      (S).substitutionAlgebra.a.2 =>
        (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
          ((U).map k.left ⟨0,rfl⟩)) h
  simp only [Over.comp_left,Functor.map_comp_apply] at hv
  have hc := congrArg (fun v =>
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((U).map (S).substitutionFold.2.left v))
    (PointFrame.constant_point (R) (parameterPoint P σ π d x t) (S).algebra.a.2 (formulaPoint P σ π d φ))
  exact (formulaState_frame_value P σ π d x t φ).symm.trans (hc.symm.trans hv)

def formulaNativeStateInputData (x : ℕ) (t : Tm) (φ : Fm) :
    PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q) :=
  formulaStateInputData P σ π d (parameterPoint P σ π d x t)
    (Standard.mapData
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
      (b) (paFormulaNodeData σ π d φ))

theorem expectedFormulaState_step (x : ℕ) (t : Tm) (φ : Fm) :
    formulaStepValue P σ π d x t (formulaNativeStateInputData P σ π d x t φ)=
      expectedFormulaState P σ π d x t φ := by
  have h := formula_step_transport P σ π d (paParameterPoint σ π d x t)
    (Standard.mapData
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
      (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
      (b) (paFormulaNodeData σ π d φ))
  have hs := congrArg (fun v => (U).map (j).hom
    (sourcePoint P (S₀).substitutionCarriers.2 v)) (paFormulaState_step σ π d x t φ).symm
  let node := Standard.mapData
    (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1)
    (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2)
    (b) (paFormulaNodeData σ π d φ)
  let evaluated (r₁ : (U).obj (R)) : (U).obj (S).substitutionCarriers.2 :=
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((U).map (S).substitutionAlgebra.str.2.left
        ((U).map (PointFrame.realize (R) r₁ (S).substitutionAlgebra.a (q)
          (formulaStateInputData P σ π d r₁ node)).left ⟨0,rfl⟩))
  have he := congrArg evaluated (paParameterPoint_chart P σ π d x t)
  exact he.symm.trans (h.trans hs)

private theorem termLeaf_native (x : ℕ) (t r : Tm) :
    termLeaf P σ π d (parameterPoint P σ π d x t) r ≫ (S).substitutionFold.1=
      PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.1
        ((U).map (NamedSyntaxComparison.substitutionTermStateIso P (V) σ π d).hom
          (sourcePoint P (S₀).substitutionCarriers.1
            (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.1
              (SyntacticNamedHilbert.termPoint σ π d r)))) := by
  rw [paTermState_leaf]
  exact (termLeaf_fold P σ π d x t r).trans
    (congrArg (PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.1)
      (termState_comparison P σ π d x t r))

private theorem formulaLeaf_native (x : ℕ) (t : Tm) (φ : Fm)
    (ih : formulaState P σ π d x t φ=expectedFormulaState P σ π d x t φ) :
    formulaLeaf P σ π d (parameterPoint P σ π d x t) φ ≫ (S).substitutionFold.2=
      PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.2
        ((U).map (j).hom (sourcePoint P (S₀).substitutionCarriers.2
          (Standard.leafValue (paParameterPoint σ π d x t) (S₀).substitutionFold.2
            (SyntacticNamedHilbert.formulaPoint σ π d φ)))) := by
  rw [paFormulaState_leaf]
  exact (formulaLeaf_fold P σ π d x t φ).trans
    (congrArg (PointFrame.constant (R) (parameterPoint P σ π d x t) (S).substitutionCarriers.2) ih)

private theorem state_of_node_data (x : ℕ) (t : Tm) (φ : Fm)
    (h : PointFrame.mapData (R) (parameterPoint P σ π d x t) (S).substitutionFold (q)
      (formulaNodeInput P σ π d (parameterPoint P σ π d x t) φ)=
        formulaNativeStateInputData P σ π d x t φ) :
    formulaState P σ π d x t φ=expectedFormulaState P σ π d x t φ :=
  (formulaState_step P σ π d x t φ).trans
    ((congrArg (formulaStepValue P σ π d x t) h).trans (expectedFormulaState_step P σ π d x t φ))

/-- Native formula induction compares the complete original/option pair.
In particular, the equal-binder branch does not require recursive success. -/
theorem formulaState_comparison (x : ℕ) (t : Tm) (φ : Fm) :
    formulaState P σ π d x t φ=expectedFormulaState P σ π d x t φ := by
  induction φ with
  | equal u v =>
      apply state_of_node_data P σ π d x t (.equal u v)
      have hh :=
          congrArg (fun z => (Sum.inl (Sum.inl (Sum.inl (Sum.inl z))) : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q)))
            (congrArg₂ Prod.mk (termLeaf_native P σ π d x t u) (termLeaf_native P σ π d x t v))
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,PointFrame.mapData,formulaNativeStateInputData,
        paFormulaNodeData,Standard.mapData,formulaStateInputData,Standard.mappedFrameData,
        Standard.castFrameData,SyntaxPolynomial.power,NamedSyntaxComparison.substitutionStateIso]
      convert hh using 1
  | relation k label children =>
      apply state_of_node_data P σ π d x t (.relation k label children)
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,PointFrame.mapData,formulaNativeStateInputData,
        paFormulaNodeData,Standard.mapData,formulaStateInputData]
      have hn := PointFrame.arityData_natural (R) (parameterPoint P σ π d x t)
        (S).substitutionFold (fun n => (F).obj (π n)) d k (sourcePoint P (π k.val) label)
        (fun i => termLeaf P σ π d (parameterPoint P σ π d x t) (children i))
      have hh := congrArg (fun z => (Sum.inl (Sum.inl (Sum.inl (Sum.inr z))) :
        PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q))) hn
      refine hh.trans ?_
      rw [Standard.mapData_arityData,Standard.mappedFrameData_arity]
      apply congrArg (fun f => Sum.inl (Sum.inl (Sum.inl (Sum.inr
        (PointFrame.arityData (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a
          (fun n => (F).obj (π n)) d k (sourcePoint P (π k.val) label) f)))))
      funext i
      exact termLeaf_native P σ π d x t (children i)
  | neg body ih =>
      apply state_of_node_data P σ π d x t (.neg body)
      have hh :=
          congrArg (fun f => (Sum.inl (Sum.inl (Sum.inr f)) : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q))) (formulaLeaf_native P σ π d x t body ih)
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,PointFrame.mapData,formulaNativeStateInputData,
        paFormulaNodeData,Standard.mapData,formulaStateInputData,Standard.mappedFrameData,
        NamedSyntaxComparison.substitutionStateIso]
      convert hh using 1
  | imp left right ihl ihr =>
      apply state_of_node_data P σ π d x t (.imp left right)
      have hh :=
          congrArg (fun z => (Sum.inl (Sum.inr z) : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q)))
            (congrArg₂ Prod.mk (formulaLeaf_native P σ π d x t left ihl)
              (formulaLeaf_native P σ π d x t right ihr))
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,PointFrame.mapData,formulaNativeStateInputData,
        paFormulaNodeData,Standard.mapData,formulaStateInputData,Standard.mappedFrameData,
        Standard.castFrameData,SyntaxPolynomial.power,NamedSyntaxComparison.substitutionStateIso]
      convert hh using 1
  | all y body ih =>
      apply state_of_node_data P σ π d x t (.all y body)
      have hh :=
          congrArg (fun f => (Sum.inr (Points.namePoint P y,f) : PointFrame.Data (R) (parameterPoint P σ π d x t) (S).substitutionAlgebra.a (q))) (formulaLeaf_native P σ π d x t body ih)
      simp only [formulaNodeInput,SyntaxPolynomial.formulaExpression,PointFrame.mapData,formulaNativeStateInputData,
        paFormulaNodeData,Standard.mapData,formulaStateInputData,Standard.mappedFrameData,
        Points.namePoint,NamedSyntaxComparison.substitutionStateIso]
      convert hh using 1
      all_goals rfl

/-- Both failure and success are compared in the actual uniform option
object, with unchanged variable names and ordered term children. -/
theorem formulaOptionValue_eq_native (x : ℕ) (t : Tm) (φ : Fm) :
    formulaOptionValue P σ π d x t φ=optionPoint P σ π d (φ.substitute x t) := by
  have h := congrArg ((U).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj (S).algebra.a.2))
    ((formulaState_comparison P σ π d x t φ).trans (expectedFormulaState_native P σ π d x t φ))
  exact (formulaState_result P σ π d x t φ).symm.trans (h.trans (Points.pairPoint_snd _ _))

theorem decodedResult_eq_substitute (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t φ=φ.substitute x t :=
  (congrArg (decodeOption P σ π d) (formulaOptionValue_eq_native P σ π d x t φ)).trans
    (decode_optionPoint P σ π d _)

theorem native_option_graph (x : ℕ) (t : Tm) (φ : Fm) (v : Option Fm) :
    (optionPoint P σ π d v).val∈Total.val (S).formulaSubstitutionOption.hom
      (Points.substitutionPoint P σ π d x φ t).val ↔ φ.substitute x t=v := by
  simpa only [decodedResult_eq_substitute,formulaInput] using option_graph P σ π d x t φ v

theorem native_substitution_instance (x : ℕ) (t : Tm) (φ ψ : Fm)
    (hs : φ.substitute x t=some ψ) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ :=
  (success_iff P σ π d x t φ ψ).mpr ((decodedResult_eq_substitute P σ π d x t φ).trans hs)

theorem native_substitution_reflection (x : ℕ) (t : Tm) (φ ψ : Fm)
    (a : (U).obj (S).admissibleSubstitution)
    (hi : (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t)
    (hr : (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ) :
    φ.FreeFor x t ∧ φ.substitute x t=some ψ := by
  have hs := (decodedResult_eq_substitute P σ π d x t φ).symm.trans
    ((success_iff P σ π d x t φ ψ).mp ⟨a,hi,hr⟩)
  refine ⟨(Formula.substitute_isSome_iff φ x t).mp ?_,hs⟩
  rw [hs]
  rfl

theorem native_freeFor_iff_success (x : ℕ) (t : Tm) (φ : Fm) :
    φ.FreeFor x t ↔ ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t := by
  constructor
  · intro hf
    have hs := (Formula.substitute_isSome_iff φ x t).mpr hf
    cases he : φ.substitute x t with
    | none =>
        rw [he] at hs
        change (false : Bool)=true at hs
        cases hs
    | some ψ =>
        obtain ⟨a,ha,_⟩ := native_substitution_instance P σ π d x t φ ψ he
        exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    let ψ := NamedProofImage.decodeFormula P σ π d ((U).map (S).formulaSubstitution a)
    exact (native_substitution_reflection P σ π d x t φ ψ a ha
      (NamedProofImage.formulaPoint_decode P σ π d _).symm).1

theorem native_failure_iff (x : ℕ) (t : Tm) (φ : Fm) :
    φ.substitute x t=none ↔
      ¬ ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t := by
  simpa only [decodedResult_eq_substitute,formulaInput] using failure_iff P σ π d x t φ

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
