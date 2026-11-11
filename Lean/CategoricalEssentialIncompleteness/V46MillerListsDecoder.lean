/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsWordCodes
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorLaws
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphsFunctor

/-! # An actual ordinary partial-recursive decoder for literal list words

The auxiliary PA algebra computes only code translations: nil is zero
and cons is the original adjoin operation. Its coefficient predicate is
the full numerical carrier. Restriction to the actual uniform coefficient
guard and both inverse equations are proved separately.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists.CodeInverse
open SyntacticPredicates SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors

def termPolynomial : SyntacticSyntax.RawPolynomial :=
  .sum .unit (.product (.coefficient Syntax.Raw.topCarrier) .term)

def projectionGraph : Graph := .mkSigma “x p. p=0”

def projection : GraphMorphism 𝗣𝗔 Syntax.Raw.topCarrier Coding.zeroCarrier where
  graph := projectionGraph
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp [models_iff,supportSentence,projectionGraph,Syntax.Raw.topCarrier,Coding.zeroCarrier]
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp [models_iff,totalSentence,projectionGraph,Syntax.Raw.topCarrier]

def termGraph : TernaryGraph := .mkSigma
  “p u value. p=0 ∧
    ((!pairDef.val u 0 0 ∧ value=0) ∨
      ∃ head tail pair, !pairDef.val pair head tail ∧ !pairDef.val u pair 1 ∧ !adjoinDef.val value head tail)”

def formulaGraph : TernaryGraph := .mkSigma “p u value. p=0 ∧ u=0 ∧ value=0”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem termGraph_eval (p u value : M) : termGraph.val.Evalb ![p,u,value] ↔
    p=0 ∧ ((u=Arithmetic.pair 0 0 ∧ value=0) ∨
      ∃ head tail : M,u=Arithmetic.pair (Arithmetic.pair head tail) 1 ∧ value=adjoin head tail) := by
  simp [termGraph]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem formulaGraph_eval (p u value : M) :
    formulaGraph.val.Evalb ![p,u,value] ↔ p=0 ∧ u=0 ∧ value=0 := by simp [formulaGraph]

theorem term_support_model (p u value : M) (h : termGraph.val.Evalb ![p,u,value]) :
    (rawFiber Coding.zeroCarrier Syntax.Raw.topCarrier Syntax.Raw.topCarrier projectionGraph projectionGraph termPolynomial).val.Evalb ![p,u] ∧
      Syntax.Raw.topCarrier.val.Evalb ![value] ∧ projectionGraph.val.Evalb ![value,p] := by
  obtain ⟨hp,h⟩ := (termGraph_eval p u value).mp h
  have hp' : Coding.zeroCarrier.val.Evalb ![p] := by simp [Coding.zeroCarrier,hp]
  refine ⟨?_,by simp [Syntax.Raw.topCarrier],by simp [projectionGraph,hp]⟩
  rcases h with ⟨rfl,_⟩ | ⟨head,tail,rfl,_⟩
  · apply (rawFiber_sum_eval _ _ _ _ _ .unit (.product (.coefficient Syntax.Raw.topCarrier) .term) p _).mpr
    exact Or.inl ⟨0,rfl,by simp [rawFiber,Coding.zeroCarrier,hp]⟩
  · apply (rawFiber_sum_eval _ _ _ _ _ .unit (.product (.coefficient Syntax.Raw.topCarrier) .term) p _).mpr
    refine Or.inr ⟨Arithmetic.pair head tail,rfl,?_⟩
    apply (rawFiber_product_eval _ _ _ _ _ (.coefficient Syntax.Raw.topCarrier) .term p _).mpr
    exact ⟨head,tail,rfl,by simp [rawFiber,Coding.zeroCarrier,Syntax.Raw.topCarrier,hp],
      by simp [rawFiber,Coding.zeroCarrier,Syntax.Raw.topCarrier,projectionGraph,hp]⟩

theorem term_total_model (p u : M)
    (h : (rawFiber Coding.zeroCarrier Syntax.Raw.topCarrier Syntax.Raw.topCarrier projectionGraph projectionGraph termPolynomial).val.Evalb ![p,u]) :
    ∃! value : M,termGraph.val.Evalb ![p,u,value] := by
  rcases (rawFiber_sum_eval _ _ _ _ _ .unit (.product (.coefficient Syntax.Raw.topCarrier) .term) p u).mp h with
    ⟨v,rfl,hv⟩ | ⟨v,rfl,hv⟩
  · have hp : p=0 ∧ v=0 := by simpa [rawFiber,Coding.zeroCarrier] using hv
    rcases hp with ⟨hp,rfl⟩
    refine ⟨0,by simp [hp],?_⟩
    intro value hvalue
    simpa [hp] using hvalue
  · obtain ⟨head,tail,rfl,hh,ht⟩ := (rawFiber_product_eval _ _ _ _ _ (.coefficient Syntax.Raw.topCarrier) .term p v).mp hv
    have hp : p=0 := by
      have hs := rawFiber_parameter Coding.zeroCarrier Syntax.Raw.topCarrier Syntax.Raw.topCarrier projectionGraph projectionGraph .term p tail ht
      simpa [Coding.zeroCarrier] using hs
    refine ⟨adjoin head tail,by simp [hp],?_⟩
    intro value hvalue
    simpa [hp] using hvalue
end Models

def algebra : SliceAlgebra 𝗣𝗔 Coding.zeroCarrier Syntax.Raw.topCarrier Syntax.Raw.topCarrier termPolynomial .unit where
  termProjection := projection
  formulaProjection := projection
  termOp := termGraph
  formulaOp := formulaGraph
  term_support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    have h := @term_support_model M _ inferInstance
    simpa [models_iff,operationSupportSentence,projection] using h
  term_total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    have h := @term_total_model M _ inferInstance
    simpa [models_iff,operationTotalSentence,projection] using h
  formula_support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp only [models_iff,operationSupportSentence,formulaGraph,rawFiber,Coding.zeroCarrier,Syntax.Raw.topCarrier,projection,projectionGraph]
    simp
    aesop
  formula_total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    simp [models_iff,operationTotalSentence,formulaGraph,rawFiber,Coding.zeroCarrier]

def morphism : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    (productCarrier Coding.zeroCarrier (Postfix.carrier false termPolynomial .unit)) Syntax.Raw.topCarrier :=
  representedArrow 𝗣𝗔 (algebra.evaluationMorphism false)

def decode (word : ℕ) : Part ℕ :=
  (NumericalArithmetic.numericalInterpretation.map morphism).restrictedProgram (Nat.pair 0 word)

theorem decode_partrec : Partrec decode :=
  (NumericalTuples.Map.restrictedProgram_partrec _).comp
    (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id).partrec

theorem graph_pair (word value : ℕ) :
    (algebra.evaluationGraph false).val.Evalb (M := ℕ) ![Nat.pair 0 word,value] ↔
      (algebra.evaluationFormula false).val.Evalb (M := ℕ) ![0,word,value] := by
  simp [SliceAlgebra.evaluationGraph,nat_pair_eq]

private theorem numericalGraph_graph {C D : PredicateCategory 𝗣𝗔}
    (g : GraphMorphism 𝗣𝗔 C D) (input output : ℕ) :
    output ∈ (NumericalArithmetic.numericalInterpretation.map (representedArrow 𝗣𝗔 g)).restrictedProgram input ↔
      g.graph.val.Evalb (M := ℕ) ![input,output] := by
  rw [NumericalTuples.Map.restrictedProgram_graph]
  constructor
  · rintro ⟨x,hx,hy⟩
    change NumericalTuples.code 1 (x.val : ℕ)=input at hx
    rw [NumericalTuples.code_one] at hx
    change NumericalTuples.code 1
      ((NumericalArithmetic.numericalInterpretation.map (representedArrow 𝗣𝗔 g)).toFun x).val=output at hy
    rw [NumericalTuples.code_one] at hy
    have hv : ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 g) x).val=output :=
      (congrArg Subtype.val (NumericalArithmetic.numericalInterpretation_value (representedArrow 𝗣𝗔 g) x)).symm.trans hy
    have hg := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ g x
      ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 g) x)).mp rfl
    simpa only [hx,hv] using hg
  · intro hg
    let x : PredicateInterpretation.Obj ℕ C := ⟨input,(g.support_model ℕ input output hg).1⟩
    let y : PredicateInterpretation.Obj ℕ D := ⟨output,(g.support_model ℕ input output hg).2⟩
    have hv : (PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 g) x=y :=
      (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ g x y).mpr hg
    refine ⟨x,?_,?_⟩
    · change NumericalTuples.code 1 input=input
      exact NumericalTuples.code_one input
    · change NumericalTuples.code 1
        ((NumericalArithmetic.numericalInterpretation.map (representedArrow 𝗣𝗔 g)).toFun x).val=output
      rw [NumericalTuples.code_one]
      exact (congrArg Subtype.val (NumericalArithmetic.numericalInterpretation_value
        (representedArrow 𝗣𝗔 g) x)).trans (congrArg Subtype.val hv)

theorem decode_graph (word value : ℕ) :
    value ∈ decode word ↔ (algebra.evaluationFormula false).val.Evalb (M := ℕ) ![0,word,value] := by
  exact (numericalGraph_graph (algebra.evaluationMorphism false) (Nat.pair 0 word) value).trans
    (graph_pair word value)

theorem decode_nil {P : Uniform.Family} (V : Total.Carrier P) : 0 ∈ decode (nilWord V) := by
  apply (decode_graph _ _).mpr
  apply algebra.evaluation_of_mapRaw false 0 (Nat.pair 0 0) (Nat.pair 0 0) 0
  · simp [termPolynomial,mapRaw,Coding.zeroCarrier,nat_pair_eq]
  · simp [algebra,nat_pair_eq]

theorem decode_cons {P : Uniform.Family} (V : Total.Carrier P) (head word value : ℕ)
    (hv : value ∈ decode word) : adjoin head value ∈ decode (consWord V head word) := by
  apply (decode_graph _ _).mpr
  apply algebra.evaluation_of_mapRaw false 0 (Nat.pair (Nat.pair head word) 1) (Nat.pair (Nat.pair head value) 1) (adjoin head value)
  · apply (mapRaw_sum_eval Coding.zeroCarrier (algebra.evaluationFormula false)
      (algebra.evaluationFormula true) .unit (.product (.coefficient Syntax.Raw.topCarrier) .term) 0 _ _).mpr
    refine Or.inr ⟨Nat.pair head word,Nat.pair head value,by simp [nat_pair_eq],by simp [nat_pair_eq],?_⟩
    apply (mapRaw_product_eval Coding.zeroCarrier (algebra.evaluationFormula false)
      (algebra.evaluationFormula true) (.coefficient Syntax.Raw.topCarrier) .term 0 _ _).mpr
    refine ⟨head,word,head,value,by simp [nat_pair_eq],by simp [nat_pair_eq],?_,?_⟩
    · simp [mapRaw,Coding.zeroCarrier,Syntax.Raw.topCarrier]
    · exact (decode_graph word value).mp hv
  · simp [algebra,nat_pair_eq]

theorem decode_wordOfList {P : Uniform.Family} (V : Total.Carrier P) (L : List ℕ) :
    pack L ∈ decode (wordOfList V L) := by
  induction L with
  | nil => exact decode_nil V
  | cons head tail ih =>
      have he : pack (head::tail)=adjoin head (pack tail) := by
        simp [pack,FiniteSigmaOne.canonical_adjoin,nat_pair_eq]
      simpa only [wordOfList_cons,he] using decode_cons V head (wordOfList V tail) (pack tail) ih

theorem decode_wordOfCode {P : Uniform.Family} (V : Total.Carrier P) (n : ℕ) :
    n ∈ decode (wordOfCode V n) := by
  simpa only [wordOfCode,pack_natToList] using decode_wordOfList V (Nat.natToList n)

end CategoricalEssentialIncompleteness.V46.Miller.Lists.CodeInverse
