/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPayloads
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptions

/-! # Typed numerical result arrows into the actual substitution state objects -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

def rawResultCarrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) : Bool → Carrier
  | false => syntaxCarrier V σ π d false
  | true => PredicateInterpretation.sumCarrier terminalCarrier (syntaxCarrier V σ π d true)

def resultGraph (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) : Graph :=
  let Tm := syntaxCarrier V σ π d false
  let C := syntaxCarrier V σ π d formula
  let R := ConcreteNamedSubstitution.substitutionResultGraph V σ π d
  .mkSigma “input out. ∃ param x replacement word,
    !pairDef.val input param word ∧ !pairDef.val param x replacement ∧
    !U.val x ∧ !Tm.val replacement ∧ !C.val word ∧ !R.val out x replacement word”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem resultGraph_eval (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (formula : Bool) (input out : M) :
    (resultGraph U V σ π d formula).val.Evalb ![input,out] ↔
      ∃ x replacement word : M, input = Arithmetic.pair (Arithmetic.pair x replacement) word ∧
        U.val.Evalb ![x] ∧ (syntaxCarrier V σ π d false).val.Evalb ![replacement] ∧
        (syntaxCarrier V σ π d formula).val.Evalb ![word] ∧
        out = ConcreteNamedSubstitution.substitutionResult V σ π d x replacement word := by
  simp [resultGraph]

theorem result_value_carrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (formula : Bool) (x replacement word : M)
    (ht : (syntaxCarrier V σ π d false).val.Evalb ![replacement])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    (rawResultCarrier V σ π d formula).val.Evalb
      ![ConcreteNamedSubstitution.substitutionResult V σ π d x replacement word] := by
  cases formula
  · exact ConcreteNamedSubstitution.substitutionResult_term V σ π d x replacement word ht hw
  · apply (PredicateInterpretation.sumCarrier_eval M terminalCarrier (syntaxCarrier V σ π d true) _).mpr
    rcases ConcreteNamedSubstitution.substitutionResult_formula V σ π d x replacement word ht hw with
      hzero | ⟨out,hout,he⟩
    · exact Or.inl ⟨0,by simp [hzero,Arithmetic.pair],(terminalCarrier_eval _).mpr rfl⟩
    · exact Or.inr ⟨out,he,hout⟩

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def resultMorphism (formula : Bool) : GraphMorphism T
    (payloadInputCarrier U V σ π d formula) (rawResultCarrier V σ π d formula) where
  graph := resultGraph U V σ π d formula
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,supportSentence_eval]
    intro input out h
    obtain ⟨x,replacement,word,hi,hx,ht,hw,rfl⟩ :=
      (resultGraph_eval U V σ π d formula input out).mp h
    exact ⟨(payloadInputCarrier_eval U V σ π d formula input).mpr
      ⟨x,replacement,word,hi,hx,ht,hw⟩,result_value_carrier V σ π d formula x replacement word ht hw⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,totalSentence_eval]
    intro input hi
    obtain ⟨x,replacement,word,rfl,hx,ht,hw⟩ :=
      (payloadInputCarrier_eval U V σ π d formula input).mp hi
    refine ⟨ConcreteNamedSubstitution.substitutionResult V σ π d x replacement word,
      (resultGraph_eval U V σ π d formula _ _).mpr
        ⟨x,replacement,word,rfl,hx,ht,hw,rfl⟩,?_⟩
    intro out hout
    obtain ⟨x',replacement',word',he,_,_,_,ho⟩ :=
      (resultGraph_eval U V σ π d formula _ out).mp hout
    obtain ⟨hp,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp hp
    exact ho

def rawResultArrow (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (syntaxCarrier V σ π d formula : PredicateCategory T)) (rawResultCarrier V σ π d formula) :=
  parameterInput T U (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d formula) ≫
    representedArrow T (resultMorphism T U V σ π d formula)

def computedTermResult :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (syntaxCarrier V σ π d false : PredicateCategory T)) (syntaxCarrier V σ π d false) :=
  rawResultArrow T U V σ π d false

def computedFormulaResult :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (syntaxCarrier V σ π d true : PredicateCategory T))
      (OptionSyntax.obj (syntaxCarrier V σ π d true : PredicateCategory T)) :=
  rawResultArrow T U V σ π d true ≫ (optionIso T (syntaxCarrier V σ π d true)).hom

/-- These two state maps retain original and result as actual chosen
products, and retain the actual parameter in the outer product. -/
def computedTermState :
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (syntaxCarrier V σ π d false : PredicateCategory T) ⟶
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      ((syntaxCarrier V σ π d false : PredicateCategory T) ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) :=
  Over.homMk (prod.lift prod.fst
    (prod.lift (payloadProjectionArrow T U V σ π d .original false)
      (computedTermResult T U V σ π d))) (prod.lift_fst _ _)

def computedFormulaState :
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (syntaxCarrier V σ π d true : PredicateCategory T) ⟶
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      ((syntaxCarrier V σ π d true : PredicateCategory T) ⨯
        OptionSyntax.obj (syntaxCarrier V σ π d true : PredicateCategory T)) :=
  Over.homMk (prod.lift prod.fst
    (prod.lift (payloadProjectionArrow T U V σ π d .original true)
      (computedFormulaResult T U V σ π d))) (prod.lift_fst _ _)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem resultMorphism_value (formula : Bool)
    (input : Obj T M (payloadInputCarrier U V σ π d formula)) :
    ((F T M).map (representedArrow T (resultMorphism T U V σ π d formula)) input).val =
      ConcreteNamedSubstitution.codedSubstitutionResult V σ π d input.val := by
  let out := (F T M).map (representedArrow T (resultMorphism T U V σ π d formula)) input
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (resultMorphism T U V σ π d formula) input out).mp rfl
  obtain ⟨x,replacement,word,hi,_,_,_,ho⟩ :=
    (resultGraph_eval U V σ π d formula input.val out.val).mp h
  simpa only [hi,ConcreteNamedSubstitution.codedSubstitutionResult,pi₁_pair,pi₂_pair] using ho

theorem rawResultArrow_value (formula : Bool)
    (q : Obj T M ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T))) :
    ((F T M).map (rawResultArrow T U V σ π d formula) q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
          ((F T M).map prod.fst q)).val
        ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
          ((F T M).map prod.fst q)).val
        ((F T M).map prod.snd q).val := by
  change ((F T M).map (parameterInput T U (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d formula) ≫ representedArrow T
      (resultMorphism T U V σ π d formula)) q).val = _
  rw [Functor.map_comp_apply]
  erw [resultMorphism_value T U V σ π d M formula,
    parameterInput_value T M U (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d formula)]
  simp only [ConcreteNamedSubstitution.codedSubstitutionResult,pi₁_pair,pi₂_pair]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem computedFormulaResult_code
    (q : Obj T M ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d true : PredicateCategory T))) :
    optionCode T M (syntaxCarrier V σ π d true)
      ((F T M).map (computedFormulaResult T U V σ π d) q) =
        ((F T M).map (rawResultArrow T U V σ π d true) q).val := by
  change optionCode T M (syntaxCarrier V σ π d true)
    ((F T M).map (rawResultArrow T U V σ π d true ≫
      (optionIso T (syntaxCarrier V σ π d true)).hom) q) = _
  rw [Functor.map_comp_apply]
  exact optionCode_hom T M (syntaxCarrier V σ π d true)
    ((F T M).map (rawResultArrow T U V σ π d true) q)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
