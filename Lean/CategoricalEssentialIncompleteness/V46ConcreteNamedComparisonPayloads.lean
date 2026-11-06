/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameters
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGraphs
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithmTyped

/-! # Actual parameter-slice arrows for the original and FV payload fields -/

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

inductive PayloadProjection | original | occurrences

namespace PayloadProjection

def graph : PayloadProjection → 𝚺₁.Semisentence 2
  | .original => ConcreteNamedSubstitution.originalGraph
  | .occurrences => ConcreteNamedSubstitution.occurrencesGraph

def target (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) :
    PayloadProjection → Carrier
  | .original => syntaxCarrier V σ π d formula
  | .occurrences => SyntacticLists.listCarrier V

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def value : PayloadProjection → M → M
  | .original => ConcreteNamedSubstitution.original
  | .occurrences => ConcreteNamedSubstitution.occurrences

@[simp] theorem graph_eval (k : PayloadProjection) (out payload : M) :
    k.graph.val.Evalb ![out,payload] ↔ out = k.value payload := by
  cases k <;> simp [graph,value]

/-- This uses the actually proved PA loop invariant of the algorithm.
The variable parameter may lie in any chosen predicate U. -/
theorem value_carrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (k : PayloadProjection) (formula : Bool) (x replacement word : M)
    (ht : (syntaxCarrier V σ π d false).val.Evalb ![replacement])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    (k.target V σ π d formula).val.Evalb
      ![k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d x replacement word)] := by
  have h := ConcreteNamedSubstitution.substitutionPayload_carrier V σ π d formula x replacement word ht hw
  cases formula <;> cases k
  · exact ConcreteNamedSubstitution.termPayload_original V σ π d _ h
  · exact ConcreteNamedSubstitution.termPayload_occurrences V σ π d _ h
  · exact ConcreteNamedSubstitution.formulaPayload_original V σ π d _ h
  · exact ConcreteNamedSubstitution.formulaPayload_occurrences V σ π d _ h

end Models
end PayloadProjection

/-- Input is the literal chart ((x,replacement),word); the source
predicate for x is independent of the language's variable predicate. -/
def payloadInputCarrier (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) : Carrier :=
  productCarrier (productCarrier U (syntaxCarrier V σ π d false)) (syntaxCarrier V σ π d formula)

def payloadProjectionGraph (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (k : PayloadProjection) (formula : Bool) : Graph :=
  let Tm := syntaxCarrier V σ π d false
  let C := syntaxCarrier V σ π d formula
  let P := ConcreteNamedSubstitution.substitutionPayloadGraph V σ π d
  let K := k.graph
  .mkSigma “input out. ∃ param x replacement word payload,
    !pairDef.val input param word ∧ !pairDef.val param x replacement ∧
    !U.val x ∧ !Tm.val replacement ∧ !C.val word ∧
    !P.val payload x replacement word ∧ !K.val out payload”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem payloadInputCarrier_eval (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (formula : Bool) (input : M) :
    (payloadInputCarrier U V σ π d formula).val.Evalb ![input] ↔
      ∃ x replacement word : M, input = Arithmetic.pair (Arithmetic.pair x replacement) word ∧
        U.val.Evalb ![x] ∧ (syntaxCarrier V σ π d false).val.Evalb ![replacement] ∧
          (syntaxCarrier V σ π d formula).val.Evalb ![word] := by
  rw [payloadInputCarrier,productCarrier_eval]
  constructor
  · rintro ⟨param,word,hi,hp,hw⟩
    obtain ⟨x,replacement,hparam,hx,ht⟩ := (productCarrier_eval _ _ param).mp hp
    exact ⟨x,replacement,word,by simpa only [hparam] using hi,hx,ht,hw⟩
  · rintro ⟨x,replacement,word,rfl,hx,ht,hw⟩
    exact ⟨Arithmetic.pair x replacement,word,rfl,
      (productCarrier_eval _ _ _).mpr ⟨x,replacement,rfl,hx,ht⟩,hw⟩

@[simp] theorem payloadProjectionGraph_eval (U V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (k : PayloadProjection) (formula : Bool) (input out : M) :
    (payloadProjectionGraph U V σ π d k formula).val.Evalb ![input,out] ↔
      ∃ x replacement word : M, input = Arithmetic.pair (Arithmetic.pair x replacement) word ∧
        U.val.Evalb ![x] ∧ (syntaxCarrier V σ π d false).val.Evalb ![replacement] ∧
          (syntaxCarrier V σ π d formula).val.Evalb ![word] ∧
        out = k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d x replacement word) := by
  simp [payloadProjectionGraph]

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def payloadProjectionMorphism (k : PayloadProjection) (formula : Bool) :
    GraphMorphism T (payloadInputCarrier U V σ π d formula) (k.target V σ π d formula) where
  graph := payloadProjectionGraph U V σ π d k formula
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,SyntacticPredicates.supportSentence_eval]
    intro input out h
    obtain ⟨x,replacement,word,hi,hx,ht,hw,rfl⟩ :=
      (payloadProjectionGraph_eval U V σ π d k formula input out).mp h
    exact ⟨(payloadInputCarrier_eval U V σ π d formula input).mpr
      ⟨x,replacement,word,hi,hx,ht,hw⟩,
      k.value_carrier V σ π d formula x replacement word ht hw⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,totalSentence_eval]
    intro input hi
    obtain ⟨x,replacement,word,rfl,hx,ht,hw⟩ :=
      (payloadInputCarrier_eval U V σ π d formula input).mp hi
    refine ⟨k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d x replacement word),
      (payloadProjectionGraph_eval U V σ π d k formula _ _).mpr
        ⟨x,replacement,word,rfl,hx,ht,hw,rfl⟩,?_⟩
    intro out hout
    obtain ⟨x',replacement',word',he,_,_,_,ho⟩ :=
      (payloadProjectionGraph_eval U V σ π d k formula _ out).mp hout
    obtain ⟨hp,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp hp
    exact ho

def payloadProjectionArrow (k : PayloadProjection) (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (syntaxCarrier V σ π d formula : PredicateCategory T)) (k.target V σ π d formula) :=
  parameterInput T U (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d formula) ≫
    representedArrow T (payloadProjectionMorphism T U V σ π d k formula)

/-- The parameter coordinate is retained by the actual product lift. -/
def payloadProjectionFamily (k : PayloadProjection) (formula : Bool) :
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (syntaxCarrier V σ π d formula : PredicateCategory T) ⟶
      constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (k.target V σ π d formula : PredicateCategory T) :=
  Over.homMk (prod.lift prod.fst (payloadProjectionArrow T U V σ π d k formula)) (prod.lift_fst _ _)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem payloadProjectionMorphism_value (k : PayloadProjection) (formula : Bool)
    (input : Obj T M (payloadInputCarrier U V σ π d formula)) :
    ((F T M).map (representedArrow T (payloadProjectionMorphism T U V σ π d k formula)) input).val =
      k.value (ConcreteNamedSubstitution.codedSubstitutionPayload V σ π d input.val) := by
  let out := (F T M).map (representedArrow T (payloadProjectionMorphism T U V σ π d k formula)) input
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (payloadProjectionMorphism T U V σ π d k formula) input out).mp rfl
  obtain ⟨x,replacement,word,hi,_,_,_,ho⟩ :=
    (payloadProjectionGraph_eval U V σ π d k formula input.val out.val).mp h
  simpa only [hi,ConcreteNamedSubstitution.codedSubstitutionPayload,pi₁_pair,pi₂_pair] using ho

/-- Scalar output is read through the real chosen input projections. -/
theorem payloadProjectionArrow_value (k : PayloadProjection) (formula : Bool)
    (q : Obj T M ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T))) :
    ((F T M).map (payloadProjectionArrow T U V σ π d k formula) q).val =
      k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d
        ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
          ((F T M).map prod.fst q)).val
        ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
          ((F T M).map prod.fst q)).val
        ((F T M).map prod.snd q).val) := by
  change ((F T M).map (parameterInput T U (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d formula) ≫ representedArrow T
      (payloadProjectionMorphism T U V σ π d k formula)) q).val = _
  rw [Functor.map_comp_apply]
  erw [payloadProjectionMorphism_value T U V σ π d M k formula,
    parameterInput_value T M U (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d formula)]
  simp only [ConcreteNamedSubstitution.codedSubstitutionPayload,pi₁_pair,pi₂_pair]

/-- The leaf equation required by fixed-fiber polynomial naturality:
all numeric dependence on the parameter is read from its actual point. -/
theorem payloadProjectionFamily_value (k : PayloadProjection) (formula : Bool)
    (p : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)))
    (z : Obj T M ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T)))
    (hp : (F T M).map prod.fst z = p) :
    ((F T M).map prod.snd
      ((F T M).map (payloadProjectionFamily T U V σ π d k formula).left z)).val =
      k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d
        ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) p).val
        ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) p).val
        ((F T M).map prod.snd z).val) := by
  have hs := model_lift_snd T M prod.fst (payloadProjectionArrow T U V σ π d k formula) z
  have hv := payloadProjectionArrow_value T U V σ π d M k formula z
  have hc := congrArg (fun pp : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) =>
    k.value (ConcreteNamedSubstitution.substitutionPayload V σ π d
      ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) pp).val
      ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) pp).val
      ((F T M).map prod.snd z).val)) hp
  exact (congrArg Subtype.val hs).trans (hv.trans hc)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
