/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonProjectionValues
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonResults
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationMap

/-! # Numerical payload coordinates on the substitution state objects -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section GraphValues
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem chosenGraph_value_iff {C D : PredicateCategory T} (f : C ⟶ D)
    (x : Obj T M C) (y : M) :
    (chosenGraph T f).graph.val.Evalb ![x.val,y] ↔ ((F T M).map f x).val = y := by
  have hh := (chosenGraph_map_iff T M f x ((F T M).map f x)).mpr rfl
  constructor
  · intro h
    exact graph_functional_model (chosenGraph T f) x.val _ y hh h
  · intro h
    simpa only [h] using hh

end GraphValues

variable (P V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def computationState : Bool → PredicateCategory T
  | false => (syntaxCarrier V σ π d false : PredicateCategory T) ⨯
      (syntaxCarrier V σ π d false : PredicateCategory T)
  | true => (syntaxCarrier V σ π d true : PredicateCategory T) ⨯
      OptionSyntax.obj (syntaxCarrier V σ π d true : PredicateCategory T)

def stateOriginalArrow (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance (P ⨯ computationState T V σ π d formula)
      (syntaxCarrier V σ π d formula) :=
  match formula with
  | false => prod.snd ≫ prod.fst
  | true => prod.snd ≫ prod.fst

def stateResultCodeArrow (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance (P ⨯ computationState T V σ π d formula)
      (rawResultCarrier V σ π d formula) :=
  match formula with
  | false => prod.snd ≫ prod.snd
  | true => prod.snd ≫ prod.snd ≫ (optionIso T (syntaxCarrier V σ π d true)).inv

def nativePayloadCarrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) : Bool → Carrier
  | false => ConcreteNamedSubstitution.termPayloadCarrier V σ π d
  | true => ConcreteNamedSubstitution.formulaPayloadCarrier V σ π d

/-- The FV metadata is related to the original word by the proved numerical graph. This is
a positive relation, used only in the forward polynomial chart. Its truth for computed
leaves will be derived from the two projection Homs, not assumed as an evaluator
field. -/
def stateLeaf (formula : Bool) : TernaryGraph :=
  let C := nativePayloadCarrier V σ π d formula
  let Fp := (chosenGraph T (prod.fst : P ⨯ computationState T V σ π d formula ⟶ P)).graph
  let Fo := (chosenGraph T (stateOriginalArrow T P V σ π d formula)).graph
  let Fr := (chosenGraph T (stateResultCodeArrow T P V σ π d formula)).graph
  let O := ConcreteNamedSubstitution.originalGraph
  let F := ConcreteNamedSubstitution.occurrencesGraph
  let R := ConcreteNamedSubstitution.resultGraph
  let FV := ConcreteNamedSubstitution.freeVariablesGraph V σ π d
  .mkSigma “p payload z. !C.val payload ∧ !Fp.val z p ∧
    ∃ old fv res, !Fo.val z old ∧ !Fr.val z res ∧
      !O.val old payload ∧ !F.val fv payload ∧ !R.val res payload ∧ !FV.val fv old”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem stateLeaf_model (formula : Bool) (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d formula)) :
    (stateLeaf T P V σ π d formula).val.Evalb ![p.val,u,z.val] ↔
      (nativePayloadCarrier V σ π d formula).val.Evalb ![u] ∧
      (F T M).map (prod.fst : P ⨯ computationState T V σ π d formula ⟶ P) z = p ∧
      ((F T M).map (stateOriginalArrow T P V σ π d formula) z).val =
        ConcreteNamedSubstitution.original u ∧
      ((F T M).map (stateResultCodeArrow T P V σ π d formula) z).val =
        ConcreteNamedSubstitution.result u ∧
      ConcreteNamedSubstitution.occurrences u =
        ConcreteNamedSubstitution.freeVariables V σ π d (ConcreteNamedSubstitution.original u) := by
  have hgraph : (stateLeaf T P V σ π d formula).val.Evalb ![p.val,u,z.val] ↔
      (nativePayloadCarrier V σ π d formula).val.Evalb ![u] ∧
      (chosenGraph T (prod.fst : P ⨯ computationState T V σ π d formula ⟶ P)).graph.val.Evalb ![z.val,p.val] ∧
      ∃ old fv res : M,
        (chosenGraph T (stateOriginalArrow T P V σ π d formula)).graph.val.Evalb ![z.val,old] ∧
        (chosenGraph T (stateResultCodeArrow T P V σ π d formula)).graph.val.Evalb ![z.val,res] ∧
        old = ConcreteNamedSubstitution.original u ∧ fv = ConcreteNamedSubstitution.occurrences u ∧
        res = ConcreteNamedSubstitution.result u ∧ fv = ConcreteNamedSubstitution.freeVariables V σ π d old := by
    simp [stateLeaf]
  rw [hgraph]
  simp only [chosenGraph_value_iff T M,← Subtype.ext_iff]
  constructor
  · rintro ⟨hc,hp,old,fv,res,ho,hr,rfl,rfl,rfl,hfv⟩
    exact ⟨hc,hp,ho,hr,hfv⟩
  · rintro ⟨hc,hp,ho,hr,hfv⟩
    exact ⟨hc,hp,_,_,_,ho,hr,rfl,rfl,rfl,hfv⟩

end Models

def computedStateFamily (U : PredicateCategory T) : (formula : Bool) →
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (syntaxCarrier V σ π d formula : PredicateCategory T) ⟶
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (computationState T V σ π d formula)
  | false => computedTermState T U V σ π d
  | true => computedFormulaState T U V σ π d

@[reassoc] theorem computedState_original (U : PredicateCategory T) (formula : Bool) :
    (computedStateFamily T V σ π d U formula).left ≫
      stateOriginalArrow T (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) V σ π d formula =
        payloadProjectionArrow T U V σ π d .original formula := by
  cases formula
  · simp only [computedStateFamily,computedTermState,stateOriginalArrow,Over.homMk_left]
    erw [prod.lift_snd_assoc,prod.lift_fst]
  · simp only [computedStateFamily,computedFormulaState,stateOriginalArrow,Over.homMk_left]
    erw [prod.lift_snd_assoc,prod.lift_fst]

@[reassoc] theorem computedState_result (U : PredicateCategory T) (formula : Bool) :
    (computedStateFamily T V σ π d U formula).left ≫
      stateResultCodeArrow T (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) V σ π d formula =
        rawResultArrow T U V σ π d formula := by
  cases formula
  · simp only [computedStateFamily,computedTermState,stateResultCodeArrow,computedTermResult,Over.homMk_left]
    erw [prod.lift_snd_assoc,prod.lift_snd]
  · simp only [computedStateFamily,computedFormulaState,stateResultCodeArrow,computedFormulaResult,Over.homMk_left]
    erw [prod.lift_snd_assoc,prod.lift_snd_assoc]
    rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]

section ComputedModels
variable (U : PredicateCategory T)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem stateLeaf_computed (formula : Bool)
    (p : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)))
    (q : Obj T M ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T)))
    (hp : (F T M).map prod.fst q = p) :
    (stateLeaf T (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) V σ π d formula).val.Evalb
      ![p.val,ConcreteNamedSubstitution.substitutionPayload V σ π d
          ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) p).val
          ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) p).val
          ((F T M).map prod.snd q).val,
        ((F T M).map (computedStateFamily T V σ π d U formula).left q).val] := by
  let x := (F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) p
  let t := (F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) p
  let w := (F T M).map (prod.snd :
    (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T) ⟶ (syntaxCarrier V σ π d formula : PredicateCategory T)) q
  let payload := ConcreteNamedSubstitution.substitutionPayload V σ π d x.val t.val w.val
  apply (stateLeaf_model T _ V σ π d M formula p payload _).mpr
  refine ⟨?_,(over_value T M (computedStateFamily T V σ π d U formula) q).trans hp,?_,?_,?_⟩
  · have ht := ConcreteNamedSubstitution.substitutionPayload_carrier V σ π d formula
      x.val t.val w.val t.property w.property
    cases formula <;> exact ht
  · erw [← Functor.map_comp_apply,computedState_original]
    have ho := payloadProjectionArrow_value T U V σ π d M .original formula q
    rw [hp] at ho
    exact ho
  · erw [← Functor.map_comp_apply,computedState_result]
    have hr := rawResultArrow_value T U V σ π d M formula q
    rw [hp] at hr
    exact hr
  · have ho := originalComputation_identity T U V σ π d M formula x.val t.val w.val
      x.property t.property w.property
    have hv := occurrenceComputation_identity T U V σ π d M formula x.val t.val w.val
      x.property t.property w.property
    exact hv.trans (congrArg (ConcreteNamedSubstitution.freeVariables V σ π d) ho).symm

/-- The finite polynomial map of the computed state morphisms has the numerical payload
coordinates obtained by the proved numeric loop. This only uses a forward chart, so no
chosen-product-code identity or generic representation inverse is required. -/
theorem computedState_polynomialCoordinates
    (p : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)))
    (a : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((a.withParameters (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))).eval.obj
      (constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (syntaxCarrier V σ π d false : PredicateCategory T),
       constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (syntaxCarrier V σ π d true : PredicateCategory T))).left)
    (hz : (constantRepresentation T (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true) a).val.Evalb ![p.val,u,z.val]) :
    let P := U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)
    let h := ConcreteNamedSubstitution.substitutionPayload V σ π d
      ((F T M).map (prod.fst : P ⟶ U) p).val
      ((F T M).map (prod.snd : P ⟶ _) p).val
    (representation T P
      (constantFamily P (computationState T V σ π d false),constantFamily P (computationState T V σ π d true))
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) a).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren h h a u,
        ((F T M).map ((a.withParameters P).eval.map
          ((computedStateFamily T V σ π d U false,computedStateFamily T V σ π d U true) :
            (constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T),
              constantFamily P (syntaxCarrier V σ π d true : PredicateCategory T)) ⟶
            (constantFamily P (computationState T V σ π d false),
              constantFamily P (computationState T V σ π d true)))).left z).val] := by
  apply relationRepresentation_map T M
    (computedStateFamily T V σ π d U false) (computedStateFamily T V σ π d U true)
    (stateLeaf T _ V σ π d false) (stateLeaf T _ V σ π d true) p _ _
    (fun q hq => stateLeaf_computed T V σ π d U M false p q hq)
    (fun q hq => stateLeaf_computed T V σ π d U M true p q hq) a u z hz

end ComputedModels
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
