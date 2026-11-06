/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonAdmissibleValues

/-! # A literal T-proof identifying the numerical admissibility predicate -/

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
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

/-- The source is the actual chosen word/parameter product. The chart
converts it to the literal code ((x,replacement),word) before invoking
the separately defined primitive recursive free-for graph. -/
def canonicalFreeForPredicate : Carrier :=
  let D : PredicateCategory T := Y ⨯ P
  let I := (chosenGraph T (publicParameterInput T V X Y)).graph
  let H := ConcreteNamedSubstitution.substitutionFreeForGraph V σ π d
  .mkSigma “input. !D.val input ∧ ∃ raw names x replacement word,
    !I.val input raw ∧ !pairDef.val raw names word ∧
      !pairDef.val names x replacement ∧ !H.val 1 x replacement word”

/-- This is the actual image of the already constructed admissibility
inclusion, with its actual graph representative. -/
def canonicalAdmissibleCarrier : Carrier :=
  imageCarrier (chosenGraph T (S).admissibleInclusion).graph

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem canonicalFreeForPredicate_model (q : Obj T M (Y ⨯ P)) :
    (canonicalFreeForPredicate T V σ π d).val.Evalb ![q.val] ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 := by
  let xq := ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
  let tq := ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
  let wq := ((F T M).map prod.fst q).val
  have hpred : (canonicalFreeForPredicate T V σ π d).val.Evalb ![q.val] ↔
      (Y ⨯ P : PredicateCategory T).val.Evalb ![q.val] ∧
      ∃ raw names x replacement word : M,
        ((F T M).map (publicParameterInput T V X Y) q).val = raw ∧
        raw = Arithmetic.pair names word ∧ names = Arithmetic.pair x replacement ∧
        1 = ConcreteNamedSubstitution.substitutionFreeFor V σ π d x replacement word := by
    simp [canonicalFreeForPredicate,chosenGraph_value_iff T M]
    intro _
    rfl
  rw [hpred]
  have hc : ((F T M).map (publicParameterInput T V X Y) q).val =
      Arithmetic.pair (Arithmetic.pair xq tq) wq := publicParameterInput_value T M V X Y q
  constructor
  · rintro ⟨_,raw,names,x,replacement,word,hi,hr,hn,hf⟩
    have hp : Arithmetic.pair (Arithmetic.pair xq tq) wq =
        Arithmetic.pair (Arithmetic.pair x replacement) word :=
      hc.symm.trans (hi.trans (hr.trans
        (congrArg (fun p => Arithmetic.pair p word) hn)))
    obtain ⟨hxt,hw⟩ := (pair_eq_pair_iff _ _ _ _).mp hp
    obtain ⟨hx,ht⟩ := (pair_eq_pair_iff _ _ _ _).mp hxt
    have hs : (xq,(tq,wq)) = (x,(replacement,word)) := Prod.ext hx (Prod.ext ht hw)
    exact (congrArg (fun args : M × M × M =>
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d args.1 args.2.1 args.2.2) hs).trans hf.symm
  · intro hf
    exact ⟨q.property,_,Arithmetic.pair xq tq,xq,tq,wq,rfl,hc,rfl,hf.symm⟩

theorem canonicalAdmissibleCarrier_freeFor (input : M) :
    (canonicalAdmissibleCarrier T V σ π d).val.Evalb ![input] ↔
      (canonicalFreeForPredicate T V σ π d).val.Evalb ![input] := by
  change (imageCarrier (chosenGraph T (S).admissibleInclusion).graph).val.Evalb ![input] ↔ _
  rw [imageCarrier_eval]
  constructor
  · rintro ⟨a,ha⟩
    let aa : Obj T M (S).admissibleSubstitution :=
      ⟨a,((chosenGraph T (S).admissibleInclusion).support_model M a input ha).1⟩
    let q : Obj T M (Y ⨯ P) :=
      ⟨input,((chosenGraph T (S).admissibleInclusion).support_model M a input ha).2⟩
    have hq : (F T M).map (S).admissibleInclusion aa = q :=
      (chosenGraph_map_iff T M (S).admissibleInclusion aa q).mp ha
    exact (canonicalFreeForPredicate_model T V σ π d M q).mpr
      ((canonical_admissible_model_iff T V σ π d M q).mp ⟨aa,hq⟩)
  · intro hf
    have hs : (Y ⨯ P : PredicateCategory T).val.Evalb ![input] ∧
        ∃ raw names x replacement word : M,
          (chosenGraph T (publicParameterInput T V X Y)).graph.val.Evalb ![input,raw] ∧
          raw = Arithmetic.pair names word ∧ names = Arithmetic.pair x replacement ∧
          1 = ConcreteNamedSubstitution.substitutionFreeFor V σ π d x replacement word := by
      simpa [canonicalFreeForPredicate] using hf
    have hd : (Y ⨯ P : PredicateCategory T).val.Evalb ![input] := hs.1
    let q : Obj T M (Y ⨯ P) := ⟨input,hd⟩
    have hflag := (canonicalFreeForPredicate_model T V σ π d M q).mp hf
    obtain ⟨a,ha⟩ := (canonical_admissible_model_iff T V σ π d M q).mpr hflag
    exact ⟨a.val,(chosenGraph_map_iff T M (S).admissibleInclusion a q).mpr ha⟩

end Models

/-- This is a literal T-sentence equating the actual admissible image
with the positive predicate computed by the independent raw flag. -/
def canonicalFreeForDomainSentence : ArithmeticSentence :=
  let A := canonicalAdmissibleCarrier T V σ π d
  let B := canonicalFreeForPredicate T V σ π d
  “∀ input, !A.val input ↔ !B.val input”

theorem canonicalFreeForDomain_theory : T ⊢ canonicalFreeForDomainSentence T V σ π d := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simpa [models_iff,canonicalFreeForDomainSentence] using
    (fun input : M => canonicalAdmissibleCarrier_freeFor T V σ π d M input)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
