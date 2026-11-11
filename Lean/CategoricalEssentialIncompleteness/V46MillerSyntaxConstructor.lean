/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxChildren
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # Constructor equations of the actual uniform finite-record evaluator

The source is the original postfix word; the intermediate raw value
retains the original coefficients and ordered evaluated children. The
proof constructs framed child traces and appends the actual operation
at the root. No constructor equation is supplied to the evaluator.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable (a b : SyntacticSyntax.RawPolynomial)
variable (hT : object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
variable (hF : object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)

theorem root_valueStep (formula : Bool) (r u v value : ℕ)
    (hm : MapValues a b hT hF (if formula then b else a) r u v)
    (hop : value ∈ (if formula then operation hF else operation hT) (r,v)) :
    adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ valueStep hT hF
      (r,(Nat.pair (shape (if formula then b else a) u) (if formula then 1 else 0),
        childStack (if formula then b else a) v 0+1)) := by
  have hs := mapValues_shape a b hT hF (if formula then b else a) hm
  have ht := mapValues_target_raw a b hT hF (if formula then b else a) hm
  have hrefill : refill ((if formula then b else a).mapCoefficients (predicateFunctor P).obj)
      (shape (if formula then b else a) u) (childStack (if formula then b else a) v 0)=adjoin v 0 := by
    rw [refill_mapped,hs]
    exact Coding.refill_shape (if formula then b else a) v 0 ht
  cases formula
  · change _ ∈ valueStep hT hF (r,(Nat.pair (shape a u) 0,childStack a v 0+1))
    simp only [valueStep,Nat.add_one_ne_zero,ite_false,Nat.unpair_pair,ite_true,Nat.add_sub_cancel]
    exact (outcome_graph hT false r (shape a u) (childStack a v 0) _).mpr
      (Or.inr ⟨v,0,value,hrefill,hop,rfl⟩)
  · change _ ∈ valueStep hT hF (r,(Nat.pair (shape b u) 1,childStack b v 0+1))
    simp only [valueStep,Nat.add_one_ne_zero,ite_false,Nat.unpair_pair,ite_true,Nat.add_sub_cancel]
    exact (outcome_graph hF true r (shape b u) (childStack b v 0) _).mpr
      (Or.inr ⟨v,0,value,hrefill,hop,rfl⟩)

theorem evaluation_of_mapValues (formula : Bool) (r u v value : ℕ)
    (hm : MapValues a b hT hF (if formula then b else a) r u v)
    (hop : value ∈ (if formula then operation hF else operation hT) (r,v)) :
    adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈
      evaluation hT hF (Nat.pair r (constructor formula (if formula then b else a) u)) := by
  have hchildren := children_trace a b hT hF (if formula then b else a) hm 0
  have hroot := root_valueStep a b hT hF formula r u v value hm hop
  have htail : Trace hT hF r [Nat.pair (shape (if formula then b else a) u) (if formula then 1 else 0)]
      (childStack (if formula then b else a) v 0+1)
      (adjoin (Nat.pair value (if formula then 1 else 0)) 0+1) :=
    .cons hroot (.nil _)
  apply (evaluation_trace hT hF r _ _).mpr
  simpa only [constructor,natToList_concat,nat_pair_eq,zero_add] using
    Trace.append hT hF hchildren htail

theorem evaluation_constructor (formula : Bool) (r u value : ℕ)
    (hr : r ∈ R.obj.support)
    (hu : (SyntacticSyntax.rawCarrier (Postfix.plainCarrier false a b) (Postfix.plainCarrier true a b)
      (if formula then b else a)).val.Evalb (M := ℕ) ![u]) :
    (adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈
      evaluation hT hF (Nat.pair r (constructor formula (if formula then b else a) u)) ↔
      ∃ v,MapValues a b hT hF (if formula then b else a) r u v ∧
        value ∈ (if formula then operation hF else operation hT) (r,v)) := by
  constructor
  · intro he
    obtain ⟨v,hm⟩ := mapValues_exists a b hT hF (if formula then b else a) hr hu
    have hf := mapValues_fiber a b hT hF (if formula then b else a) hm
    have htotal : ∃ output,output ∈ (if formula then operation hF else operation hT) (r,v) := by
      cases formula
      · exact operation_exists hT hf
      · exact operation_exists hF hf
    obtain ⟨output,hop⟩ := htotal
    have hout := evaluation_of_mapValues a b hT hF formula r u v output hm hop
    have heq : value=output := by
      have he := Part.mem_unique he hout
      have hb := ((adjoin_inj _ _ _ _).mp (Nat.add_right_cancel he)).1
      have hv := congrArg (fun n => (Nat.unpair n).1) hb
      simpa only [Nat.unpair_pair] using hv
    exact ⟨v,hm,heq.symm ▸ hop⟩
  · rintro ⟨v,hm,hop⟩
    exact evaluation_of_mapValues a b hT hF formula r u v value hm hop

theorem fold_constructor (formula : Bool) (r u value : ℕ)
    (hr : r ∈ R.obj.support)
    (hu : (SyntacticSyntax.rawCarrier (Postfix.plainCarrier false a b) (Postfix.plainCarrier true a b)
      (if formula then b else a)).val.Evalb (M := ℕ) ![u]) :
    (value ∈ Total.val (fold a b hT hF formula).left.hom
      (Nat.pair r (constructor formula (if formula then b else a) u)) ↔
      ∃ v,MapValues a b hT hF (if formula then b else a) r u v ∧
        value ∈ (if formula then operation hF else operation hT) (r,v)) := by
  have hw : constructor formula (if formula then b else a) u ∈ (words P formula a b).support :=
    (Postfix.plain_constructor_comparison formula a b u hu).2
  rw [fold_graph]
  simp only [hr,hw,true_and]
  exact evaluation_constructor a b hT hF formula r u value hr hu

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
