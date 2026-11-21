/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Public word-first substitution inputs use the product braiding -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem braided_value {U R C D : PredicateCategory T}
    (f : (U ⨯ R) ⨯ C ⟶ D) (value : Obj T M D → M) (φ : M → M → M → M)
    (hf : ∀ z : Obj T M ((U ⨯ R) ⨯ C), value ((F T M).map f z) =
      φ ((F T M).map (prod.fst : U ⨯ R ⟶ U) ((F T M).map prod.fst z)).val
        ((F T M).map (prod.snd : U ⨯ R ⟶ R) ((F T M).map prod.fst z)).val
        ((F T M).map prod.snd z).val)
    (q : Obj T M (C ⨯ (U ⨯ R))) :
    value ((F T M).map ((prod.braiding C (U ⨯ R)).hom ≫ f) q) =
      φ ((F T M).map (prod.fst : U ⨯ R ⟶ U) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : U ⨯ R ⟶ R) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  rw [Functor.map_comp_apply]
  let z := (F T M).map (prod.braiding C (U ⨯ R)).hom q
  have hp : (F T M).map (prod.fst : (U ⨯ R) ⨯ C ⟶ U ⨯ R) z =
      (F T M).map (prod.snd : C ⨯ (U ⨯ R) ⟶ _) q :=
    model_lift_fst T M prod.snd prod.fst q
  have hw : (F T M).map (prod.snd : (U ⨯ R) ⨯ C ⟶ C) z =
      (F T M).map (prod.fst : C ⨯ (U ⨯ R) ⟶ C) q :=
    model_lift_snd T M prod.snd prod.fst q
  have hx := congrArg (fun p => ((F T M).map (prod.fst : U ⨯ R ⟶ U) p).val) hp
  have ht := congrArg (fun p => ((F T M).map (prod.snd : U ⨯ R ⟶ R) p).val) hp
  have hw' := congrArg Subtype.val hw
  have hi :
      (((F T M).map (prod.fst : U ⨯ R ⟶ U) ((F T M).map prod.fst z)).val,
        (((F T M).map (prod.snd : U ⨯ R ⟶ R) ((F T M).map prod.fst z)).val,
          ((F T M).map (prod.snd : (U ⨯ R) ⨯ C ⟶ C) z).val)) =
      (((F T M).map (prod.fst : U ⨯ R ⟶ U) ((F T M).map prod.snd q)).val,
        (((F T M).map (prod.snd : U ⨯ R ⟶ R) ((F T M).map prod.snd q)).val,
          ((F T M).map (prod.fst : C ⨯ (U ⨯ R) ⟶ C) q).val)) :=
    Prod.ext hx (Prod.ext ht hw')
  exact (hf z).trans (congrArg (fun inputs : M × M × M => φ inputs.1 inputs.2.1 inputs.2.2) hi)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
