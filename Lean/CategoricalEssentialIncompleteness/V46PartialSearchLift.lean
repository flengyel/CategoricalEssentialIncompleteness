/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSearch
public import CategoricalEssentialIncompleteness.SyntacticPreservation

/-! # Partial search with reversed model fibers

The selected source morphism depends only on two Sigma-one formulas.
Disjointness is required in the interpreting model, not provable in PA.
The coproduct uses the production pair-and-tag code and its proved
comparison with recursively interpreted sums.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.ProgramGraph
open FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSearchLift

abbrev Carrier := 𝚺₁.Semisentence 1

/-- Positive evidence selects the second summand; negative evidence the first. -/
def reversedGraph (C D : Carrier) : Graph := .mkSigma
  “x z. (!C.val x ∧ !pairDef.val z x 1) ∨ (!D.val x ∧ !pairDef.val z x 0)”

section Models

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem reversedGraph_eval (C D : Carrier) (x z : M) :
    (reversedGraph C D).val.Evalb ![x, z] ↔
      (C.val.Evalb ![x] ∧ z = pair x 1) ∨ (D.val.Evalb ![x] ∧ z = pair x 0) := by
  simp [reversedGraph]

theorem reversedGraph_functional (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x]))
    (x y z : M) (hy : (reversedGraph C D).val.Evalb ![x, y])
    (hz : (reversedGraph C D).val.Evalb ![x, z]) : y = z := by
  rw [reversedGraph_eval] at hy hz
  rcases hy with ⟨hc, rfl⟩ | ⟨hd', rfl⟩
  · rcases hz with ⟨_, rfl⟩ | ⟨hd', _⟩
    · rfl
    · exact False.elim (hd x ⟨hc, hd'⟩)
  · rcases hz with ⟨hc, _⟩ | ⟨_, rfl⟩
    · exact False.elim (hd x ⟨hc, hd'⟩)
    · rfl

/-- Search is exact in any particular disjoint model. No proof of
disjointness in PA or coverage hypothesis is used. -/
theorem search_graph_in_model (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x z : M) :
    (eventualGraph (SyntacticSearch.searchIndex (reversedGraph C D))).val.Evalb ![x, z] ↔
      (reversedGraph C D).val.Evalb ![x, z] := by
  constructor
  · exact SyntacticSearch.search_sound_in_model _ x z
  · intro hz
    obtain ⟨y, hy⟩ := (SyntacticSearch.search_domain_in_model (reversedGraph C D) x).mpr ⟨z, hz⟩
    have he := reversedGraph_functional C D hd x y z
      (SyntacticSearch.search_sound_in_model _ x y hy) hz
    simpa only [he] using hy

end Models

/-- A fixed partial source morphism, chosen before any model or disjointness witness. -/
def lift (C D : Carrier) : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega)
    (SyntacticSearch.searchIndex (reversedGraph C D))

section Interpretation

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem mem_model_lift (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x : M) (y : M ⊕ M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x ↔
      match y with
      | Sum.inl z => D.val.Evalb ![x] ∧ z = x
      | Sum.inr z => C.val.Evalb ![x] ∧ z = x := by
  rw [lift, SyntacticModel.mem_model_index, search_graph_in_model C D hd]
  cases y with
  | inl z =>
    change (reversedGraph C D).val.Evalb ![x, pair z 0] ↔ _
    rw [reversedGraph_eval]
    constructor
    · rintro (⟨_, he⟩ | ⟨hD, he⟩)
      · have h := congrArg unpair he
        have h01 : (0 : M) = 1 := by simpa only [unpair_pair] using congrArg Prod.snd h
        exact False.elim (zero_ne_one h01)
      · have h := congrArg unpair he
        exact ⟨hD, by simpa only [unpair_pair] using congrArg Prod.fst h⟩
    · rintro ⟨hD, rfl⟩
      exact Or.inr ⟨hD, rfl⟩
  | inr z =>
    change (reversedGraph C D).val.Evalb ![x, pair z 1] ↔ _
    rw [reversedGraph_eval]
    constructor
    · rintro (⟨hC, he⟩ | ⟨_, he⟩)
      · have h := congrArg unpair he
        exact ⟨hC, by simpa only [unpair_pair] using congrArg Prod.fst h⟩
      · have h := congrArg unpair he
        have h10 : (1 : M) = 0 := by simpa only [unpair_pair] using congrArg Prod.snd h
        exact False.elim (_root_.one_ne_zero h10)
    · rintro ⟨hC, rfl⟩
      exact Or.inl ⟨hC, rfl⟩

theorem model_lift_domain (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x : M) :
    (∃ y : M ⊕ M, y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x) ↔
      C.val.Evalb ![x] ∨ D.val.Evalb ![x] := by
  constructor
  · rintro ⟨y, hy⟩
    cases y with
    | inl z => exact Or.inr ((mem_model_lift M C D hd x (Sum.inl z)).mp hy).1
    | inr z => exact Or.inl ((mem_model_lift M C D hd x (Sum.inr z)).mp hy).1
  · rintro (hC | hD)
    · exact ⟨Sum.inr x, (mem_model_lift M C D hd x (Sum.inr x)).mpr ⟨hC, rfl⟩⟩
    · exact ⟨Sum.inl x, (mem_model_lift M C D hd x (Sum.inl x)).mpr ⟨hD, rfl⟩⟩

/-- The model's canonical coproduct comparison is the identity on the
recursively interpreted sum, giving the required lifted-map equation. -/
theorem lift_comparison (C D : Carrier) :
    (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) =
      (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) ≫
        ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
          (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom := by
  change _ = _ ≫ coproductComparison (SyntacticModel.modelFunctor 𝗣𝗔 M) _ _
  rw [SyntacticModel.model_comparison_eq_id, Category.comp_id]

open PartialFunctions

theorem mem_support_summand0 (z : M ⊕ M) :
    z ∈ support (summand0 (PartialFun.of M) (PartialFun.of M)) ↔
      ∃ n, z = Sum.inl n := by
  rw [mem_support]
  change (∃ w, w ∈ coprod_map (𝟙 (PartialFun.of M))
    (0 : PartialFun.of M ⟶ PartialFun.of M) z) ↔ _
  cases z <;> simp

theorem mem_support_summand1 (z : M ⊕ M) :
    z ∈ support (summand1 (PartialFun.of M) (PartialFun.of M)) ↔
      ∃ n, z = Sum.inr n := by
  rw [mem_support]
  change (∃ w, w ∈ coprod_map (0 : PartialFun.of M ⟶ PartialFun.of M)
    (𝟙 (PartialFun.of M)) z) ↔ _
  cases z <;> simp

theorem pull_summand0 (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D))
      (summand0 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {x : M | D.val.Evalb ![x]} := by
  apply support_injective
  ext x
  rw [support_pull, support_setIdem]
  change (∃ y : M ⊕ M, y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x ∧
    y ∈ support (summand0 (PartialFun.of M) (PartialFun.of M))) ↔ _
  simp only [mem_support_summand0]
  constructor
  · rintro ⟨_, hy, z, rfl⟩
    exact ((mem_model_lift M C D hd x (Sum.inl z)).mp hy).1
  · intro hx
    exact ⟨Sum.inl x, (mem_model_lift M C D hd x (Sum.inl x)).mpr ⟨hx, rfl⟩,
      x, rfl⟩

theorem pull_summand1 (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D))
      (summand1 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {x : M | C.val.Evalb ![x]} := by
  apply support_injective
  ext x
  rw [support_pull, support_setIdem]
  change (∃ y : M ⊕ M, y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x ∧
    y ∈ support (summand1 (PartialFun.of M) (PartialFun.of M))) ↔ _
  simp only [mem_support_summand1]
  constructor
  · rintro ⟨_, hy, z, rfl⟩
    exact ((mem_model_lift M C D hd x (Sum.inr z)).mp hy).1
  · intro hx
    exact ⟨Sum.inr x, (mem_model_lift M C D hd x (Sum.inr x)).mpr ⟨hx, rfl⟩,
      x, rfl⟩

/-- Lemma 8.2's search construction for arbitrary Sigma-one evidence predicates. Concrete
provability predicates may be substituted after their categorical syntax comparison
has been established. -/
theorem partial_lift (C D : Carrier) :
    ∃ ell : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map ell)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {x : M | D.val.Evalb ![x]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map ell)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {x : M | C.val.Evalb ![x]} := by
  exact ⟨lift C D, fun M _ _ hd => ⟨pull_summand0 M C D hd, pull_summand1 M C D hd⟩⟩

end Interpretation

end CategoricalEssentialIncompleteness.V46.PartialSearchLift
