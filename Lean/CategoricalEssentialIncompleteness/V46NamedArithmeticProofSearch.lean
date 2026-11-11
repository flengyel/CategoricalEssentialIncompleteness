/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSubstitution
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedAxioms
public import CategoricalEssentialIncompleteness.V46SyntacticParityComparison

/-! # The partial proof-search morphism for the constructed arithmetic theory

Both evidence predicates use the selected program of the actual generated
proof algebra. Their input is the actual fixed-formula substitution graph;
refutation uses the graph of the actual negation constructor. The source
morphism is chosen before an interpreting model or a disjointness proof.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

open NamedArithmeticSignature
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound

/-- Provability after the actual numeral-substitution graph. Its graph
coordinates are output/input, whereas represented morphisms use input/output. -/
def positive (Γ : Carrier) (φ : Formula) : Carrier :=
  let H := NamedArithmeticFixedSubstitution.graph φ
  let Th := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound Γ
  .mkSigma “n. ∃ word, !H.val word n ∧ !Th.val word”

/-- Refutation after substitution uses the actual formula-negation graph. -/
def negative (Γ : Carrier) (φ : Formula) : Carrier :=
  let H := NamedArithmeticFixedSubstitution.graph φ
  let Neg := (chosenGraph 𝗣𝗔 (S).negationConstructor).graph
  let Th := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound Γ
  .mkSigma “n. ∃ word negative, !H.val word n ∧ !Neg.val word negative ∧ !Th.val negative”

/-- The actual partial source lift. No consistency or totality hypothesis
enters its definition. -/
def ell (Γ : Carrier) (φ : Formula) :
    omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  PartialSearchLift.lift (positive Γ φ) (negative Γ φ)

/-- The same source computation in numerical even/odd coordinates. -/
def numericalEll (Γ : Carrier) (φ : Formula) : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  PartialSearchLift.parityLift (positive Γ φ) (negative Γ φ)

theorem numericalEll_decode (Γ : Carrier) (φ : Formula) :
    numericalEll Γ φ ≫ (omegaCoprodIso 𝗣𝗔).inv = ell Γ φ :=
  PartialSearchLift.parityLift_decode (positive Γ φ) (negative Γ φ)

section Models

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem positive_eval (Γ : Carrier) (φ : Formula) (n : M) :
    (positive Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] := by
  simp [positive]

@[simp] theorem negative_eval (Γ : Carrier) (φ : Formula) (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      ∃ negative : M,
        (chosenGraph 𝗣𝗔 (S).negationConstructor).graph.val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n,negative] ∧
        (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb ![negative] := by
  simp [negative]

/-- Exact graph over every element of any PA model satisfying the printed
model-disjointness condition. Inputs and outputs may be nonstandard. -/
theorem mem_ell (Γ : Carrier) (φ : Formula)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]))
    (x : M) (y : M ⊕ M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) x ↔
      match y with
      | Sum.inl z => (negative Γ φ).val.Evalb ![x] ∧ z = x
      | Sum.inr z => (positive Γ φ).val.Evalb ![x] ∧ z = x :=
  PartialSearchLift.mem_model_lift M (positive Γ φ) (negative Γ φ) hd x y

theorem ell_domain (Γ : Carrier) (φ : Formula)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]))
    (x : M) :
    (∃ y : M ⊕ M, y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) x) ↔
      (positive Γ φ).val.Evalb ![x] ∨ (negative Γ φ).val.Evalb ![x] :=
  PartialSearchLift.model_lift_domain M (positive Γ φ) (negative Γ φ) hd x

/-- The literal even/odd relation printed in Lemma 7.2. This does not assert
that proof search is total on inputs for which neither predicate holds. -/
theorem mem_numericalEll (Γ : Carrier) (φ : Formula)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]))
    (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (numericalEll Γ φ) x ↔
      ((positive Γ φ).val.Evalb ![x] ∧ y = 2 * x + 1) ∨
        ((negative Γ φ).val.Evalb ![x] ∧ y = 2 * x) :=
  PartialSearchLift.mem_parityLift M (positive Γ φ) (negative Γ φ) hd x y

theorem pull_summand0 (Γ : Carrier) (φ : Formula)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand0 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {n : M | (negative Γ φ).val.Evalb ![n]} :=
  PartialSearchLift.pull_summand0 M (positive Γ φ) (negative Γ φ) hd

theorem pull_summand1 (Γ : Carrier) (φ : Formula)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand1 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {n : M | (positive Γ φ).val.Evalb ![n]} :=
  PartialSearchLift.pull_summand1 M (positive Γ φ) (negative Γ φ) hd

theorem ell_comparison (Γ : Carrier) (φ : Formula) :
    (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) =
      (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) ≫
        ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
          (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom :=
  PartialSearchLift.lift_comparison M (positive Γ φ) (negative Γ φ)

end Models

/-- The source morphism is selected before all model structures and before
the disjointness witness, for the actual generated Γ theory. -/
theorem partial_proof_search (Γ : Carrier) (φ : Formula) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (negative Γ φ).val.Evalb ![n]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (positive Γ φ).val.Evalb ![n]} := by
  exact ⟨ell Γ φ,fun M _ _ hd => ⟨pull_summand0 M Γ φ hd,pull_summand1 M Γ φ hd⟩⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
