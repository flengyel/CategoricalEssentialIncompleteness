/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNonLocalConnectedness

/-! # Connected domains and the unprimed category in Appendix D -/

@[expose] public section

noncomputable section
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 ConnectedNumeralDomains SyntacticPredicates

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (C P N : Carrier) (hC : Connected (predicateIdem T C))
    (hPN : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M),
      N.val.Evalb ![x] ↔ ¬P.val.Evalb ![x]) : Implies T C P ∨ Implies T C N :=
  connected_decides T C P N hC hPN

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    ArithmeticDiagonalCodes.alpha.val.Evalb ![n] ↔ ∃ s : M, (stageParity 1).val.Evalb ![n, s] :=
  alpha_iff_stage n

example [T.RE] (c : Idem (omegaObject T)) (hc : Connected c) (hne : c ≠ ⊥) :
    ∃ n : ℕ, c ≤ predicateIdem T (numeralPredicate n) := connected_le_numeral T c hc hne

example {e f : ℕ} (h : ConcreteIndices.PointwiseIndex T e f) (n : ℕ) :
    (predicateIdem T (numeralPredicate n)).hom ≫ omegaArrow T (classOf T e) =
      (predicateIdem T (numeralPredicate n)).hom ≫ omegaArrow T (classOf T f) :=
  numeral_restriction_eq T h n

example [Consistent T] [T.RE] : ∃ f g : omegaObject T ⟶ omegaObject T, f ≠ g ∧
    ∀ c : Idem (omegaObject T), Connected c → c.hom ≫ f = c.hom ≫ g :=
  indistinguishable_on_connected T (axiomCodes_enumerable T)

example [Consistent T] (he : REPred (AxiomCodes T)) : ¬LocallyConnected (CodedProgramCategory T) :=
  not_locallyConnected T he

example [Consistent T] [T.RE] : ¬LocallyConnected (PrintedObjectCoding.NormalizedCategory T) :=
  unprimed_not_locallyConnected T
