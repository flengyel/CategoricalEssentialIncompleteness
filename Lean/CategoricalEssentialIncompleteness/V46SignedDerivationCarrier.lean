/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationFiniteValuation
public import CategoricalEssentialIncompleteness.V46SignedDerivationRules

/-! # Finite atom valuations on the constructed signed derivation carrier -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : PredicateCategory T}

/-- Successful validation retains the coefficient condition of the original word,
including its nonlogical axiom labels. -/
theorem derivation_coefficients (R : RulePresentation F 2)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (word : M) (hw : (SyntacticDerivation.derivationCarrier T R).val.Evalb ![word]) :
    (Coding.coefficients
      (SyntaxPolynomial.constructors
        (SyntacticDerivation.PolynomialComparison.coefficients (D := PredicateCategory T) R) 2)
      .unit).val.Evalb ![word] := by
  obtain ⟨z, hz⟩ := (SyntacticDerivation.SuccessCarrier.carrier_eval
    (SyntacticDerivation.validatorFold T R).f M word).mp hw
  have ht := (SyntacticDerivation.SuccessCarrier.valueGraph_eval
    (SyntacticDerivation.validatorFold T R).f M word z).mp hz |>.1
  change (Postfix.carrier false
    (SyntaxPolynomial.constructors
      (SyntacticDerivation.PolynomialComparison.coefficients (D := PredicateCategory T) R) 2)
    .unit).val.Evalb ![word] at ht
  exact ((Postfix.carrier_eval false _ _ word).mp ht).1

variable {L A B V S : PredicateCategory T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
local notation "R" => literalRules T logical sentence axioms all imp

theorem signed_derivation_coefficients
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (word : M) (hw : (SyntacticDerivation.derivationCarrier T R).val.Evalb ![word]) :
    (Coding.coefficients (rulePolynomial L A B (Limits.prod (C := PredicateCategory T) V F)
      (Limits.prod (C := PredicateCategory T) F F)) .unit).val.Evalb ![word] := by
  have h := derivation_coefficients T R word hw
  rw [literal_rule_polynomial T logical sentence axioms all imp] at h
  exact h

theorem signed_derivation_labels
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (word : M) (hw : (SyntacticDerivation.derivationCarrier T R).val.Evalb ![word]) :
    (SyntacticLists.listCarrier A).val.Evalb ![positiveLabels word] :=
  positiveLabels_carrier L A B (Limits.prod (C := PredicateCategory T) V F)
    (Limits.prod (C := PredicateCategory T) F F) word
    (signed_derivation_coefficients T logical sentence axioms all imp word hw)

/-- A common finite assignment for two constructed derivations. -/
theorem signed_derivation_values
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (hd : ∀ n : M, ¬ (A.val.Evalb ![n] ∧ B.val.Evalb ![n]))
    (p q : M)
    (hp : (SyntacticDerivation.derivationCarrier T R).val.Evalb ![p])
    (hq : (SyntacticDerivation.derivationCarrier T R).val.Evalb ![q]) :
    (∀ n : M, (MemVec (leaf n 0) p ∨ MemVec (leaf n 0) q) →
      member n (jointLabels p q) = 1) ∧
    (∀ n : M, B.val.Evalb ![n] → member n (jointLabels p q) = 0) :=
  ⟨fun n hn => jointLabels_positive p q n hn,
    fun n hn => jointLabels_negative L A B (Limits.prod (C := PredicateCategory T) V F)
      (Limits.prod (C := PredicateCategory T) F F) hd p q n
      (signed_derivation_coefficients T logical sentence axioms all imp p hp)
      (signed_derivation_coefficients T logical sentence axioms all imp q hq) hn⟩

def derivationValuationSentence : ArithmeticSentence :=
  let D := SyntacticDerivation.derivationCarrier T R
  “∀ p q, !D.val p → !D.val q → ∃ labels, !jointLabelsGraph.val labels p q ∧
    (∀ n, (!positiveOccurrence.val n p ∨ !positiveOccurrence.val n q) →
      !memberGraph.val 1 labels n) ∧
    (∀ n, !B.val n → !memberGraph.val 0 labels n)”

theorem derivationValuation_theory (hd : T ⊢ disjointnessSentence A B) :
    T ⊢ derivationValuationSentence T logical sentence axioms all imp := by
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  have hdisjoint : ∀ n : M, ¬ (A.val.Evalb ![n] ∧ B.val.Evalb ![n]) := by
    simpa only [models_iff, disjointnessSentence, Semiformula.eval_all,
      LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.and_eq] using
      (consequence_iff.mp (Theory.Proof.sound hd) M inferInstance)
  have hval := signed_derivation_values T logical sentence axioms all imp hdisjoint
  simpa [models_iff, derivationValuationSentence, eq_comm] using hval

end CategoricalEssentialIncompleteness.V46.SignedDerivation

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

variable {L V S F : PredicateCategory 𝗣𝗔}
variable (logical : L ⟶ F) (sentence : S ⟶ F)
variable (axioms : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
  (Limits.coprod (C := PredicateCategory 𝗣𝗔) ArithmeticDiagonalCodes.alpha
    ArithmeticDiagonalCodes.beta) S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

theorem arithmetic_derivationValuation_PA :
    𝗣𝗔 ⊢ derivationValuationSentence 𝗣𝗔 logical sentence axioms all imp :=
  derivationValuation_theory 𝗣𝗔 logical sentence axioms all imp ArithmeticDiagonalCodes.disjoint_PA

end CategoricalEssentialIncompleteness.V46.SignedDerivation
