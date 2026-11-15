/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationCarrier

/-! # Independent checks of finite positive-label valuations -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax ConcreteNamedSubstitution SignedDerivation

section PrimitiveRecursion

example : Primrec (positiveLabels : ℕ → ℕ) := positiveLabels_primrec
example : Primrec₂ (jointLabels : ℕ → ℕ → ℕ) := jointLabels_primrec
example : Primrec (fun p : (ℕ × ℕ) × ℕ => member p.2 (jointLabels p.1.1 p.1.2)) :=
  finiteAtomValue_primrec

end PrimitiveRecursion

section InternalCodes
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (n word : M) : member n (positiveLabels word) = 1 ↔
    ∃ i < len word, nth word i = leaf n 0 := by
  rw [member_positiveLabels]
  simp only [MemVec, eq_comm]

example (p q : M) : positiveLabels (Words.append p q) =
    Words.append (positiveLabels p) (positiveLabels q) := positiveLabels_append p q

variable {L A B V S F : PredicateCategory 𝗣𝗔}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
local notation "D" => SyntacticDerivation.derivationCarrier 𝗣𝗔
  (literalRules 𝗣𝗔 logical sentence axioms all imp)

example (hd : ∀ n : M, ¬ (A.val.Evalb ![n] ∧ B.val.Evalb ![n]))
    (p q : M) (hp : (D).val.Evalb ![p]) (hq : (D).val.Evalb ![q]) :
    ∃ labels : M,
      (∀ n : M, member n labels = 0 ∨ member n labels = 1) ∧
      (∀ n i : M, i < len p → nth p i = leaf n 0 → member n labels = 1) ∧
      (∀ n i : M, i < len q → nth q i = leaf n 0 → member n labels = 1) ∧
      (∀ n : M, B.val.Evalb ![n] → member n labels = 0) := by
  have h := signed_derivation_values 𝗣𝗔 logical sentence axioms all imp hd p q hp hq
  exact ⟨jointLabels p q, fun n => member_boolean n _,
    fun n i hi he => h.1 n (Or.inl ⟨i, hi, he.symm⟩),
    fun n i hi he => h.1 n (Or.inr ⟨i, hi, he.symm⟩), h.2⟩

example (hd : 𝗣𝗔 ⊢ disjointnessSentence A B) :
    𝗣𝗔 ⊢ derivationValuationSentence 𝗣𝗔 logical sentence axioms all imp :=
  derivationValuation_theory 𝗣𝗔 logical sentence axioms all imp hd

example : imageSubobject (pullback.snd (SyntacticDerivation.derivationAlgebra 𝗣𝗔
      (literalRules 𝗣𝗔 logical sentence axioms all imp)).a.hom sentence) =
    imageSubobject (pullback.snd (SyntacticDerivation.derivationAlgebra 𝗣𝗔
      (firstOrderRules logical sentence axioms all imp)).a.hom sentence) :=
  literal_sentence_image 𝗣𝗔 logical sentence axioms all imp

end InternalCodes

section ArithmeticPair
variable {L V S F : PredicateCategory 𝗣𝗔}
variable (logical : L ⟶ F) (sentence : S ⟶ F)
variable (axioms : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
  (Limits.coprod (C := PredicateCategory 𝗣𝗔) ArithmeticDiagonalCodes.alpha
    ArithmeticDiagonalCodes.beta) S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

example : 𝗣𝗔 ⊢ derivationValuationSentence 𝗣𝗔 logical sentence axioms all imp :=
  arithmetic_derivationValuation_PA logical sentence axioms all imp

end ArithmeticPair

#print axioms SignedDerivation.positive_record
#print axioms SignedDerivation.negative_record
#print axioms SignedDerivation.leaf_primrec
#print axioms SignedDerivation.label_primrec
#print axioms SignedDerivation.positiveLabelsGraph_eval
#print axioms SignedDerivation.member_positiveLabels
#print axioms SignedDerivation.positiveLabels_append
#print axioms SignedDerivation.positiveLabels_carrier
#print axioms SignedDerivation.positiveLabels_primrec
#print axioms SignedDerivation.jointLabels_positive
#print axioms SignedDerivation.jointLabels_negative
#print axioms SignedDerivation.finiteValuation_PA
#print axioms SignedDerivation.arithmetic_finiteValuation_PA
#print axioms SignedDerivation.jointLabels_primrec
#print axioms SignedDerivation.finiteAtomValue_primrec
#print axioms SignedDerivation.derivation_coefficients
#print axioms SignedDerivation.sumIso
#print axioms SignedDerivation.axiomIso
#print axioms SignedDerivation.literal_rule_polynomial
#print axioms SignedDerivation.literal_conclusion_image
#print axioms SignedDerivation.literal_sentence_image
#print axioms RuleRelabelling.conclusion_image_eq
#print axioms RuleRelabelling.sentence_image_eq
#print axioms SignedDerivation.signed_derivation_coefficients
#print axioms SignedDerivation.signed_derivation_labels
#print axioms SignedDerivation.signed_derivation_values
#print axioms SignedDerivation.derivationValuation_theory
#print axioms SignedDerivation.arithmetic_derivationValuation_PA
