/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationPositiveLabels
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! # A common finite atom valuation for two signed derivation words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

def jointLabelsGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p q. ∃ a b, !positiveLabelsGraph.val a p ∧ !positiveLabelsGraph.val b q ∧
    !Words.appendDef.val out a b”

def positiveOccurrence : 𝚺₁.Semisentence 2 := .mkSigma
  “n word. ∃ r, !leafGraph.val r n 0 ∧ !memVecDef.sigma r word”

def disjointnessSentence (A B : Carrier) : ArithmeticSentence := ∀¹ (∼(A.val ⋏ B.val))

/-- The two words have well-typed rule coefficients. Positive leaves in
either word receive value one; every negative axiom label receives zero. -/
def finiteValuationSentence (L A B R₁ R₂ : Carrier) : ArithmeticSentence :=
  let C := Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit
  “∀ p q, !C.val p → !C.val q → ∃ labels, !jointLabelsGraph.val labels p q ∧
    (∀ n, (!positiveOccurrence.val n p ∨ !positiveOccurrence.val n q) →
      !memberGraph.val 1 labels n) ∧
    (∀ n, !B.val n → !memberGraph.val 0 labels n)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def jointLabels (p q : M) : M := Words.append (positiveLabels p) (positiveLabels q)

@[simp] theorem jointLabelsGraph_eval (out p q : M) :
    jointLabelsGraph.val.Evalb ![out, p, q] ↔ out = jointLabels p q := by
  simp [jointLabelsGraph, jointLabels]

@[simp] theorem positiveOccurrence_eval (n word : M) :
    positiveOccurrence.val.Evalb ![n, word] ↔ MemVec (leaf n 0) word := by
  simp [positiveOccurrence, MemVec]

theorem jointLabels_positive (p q n : M)
    (hn : MemVec (leaf n 0) p ∨ MemVec (leaf n 0) q) :
    member n (jointLabels p q) = 1 := by
  classical
  rcases hn with hp | hq
  · have hm := (member_positiveLabels n p).mpr hp
    simp [jointLabels, member_append, hm]
  · have hm := (member_positiveLabels n q).mpr hq
    simp [jointLabels, member_append, hm]

theorem jointLabels_carrier (L A B R₁ R₂ : Carrier) (p q : M)
    (hp : (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![p])
    (hq : (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![q]) :
    (SyntacticLists.listCarrier A).val.Evalb ![jointLabels p q] :=
  append_carrier A _ _ (positiveLabels_carrier L A B R₁ R₂ p hp)
    (positiveLabels_carrier L A B R₁ R₂ q hq)

theorem jointLabels_negative (L A B R₁ R₂ : Carrier)
    (hd : ∀ n : M, ¬ (A.val.Evalb ![n] ∧ B.val.Evalb ![n])) (p q n : M)
    (hp : (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![p])
    (hq : (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![q])
    (hn : B.val.Evalb ![n]) : member n (jointLabels p q) = 0 := by
  have hc := (SyntacticLists.listCarrier_eval A (jointLabels p q)).mp
    (jointLabels_carrier L A B R₁ R₂ p q hp hq)
  rcases member_boolean n (jointLabels p q) with hzero | hone
  · exact hzero
  · obtain ⟨i, hi, he⟩ := (member_eq_one_iff n (jointLabels p q)).mp hone
    exact (hd n ⟨he ▸ hc i hi, hn⟩).elim

theorem finiteValuationSentence_eval (L A B R₁ R₂ : Carrier) :
    (finiteValuationSentence L A B R₁ R₂).Evalb (M := M) ![] ↔
      ∀ p q : M,
        (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![p] →
        (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![q] →
        (∀ n : M, (MemVec (leaf n 0) p ∨ MemVec (leaf n 0) q) →
          member n (jointLabels p q) = 1) ∧
        (∀ n : M, B.val.Evalb ![n] → member n (jointLabels p q) = 0) := by
  simp [finiteValuationSentence, eq_comm]

end Models

theorem finiteValuation_PA (L A B R₁ R₂ : Carrier)
    (hd : 𝗣𝗔 ⊢ disjointnessSentence A B) :
    𝗣𝗔 ⊢ finiteValuationSentence L A B R₁ R₂ := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, finiteValuationSentence_eval]
  have hdisjoint : ∀ n : M, ¬ (A.val.Evalb ![n] ∧ B.val.Evalb ![n]) := by
    simpa only [models_iff, disjointnessSentence, Semiformula.eval_all,
      LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.and_eq] using
      (consequence_iff.mp (Theory.Proof.sound hd) M inferInstance)
  intro p q hp hq
  exact ⟨fun n hn => jointLabels_positive p q n hn,
    fun n hn => jointLabels_negative L A B R₁ R₂ hdisjoint p q n hp hq hn⟩

theorem arithmetic_finiteValuation_PA (L R₁ R₂ : Carrier) :
    𝗣𝗔 ⊢ finiteValuationSentence L ArithmeticDiagonalCodes.alpha
      ArithmeticDiagonalCodes.beta R₁ R₂ :=
  finiteValuation_PA L _ _ R₁ R₂ ArithmeticDiagonalCodes.disjoint_PA

open SyntacticSyntax.NatVectors

theorem jointLabels_primrec : Primrec₂ (jointLabels : ℕ → ℕ → ℕ) :=
  append_primrec.comp (positiveLabels_primrec.comp Primrec.fst)
    (positiveLabels_primrec.comp Primrec.snd)

theorem finiteAtomValue_primrec :
    Primrec (fun p : (ℕ × ℕ) × ℕ => member p.2 (jointLabels p.1.1 p.1.2)) :=
  member_primrec.comp Primrec.snd (jointLabels_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))

end CategoricalEssentialIncompleteness.V46.SignedDerivation
