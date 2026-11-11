/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes

/-!
# Proof-presentation bridge schemas and operations

This layer extends the numerical-specialization presentation with explicit
bridge axioms and primitive-recursive proof transformations.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator
open FFL.FirstOrder.Arithmetic.Bootstrapping

/-! ## Bridge schemas and the extended presentation -/

def bridgeEqualityAxiomString (q r s : ℕ) : FormulaString :=
  impString (stageString (eqSentenceCode q r) s) (equalityString q r)

def bridgeLeftAxiomString (q n m s : ℕ) : FormulaString :=
  impString (stageString (leftSentenceCode q n m) s)
    (leftInstanceString q n m)

def bridgeRightAxiomString (r n m s : ℕ) : FormulaString :=
  impString (stageString (rightSentenceCode r n m) s)
    (rightInstanceString r n m)

def bridgeEqualityAxiomCode (q r s : ℕ) : FormulaCode :=
  encodeFormula (bridgeEqualityAxiomString q r s)

def bridgeLeftAxiomCode (q n m s : ℕ) : FormulaCode :=
  encodeFormula (bridgeLeftAxiomString q n m s)

def bridgeRightAxiomCode (r n m s : ℕ) : FormulaCode :=
  encodeFormula (bridgeRightAxiomString r n m s)

private theorem encodeFormula_impString_eq_imp (a b : FormulaString) :
    encodeFormula (impString a b) =
      imp (encodeFormula a) (encodeFormula b) := by
  unfold Metamath.Feferman.imp
  rw [decodeFormula_encodeFormula, decodeFormula_encodeFormula]

@[simp] theorem bridgeEqualityAxiomCode_eq_imp (q r s : ℕ) :
    bridgeEqualityAxiomCode q r s =
      imp (stageCode (eqSentenceCode q r) s) (equalityCode q r) := by
  simpa [bridgeEqualityAxiomCode, bridgeEqualityAxiomString, stageCode,
    equalityCode] using
    encodeFormula_impString_eq_imp
      (stageString (eqSentenceCode q r) s) (equalityString q r)

@[simp] theorem bridgeLeftAxiomCode_eq_imp (q n m s : ℕ) :
    bridgeLeftAxiomCode q n m s =
      imp (stageCode (leftSentenceCode q n m) s)
        (leftInstanceCode q n m) := by
  simpa [bridgeLeftAxiomCode, bridgeLeftAxiomString, stageCode,
    leftInstanceCode] using
    encodeFormula_impString_eq_imp
      (stageString (leftSentenceCode q n m) s)
      (leftInstanceString q n m)

@[simp] theorem bridgeRightAxiomCode_eq_imp (r n m s : ℕ) :
    bridgeRightAxiomCode r n m s =
      imp (stageCode (rightSentenceCode r n m) s)
        (rightInstanceCode r n m) := by
  simpa [bridgeRightAxiomCode, bridgeRightAxiomString, stageCode,
    rightInstanceCode] using
    encodeFormula_impString_eq_imp
      (stageString (rightSentenceCode r n m) s)
      (rightInstanceString r n m)

theorem primrec_bridgeEqualityAxiomString :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      bridgeEqualityAxiomString z.1.1 z.1.2 z.2) := by
  have hsentence : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      eqSentenceCode z.1.1 z.1.2) :=
    primrec₂_eqSentenceCode.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hstage : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      stageString (eqSentenceCode z.1.1 z.1.2) z.2) :=
    primrec₂_stageString.comp hsentence Primrec.snd
  have htag : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      equalityString z.1.1 z.1.2) :=
    primrec₂_equalityString.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact primrec_impString.comp hstage htag

theorem primrec_bridgeLeftAxiomString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      bridgeLeftAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hsentence : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      leftSentenceCode z.1.1.1 z.1.1.2 z.1.2) :=
    primrec_leftSentenceCode.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))
  have hstage : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      stageString (leftSentenceCode z.1.1.1 z.1.1.2 z.1.2) z.2) :=
    primrec₂_stageString.comp hsentence Primrec.snd
  have htag : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      leftInstanceString z.1.1.1 z.1.1.2 z.1.2) :=
    primrec_leftInstanceString.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))
  exact primrec_impString.comp hstage htag

theorem primrec_bridgeRightAxiomString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      bridgeRightAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hsentence : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      rightSentenceCode z.1.1.1 z.1.1.2 z.1.2) :=
    primrec_rightSentenceCode.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))
  have hstage : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      stageString (rightSentenceCode z.1.1.1 z.1.1.2 z.1.2) z.2) :=
    primrec₂_stageString.comp hsentence Primrec.snd
  have htag : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      rightInstanceString z.1.1.1 z.1.1.2 z.1.2) :=
    primrec_rightInstanceString.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))
  exact primrec_impString.comp hstage htag

theorem primrec_bridgeEqualityAxiomCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      bridgeEqualityAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_bridgeEqualityAxiomString

theorem primrec_bridgeLeftAxiomCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      bridgeLeftAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_bridgeLeftAxiomString

theorem primrec_bridgeRightAxiomCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ =>
      bridgeRightAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_bridgeRightAxiomString

def bridgeTokenAt (i : ℕ) (s : FormulaString) : ℕ :=
  s.getD i 0

def BridgeAxiomShape (s : FormulaString) : Prop :=
  s = bridgeEqualityAxiomString
      (bridgeTokenAt 6 s) (bridgeTokenAt 7 s) (bridgeTokenAt 4 s) ∨
  s = bridgeLeftAxiomString
      (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
      (bridgeTokenAt 8 s) (bridgeTokenAt 4 s) ∨
  s = bridgeRightAxiomString
      (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
      (bridgeTokenAt 8 s) (bridgeTokenAt 4 s)

def ExtendedLogicalAxiomShape (s : FormulaString) : Prop :=
  LogicalAxiomShape s ∨ BridgeAxiomShape s

def bridgeEqualityAxiomTest (s : FormulaString) : Bool :=
  s == bridgeEqualityAxiomString
    (bridgeTokenAt 6 s) (bridgeTokenAt 7 s) (bridgeTokenAt 4 s)

def bridgeLeftAxiomTest (s : FormulaString) : Bool :=
  s == bridgeLeftAxiomString
      (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
      (bridgeTokenAt 8 s) (bridgeTokenAt 4 s)

def bridgeRightAxiomTest (s : FormulaString) : Bool :=
  s == bridgeRightAxiomString
      (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
      (bridgeTokenAt 8 s) (bridgeTokenAt 4 s)

def bridgeAxiomTest (s : FormulaString) : Bool :=
  bridgeEqualityAxiomTest s ||
    (bridgeLeftAxiomTest s || bridgeRightAxiomTest s)

@[simp] theorem bridgeAxiomTest_eq_true_iff (s : FormulaString) :
    bridgeAxiomTest s = true ↔ BridgeAxiomShape s := by
  simp [bridgeAxiomTest, bridgeEqualityAxiomTest, bridgeLeftAxiomTest,
    bridgeRightAxiomTest, BridgeAxiomShape]

def extendedLogicalAxiomTest (s : FormulaString) : Bool :=
  logicalAxiomTest s || bridgeAxiomTest s

@[simp] theorem extendedLogicalAxiomTest_eq_true_iff (s : FormulaString) :
    extendedLogicalAxiomTest s = true ↔ ExtendedLogicalAxiomShape s := by
  simp [extendedLogicalAxiomTest, ExtendedLogicalAxiomShape]

theorem bridgeAxiomShape_iff (s : FormulaString) :
    BridgeAxiomShape s ↔
      (∃ q r k, s = bridgeEqualityAxiomString q r k) ∨
      (∃ q n m k, s = bridgeLeftAxiomString q n m k) ∨
      (∃ r n m k, s = bridgeRightAxiomString r n m k) := by
  change
    (s = bridgeEqualityAxiomString
        (bridgeTokenAt 6 s) (bridgeTokenAt 7 s) (bridgeTokenAt 4 s) ∨
      s = bridgeLeftAxiomString
        (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
        (bridgeTokenAt 8 s) (bridgeTokenAt 4 s) ∨
      s = bridgeRightAxiomString
        (bridgeTokenAt 6 s) (bridgeTokenAt 7 s)
        (bridgeTokenAt 8 s) (bridgeTokenAt 4 s)) ↔ _
  constructor
  · rintro (h | h | h)
    · exact Or.inl
        ⟨bridgeTokenAt 6 s, bridgeTokenAt 7 s, bridgeTokenAt 4 s, h⟩
    · exact Or.inr (Or.inl
        ⟨bridgeTokenAt 6 s, bridgeTokenAt 7 s, bridgeTokenAt 8 s,
          bridgeTokenAt 4 s, h⟩)
    · exact Or.inr (Or.inr
        ⟨bridgeTokenAt 6 s, bridgeTokenAt 7 s, bridgeTokenAt 8 s,
          bridgeTokenAt 4 s, h⟩)
  · rintro (⟨q, r, k, rfl⟩ | ⟨q, n, m, k, rfl⟩ |
      ⟨r, n, m, k, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem primrec_bridgeTokenAt (i : ℕ) : Primrec (bridgeTokenAt i) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)

private def bridgeEqualityRecognizerArgs (s : FormulaString) :
    (ℕ × ℕ) × ℕ :=
  ((bridgeTokenAt 6 s, bridgeTokenAt 7 s), bridgeTokenAt 4 s)

private def bridgeInstanceRecognizerArgs (s : FormulaString) :
    ((ℕ × ℕ) × ℕ) × ℕ :=
  (((bridgeTokenAt 6 s, bridgeTokenAt 7 s), bridgeTokenAt 8 s),
    bridgeTokenAt 4 s)

private theorem primrec_bridgeEqualityRecognizerArgs :
    Primrec bridgeEqualityRecognizerArgs := by
  exact ((primrec_bridgeTokenAt 6).pair (primrec_bridgeTokenAt 7)).pair
    (primrec_bridgeTokenAt 4)

private theorem primrec_bridgeInstanceRecognizerArgs :
    Primrec bridgeInstanceRecognizerArgs := by
  exact (((primrec_bridgeTokenAt 6).pair (primrec_bridgeTokenAt 7)).pair
    (primrec_bridgeTokenAt 8)).pair (primrec_bridgeTokenAt 4)

private def bridgeEqualityAxiomCandidate (s : FormulaString) : FormulaString :=
  let z := bridgeEqualityRecognizerArgs s
  bridgeEqualityAxiomString z.1.1 z.1.2 z.2

private def bridgeLeftAxiomCandidate (s : FormulaString) : FormulaString :=
  let z := bridgeInstanceRecognizerArgs s
  bridgeLeftAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2

private def bridgeRightAxiomCandidate (s : FormulaString) : FormulaString :=
  let z := bridgeInstanceRecognizerArgs s
  bridgeRightAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2

private theorem primrec_bridgeEqualityAxiomCandidate :
    Primrec bridgeEqualityAxiomCandidate := by
  exact (primrec_bridgeEqualityAxiomString.comp
    primrec_bridgeEqualityRecognizerArgs).of_eq (fun _ => rfl)

private theorem primrec_bridgeLeftAxiomCandidate :
    Primrec bridgeLeftAxiomCandidate := by
  exact (primrec_bridgeLeftAxiomString.comp
    primrec_bridgeInstanceRecognizerArgs).of_eq (fun _ => rfl)

private theorem primrec_bridgeRightAxiomCandidate :
    Primrec bridgeRightAxiomCandidate := by
  exact (primrec_bridgeRightAxiomString.comp
    primrec_bridgeInstanceRecognizerArgs).of_eq (fun _ => rfl)

private theorem primrec_bridgeEqualityAxiomTest :
    Primrec bridgeEqualityAxiomTest := by
  exact (Primrec.beq.comp Primrec.id
    primrec_bridgeEqualityAxiomCandidate).of_eq (fun s => by
      simp [bridgeEqualityAxiomCandidate, bridgeEqualityRecognizerArgs,
        bridgeEqualityAxiomTest])

private theorem primrec_bridgeLeftAxiomTest :
    Primrec bridgeLeftAxiomTest := by
  exact (Primrec.beq.comp Primrec.id
    primrec_bridgeLeftAxiomCandidate).of_eq (fun s => by
      simp [bridgeLeftAxiomCandidate, bridgeInstanceRecognizerArgs,
        bridgeLeftAxiomTest])

private theorem primrec_bridgeRightAxiomTest :
    Primrec bridgeRightAxiomTest := by
  exact (Primrec.beq.comp Primrec.id
    primrec_bridgeRightAxiomCandidate).of_eq (fun s => by
      simp [bridgeRightAxiomCandidate, bridgeInstanceRecognizerArgs,
        bridgeRightAxiomTest])

theorem primrec_bridgeAxiomTest : Primrec bridgeAxiomTest := by
  unfold bridgeAxiomTest
  exact Primrec.or.comp primrec_bridgeEqualityAxiomTest
    (Primrec.or.comp primrec_bridgeLeftAxiomTest
      primrec_bridgeRightAxiomTest)

theorem primrec_extendedLogicalAxiomTest :
    Primrec extendedLogicalAxiomTest :=
  Primrec.or.comp primrec_logicalAxiomTest primrec_bridgeAxiomTest

def extendedTheoryPresentation (w : ℕ → ℕ → Bool) :
    TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨extendedLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def extendedPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := extendedTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_extendedLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem oldLogicalAxiom_holds_extended
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (specializationTheoryPresentation w).syn.logicalAxiom.Holds s) :
    (extendedTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change logicalAxiomTest s = true at h
  change extendedLogicalAxiomTest s = true
  rw [extendedLogicalAxiomTest_eq_true_iff]
  exact Or.inl ((logicalAxiomTest_eq_true_iff s).mp h)

private theorem bridgeAxiomShape_holds
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : BridgeAxiomShape s) :
    (extendedTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change extendedLogicalAxiomTest s = true
  exact (extendedLogicalAxiomTest_eq_true_iff s).mpr (Or.inr h)

theorem bridgeEqualityAxiom_holds
    (w : ℕ → ℕ → Bool) (q r s : ℕ) :
    (extendedTheoryPresentation w).syn.logicalAxiom.Holds
      (bridgeEqualityAxiomString q r s) := by
  apply bridgeAxiomShape_holds
  apply (bridgeAxiomShape_iff _).mpr
  exact Or.inl ⟨q, r, s, rfl⟩

theorem bridgeLeftAxiom_holds
    (w : ℕ → ℕ → Bool) (q n m s : ℕ) :
    (extendedTheoryPresentation w).syn.logicalAxiom.Holds
      (bridgeLeftAxiomString q n m s) := by
  apply bridgeAxiomShape_holds
  apply (bridgeAxiomShape_iff _).mpr
  exact Or.inr (Or.inl ⟨q, n, m, s, rfl⟩)

theorem bridgeRightAxiom_holds
    (w : ℕ → ℕ → Bool) (r n m s : ℕ) :
    (extendedTheoryPresentation w).syn.logicalAxiom.Holds
      (bridgeRightAxiomString r n m s) := by
  apply bridgeAxiomShape_holds
  apply (bridgeAxiomShape_iff _).mpr
  exact Or.inr (Or.inr ⟨r, n, m, s, rfl⟩)

theorem proof_T_old_to_extended
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (specializationTheoryPresentation w) p a) :
    Proof_T (extendedTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro i hi
  obtain ⟨hline, hformula, hcase⟩ := hj i hi
  refine ⟨hline, ?_, ?_⟩
  · simp [specializationTheoryPresentation, extendedTheoryPresentation,
      StringPredicate.Holds] at hformula ⊢
  · rcases hcase with hlog | hax | hmp
    · exact Or.inl (oldLogicalAxiom_holds_extended w hlog)
    · exact Or.inr (Or.inl (by
        simpa [specializationTheoryPresentation, extendedTheoryPresentation]
          using hax))
    · exact Or.inr (Or.inr hmp)

/-! ## Total primitive-recursive bridge operations -/

def bridgeEquality (p s q r : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (bridgeEqualityAxiomCode q r s)) p

def bridgeLeft (p s q n m : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (bridgeLeftAxiomCode q n m s)) p

def bridgeRight (p s r n m : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (bridgeRightAxiomCode r n m s)) p

theorem proof_T_bridgeEquality
    (w : ℕ → ℕ → Bool) {p s q r : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (eqSentenceCode q r) s)) :
    Proof_T (extendedTheoryPresentation w)
      (bridgeEquality p s q r) (equalityCode q r) := by
  apply proof_T_mp _ hp
  rw [← bridgeEqualityAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [bridgeEqualityAxiomCode, decodeFormula_encodeFormula]
  exact bridgeEqualityAxiom_holds w q r s

theorem proof_T_bridgeLeft
    (w : ℕ → ℕ → Bool) {p s q n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (leftSentenceCode q n m) s)) :
    Proof_T (extendedTheoryPresentation w)
      (bridgeLeft p s q n m) (leftInstanceCode q n m) := by
  apply proof_T_mp _ hp
  rw [← bridgeLeftAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [bridgeLeftAxiomCode, decodeFormula_encodeFormula]
  exact bridgeLeftAxiom_holds w q n m s

theorem proof_T_bridgeRight
    (w : ℕ → ℕ → Bool) {p s r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (rightSentenceCode r n m) s)) :
    Proof_T (extendedTheoryPresentation w)
      (bridgeRight p s r n m) (rightInstanceCode r n m) := by
  apply proof_T_mp _ hp
  rw [← bridgeRightAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [bridgeRightAxiomCode, decodeFormula_encodeFormula]
  exact bridgeRightAxiom_holds w r n m s

abbrev BridgeEqualityArgs := (((ℕ × ℕ) × ℕ) × ℕ)
abbrev BridgeInstanceArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

def bridgeEqualityPacked (z : BridgeEqualityArgs) : ProofSequenceCode :=
  bridgeEquality z.1.1.1 z.1.1.2 z.1.2 z.2

def bridgeLeftPacked (z : BridgeInstanceArgs) : ProofSequenceCode :=
  bridgeLeft z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

def bridgeRightPacked (z : BridgeInstanceArgs) : ProofSequenceCode :=
  bridgeRight z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

theorem primrec_bridgeEquality : Primrec bridgeEqualityPacked := by
  have hargs : Primrec (fun z : BridgeEqualityArgs =>
      ((z.1.2, z.2), z.1.1.2)) :=
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hax := primrec_bridgeEqualityAxiomCode.comp hargs
  exact (primrec_mp.comp (primrec_oneLineProofCode.comp hax)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).of_eq
      (fun _ => rfl)

theorem primrec_bridgeLeft : Primrec bridgeLeftPacked := by
  have hargs : Primrec (fun z : BridgeInstanceArgs =>
      (((z.1.1.2, z.1.2), z.2), z.1.1.1.2)) :=
    ((((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).pair
        (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))
  have hax := primrec_bridgeLeftAxiomCode.comp hargs
  exact (primrec_mp.comp (primrec_oneLineProofCode.comp hax)
    (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))).of_eq
        (fun _ => rfl)

theorem primrec_bridgeRight : Primrec bridgeRightPacked := by
  have hargs : Primrec (fun z : BridgeInstanceArgs =>
      (((z.1.1.2, z.1.2), z.2), z.1.1.1.2)) :=
    ((((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).pair
        (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))))
  have hax := primrec_bridgeRightAxiomCode.comp hargs
  exact (primrec_mp.comp (primrec_oneLineProofCode.comp hax)
    (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))).of_eq
        (fun _ => rfl)

end FailureOfComposition.NumericalProofBridge
