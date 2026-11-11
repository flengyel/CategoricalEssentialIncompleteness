/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core
public import FailureOfComposition.RangeAssignment

/-!
# Numerical proofs of range membership from computations

This module adds two axiom families to the selected numerical proof
presentation.  The first admits a stage-tagged graph instance only when its
displayed evaluator computation is verified.  The second, for fixed external
indices `e` and `r`, expresses that a value computed by `e` is fixed by `r`.
The latter family is arithmetically sound when a fixed PA derivation identifies
the graph of `r` with `rangeGraph e`; that hypothesis is used in the soundness
layer, not by the executable recognizer.

The resulting map is total on all natural-number inputs.  Its correctness
theorem assumes that the supplied stage really codes the displayed
computation, so malformed inputs have defined but otherwise unspecified
output proof codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalRangeProofs

open ConcreteEvaluator NumericalProofBridge NumericalSpecialization ProofSearch

/-! ## The accepted numerical computation relation -/

/-- Arguments `(e,s,u,i)` for a supplied computation: program, stage, input,
and output. -/
abbrev ComputationArgs := (((ℕ × ℕ) × ℕ) × ℕ)

/-- A self-contained stage number carrying all four parameters of a checked
computation.  The redundancy lets the logical-axiom recognizer recover every
parameter without decoding arithmetic syntax. -/
def computationStage (e s u i : ℕ) : ℕ :=
  Nat.pair e (Nat.pair s (Nat.pair u i))

def computationStagePacked (z : ComputationArgs) : ℕ :=
  computationStage z.1.1.1 z.1.1.2 z.1.2 z.2

theorem primrec_computationStage : Primrec computationStagePacked := by
  have he : Primrec (fun z : ComputationArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec (fun z : ComputationArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun z : ComputationArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ComputationArgs => z.2) := Primrec.snd
  exact (Primrec₂.natPair.comp he
    (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp hu hi))).of_eq
      (fun _ => rfl)

/-- Boolean verification of the exact evaluator-stage relation used by the
range proof map. -/
def computationTest (e s u i : ℕ) : Bool :=
  decide (Nat.Partrec.Code.evaln s
    (Denumerable.ofNat Nat.Partrec.Code e) u = some i)

@[simp] theorem computationTest_eq_true_iff (e s u i : ℕ) :
    computationTest e s u i = true ↔ stageComputation s e u i := by
  simpa [computationTest, Denumerable.encode_ofNat, Option.mem_def] using
    (stageComputation_iff_evaln s
      (Denumerable.ofNat Nat.Partrec.Code e) u i).symm

private theorem primrecPred_computationRelation :
    PrimrecPred (fun z : ComputationArgs =>
      Nat.Partrec.Code.evaln z.1.1.2
        (Denumerable.ofNat Nat.Partrec.Code z.1.1.1) z.1.2 = some z.2) := by
  have he : Primrec (fun z : ComputationArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec (fun z : ComputationArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun z : ComputationArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ComputationArgs => z.2) := Primrec.snd
  have heval : Primrec (fun z : ComputationArgs =>
      Nat.Partrec.Code.evaln z.1.1.2
        (Denumerable.ofNat Nat.Partrec.Code z.1.1.1) z.1.2) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((hs.pair ((Primrec.ofNat Nat.Partrec.Code).comp he)).pair hu)
  have hsome : Primrec (fun z : ComputationArgs => some z.2) :=
    Primrec.option_some.comp hi
  exact Primrec.eq.comp heval hsome

theorem primrecPred_stageComputation :
    PrimrecPred (fun z : ComputationArgs =>
      stageComputation z.1.1.2 z.1.1.1 z.1.2 z.2) := by
  exact primrecPred_computationRelation.of_eq fun z => by
    simpa only [Denumerable.encode_ofNat, Option.mem_def] using
      (stageComputation_iff_evaln z.1.1.2
        (Denumerable.ofNat Nat.Partrec.Code z.1.1.1) z.1.2 z.2).symm

theorem primrec_computationTest :
    Primrec (fun z : ComputationArgs =>
      computationTest z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  exact PrimrecPred.decide primrecPred_computationRelation

/-! ## Computation-certificate logical axioms -/

/-- The stage-tagged copy of the closed graph instance certified by `s`. -/
def computationAxiomString (e s u i : ℕ) : FormulaString :=
  stageString (rightSentenceCode e u i) (computationStage e s u i)

def computationAxiomCode (e s u i : ℕ) : FormulaCode :=
  encodeFormula (computationAxiomString e s u i)

@[simp] theorem computationAxiomCode_eq_stage (e s u i : ℕ) :
    computationAxiomCode e s u i =
      stageCode (rightSentenceCode e u i) (computationStage e s u i) := by
  simp [computationAxiomCode, computationAxiomString, stageCode]

theorem primrec_computationAxiomString :
    Primrec (fun z : ComputationArgs =>
      computationAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have he : Primrec (fun z : ComputationArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun z : ComputationArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ComputationArgs => z.2) := Primrec.snd
  have ha := primrec_rightSentenceCode.comp ((he.pair hu).pair hi)
  exact primrec₂_stageString.comp ha primrec_computationStage

theorem primrec_computationAxiomCode :
    Primrec (fun z : ComputationArgs =>
      computationAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_computationAxiomString

def computationTokenAt (j : ℕ) (x : FormulaString) : ℕ :=
  x.getD j 0

private theorem primrec_computationTokenAt (j : ℕ) :
    Primrec (computationTokenAt j) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const j)

def recoveredStagePayload (x : FormulaString) : ℕ :=
  computationTokenAt 2 x

def recoveredProgram (x : FormulaString) : ℕ :=
  (recoveredStagePayload x).unpair.1

def recoveredStage (x : FormulaString) : ℕ :=
  (recoveredStagePayload x).unpair.2.unpair.1

def recoveredInput (x : FormulaString) : ℕ :=
  (recoveredStagePayload x).unpair.2.unpair.2.unpair.1

def recoveredOutput (x : FormulaString) : ℕ :=
  (recoveredStagePayload x).unpair.2.unpair.2.unpair.2

private theorem primrec_recoveredStagePayload :
    Primrec recoveredStagePayload := primrec_computationTokenAt 2

private theorem primrec_recoveredProgram : Primrec recoveredProgram :=
  Primrec.fst.comp (Primrec.unpair.comp primrec_recoveredStagePayload)

private theorem primrec_recoveredStage : Primrec recoveredStage :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp primrec_recoveredStagePayload)))

private theorem primrec_recoveredInput : Primrec recoveredInput :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp primrec_recoveredStagePayload)))))

private theorem primrec_recoveredOutput : Primrec recoveredOutput :=
  Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp primrec_recoveredStagePayload)))))

@[simp] private theorem recoveredProgram_axiomString (e s u i : ℕ) :
    recoveredProgram (computationAxiomString e s u i) = e := by
  have hk : recoveredStagePayload (computationAxiomString e s u i) =
      computationStage e s u i := by rfl
  rw [recoveredProgram, hk]
  simp [computationStage]

@[simp] private theorem recoveredStage_axiomString (e s u i : ℕ) :
    recoveredStage (computationAxiomString e s u i) = s := by
  have hk : recoveredStagePayload (computationAxiomString e s u i) =
      computationStage e s u i := by rfl
  rw [recoveredStage, hk]
  simp [computationStage]

@[simp] private theorem recoveredInput_axiomString (e s u i : ℕ) :
    recoveredInput (computationAxiomString e s u i) = u := by
  have hk : recoveredStagePayload (computationAxiomString e s u i) =
      computationStage e s u i := by rfl
  rw [recoveredInput, hk]
  simp [computationStage]

@[simp] private theorem recoveredOutput_axiomString (e s u i : ℕ) :
    recoveredOutput (computationAxiomString e s u i) = i := by
  have hk : recoveredStagePayload (computationAxiomString e s u i) =
      computationStage e s u i := by rfl
  rw [recoveredOutput, hk]
  simp [computationStage]

def computationAxiomCandidate (x : FormulaString) : FormulaString :=
  computationAxiomString (recoveredProgram x) (recoveredStage x)
    (recoveredInput x) (recoveredOutput x)

private theorem primrec_computationAxiomCandidate :
    Primrec computationAxiomCandidate := by
  exact (primrec_computationAxiomString.comp
    (((primrec_recoveredProgram.pair primrec_recoveredStage).pair
      primrec_recoveredInput).pair primrec_recoveredOutput)).of_eq
        (fun _ => rfl)

def ComputationAxiomShape (x : FormulaString) : Prop :=
  x = computationAxiomCandidate x ∧
    computationTest (recoveredProgram x) (recoveredStage x)
      (recoveredInput x) (recoveredOutput x) = true

def computationAxiomTest (x : FormulaString) : Bool :=
  decide (x = computationAxiomCandidate x) &&
    computationTest (recoveredProgram x) (recoveredStage x)
      (recoveredInput x) (recoveredOutput x)

@[simp] theorem computationAxiomTest_eq_true_iff (x : FormulaString) :
    computationAxiomTest x = true ↔ ComputationAxiomShape x := by
  simp [computationAxiomTest, ComputationAxiomShape]

theorem computationAxiomShape_iff (x : FormulaString) :
    ComputationAxiomShape x ↔
      ∃ e s u i, stageComputation s e u i ∧
        x = computationAxiomString e s u i := by
  constructor
  · rintro ⟨hx, hcomp⟩
    exact ⟨recoveredProgram x, recoveredStage x, recoveredInput x,
      recoveredOutput x, (computationTest_eq_true_iff _ _ _ _).mp hcomp, hx⟩
  · rintro ⟨e, s, u, i, hcomp, rfl⟩
    simp [ComputationAxiomShape, computationAxiomCandidate, hcomp]

theorem primrec_computationAxiomTest : Primrec computationAxiomTest := by
  have hargs : Primrec (fun x : FormulaString =>
      (((recoveredProgram x, recoveredStage x), recoveredInput x),
        recoveredOutput x)) :=
    ((primrec_recoveredProgram.pair primrec_recoveredStage).pair
      primrec_recoveredInput).pair primrec_recoveredOutput
  have heq : Primrec (fun x : FormulaString =>
      decide (x = computationAxiomCandidate x)) :=
    PrimrecPred.decide
      (Primrec.eq.comp Primrec.id primrec_computationAxiomCandidate)
  exact (Primrec.and.comp heq (primrec_computationTest.comp hargs)).of_eq
    (fun _ => rfl)

/-! ## Fixed-parameter range introduction -/

/-- For fixed external indices `e` and `r`, the implication saying that a
computation of `e` at `u` with value `i` makes `r` fix `i`. -/
def rangeIntroAxiomString (e r u i : ℕ) : FormulaString :=
  impString (rightInstanceString e u i) (rightInstanceString r i i)

def rangeIntroAxiomCode (e r u i : ℕ) : FormulaCode :=
  encodeFormula (rangeIntroAxiomString e r u i)

@[simp] theorem rangeIntroAxiomCode_eq_imp (e r u i : ℕ) :
    rangeIntroAxiomCode e r u i =
      imp (rightInstanceCode e u i) (rightInstanceCode r i i) := by
  simp [rangeIntroAxiomCode, rangeIntroAxiomString, rightInstanceCode, imp]

theorem primrec_rangeIntroAxiomString :
    Primrec (fun z : ComputationArgs =>
      rangeIntroAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have he : Primrec (fun z : ComputationArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun z : ComputationArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun z : ComputationArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ComputationArgs => z.2) := Primrec.snd
  exact primrec_impString.comp
    (primrec_rightInstanceString.comp ((he.pair hu).pair hi))
    (primrec_rightInstanceString.comp ((hr.pair hi).pair hi))

theorem primrec_rangeIntroAxiomCode :
    Primrec (fun z : ComputationArgs =>
      rangeIntroAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_rangeIntroAxiomString

def recoveredRangeInput (x : FormulaString) : ℕ :=
  computationTokenAt 2 (lhsString x)

def recoveredRangeOutput (x : FormulaString) : ℕ :=
  computationTokenAt 3 (lhsString x)

private theorem primrec_recoveredRangeInput : Primrec recoveredRangeInput :=
  (primrec_computationTokenAt 2).comp primrec_lhsString

private theorem primrec_recoveredRangeOutput : Primrec recoveredRangeOutput :=
  (primrec_computationTokenAt 3).comp primrec_lhsString

@[simp] private theorem recoveredRangeInput_axiomString (e r u i : ℕ) :
    recoveredRangeInput (rangeIntroAxiomString e r u i) = u := by
  simp [recoveredRangeInput, rangeIntroAxiomString, computationTokenAt,
    rightInstanceString]

@[simp] private theorem recoveredRangeOutput_axiomString (e r u i : ℕ) :
    recoveredRangeOutput (rangeIntroAxiomString e r u i) = i := by
  simp [recoveredRangeOutput, rangeIntroAxiomString, computationTokenAt,
    rightInstanceString]

def rangeIntroAxiomCandidate
    (e r : ℕ) (x : FormulaString) : FormulaString :=
  rangeIntroAxiomString e r (recoveredRangeInput x)
    (recoveredRangeOutput x)

private theorem primrec_rangeIntroAxiomCandidate (e r : ℕ) :
    Primrec (rangeIntroAxiomCandidate e r) := by
  have hargs : Primrec (fun x : FormulaString =>
      (((e, r), recoveredRangeInput x), recoveredRangeOutput x)) :=
    (((Primrec.const e).pair (Primrec.const r)).pair
      primrec_recoveredRangeInput).pair primrec_recoveredRangeOutput
  exact (primrec_rangeIntroAxiomString.comp hargs).of_eq (fun _ => rfl)

def RangeIntroAxiomShape (e r : ℕ) (x : FormulaString) : Prop :=
  x = rangeIntroAxiomCandidate e r x

def rangeIntroAxiomTest (e r : ℕ) (x : FormulaString) : Bool :=
  x == rangeIntroAxiomCandidate e r x

@[simp] theorem rangeIntroAxiomTest_eq_true_iff
    (e r : ℕ) (x : FormulaString) :
    rangeIntroAxiomTest e r x = true ↔ RangeIntroAxiomShape e r x := by
  simp [rangeIntroAxiomTest, RangeIntroAxiomShape]

theorem rangeIntroAxiomShape_iff (e r : ℕ) (x : FormulaString) :
    RangeIntroAxiomShape e r x ↔
      ∃ u i, x = rangeIntroAxiomString e r u i := by
  constructor
  · intro hx
    exact ⟨recoveredRangeInput x, recoveredRangeOutput x, hx⟩
  · rintro ⟨u, i, rfl⟩
    simp [RangeIntroAxiomShape, rangeIntroAxiomCandidate]

theorem primrec_rangeIntroAxiomTest (e r : ℕ) :
    Primrec (rangeIntroAxiomTest e r) :=
  (Primrec.beq.comp Primrec.id (primrec_rangeIntroAxiomCandidate e r)).of_eq
    (fun x => by simp [rangeIntroAxiomTest])

/-! ## The selected range-proof presentation -/

def RangeLogicalAxiomShape (e r : ℕ) (x : FormulaString) : Prop :=
  ExtendedLogicalAxiomShape x ∨ ComputationAxiomShape x ∨
    RangeIntroAxiomShape e r x

def rangeLogicalAxiomTest (e r : ℕ) (x : FormulaString) : Bool :=
  extendedLogicalAxiomTest x ||
    (computationAxiomTest x || rangeIntroAxiomTest e r x)

@[simp] theorem rangeLogicalAxiomTest_eq_true_iff
    (e r : ℕ) (x : FormulaString) :
    rangeLogicalAxiomTest e r x = true ↔
      RangeLogicalAxiomShape e r x := by
  simp [rangeLogicalAxiomTest, RangeLogicalAxiomShape]

theorem primrec_rangeLogicalAxiomTest (e r : ℕ) :
    Primrec (rangeLogicalAxiomTest e r) :=
  Primrec.or.comp primrec_extendedLogicalAxiomTest
    (Primrec.or.comp primrec_computationAxiomTest
      (primrec_rangeIntroAxiomTest e r))

def rangeTheoryPresentation (e r : ℕ)
    (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨rangeLogicalAxiomTest e r⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def rangePRTheoryPresentation (e r : ℕ)
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := rangeTheoryPresentation e r w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_rangeLogicalAxiomTest e r
  ax_prim := primrec_axiomTest w hw

noncomputable def paRangeTheoryPresentation (e r : ℕ) : TheoryPresentation :=
  rangeTheoryPresentation e r paStageWitness

noncomputable def paRangePRTheoryPresentation (e r : ℕ) :
    PRTheoryPresentation :=
  rangePRTheoryPresentation e r paStageWitness primrec_paStageWitness

theorem extendedLogicalAxiom_holds_range
    (e r : ℕ) (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds x) :
    (rangeTheoryPresentation e r w).syn.logicalAxiom.Holds x := by
  change extendedLogicalAxiomTest x = true at h
  change rangeLogicalAxiomTest e r x = true
  simp [rangeLogicalAxiomTest, h]

theorem computationAxiom_holds
    (e r : ℕ) (w : ℕ → ℕ → Bool) {q s u i : ℕ}
    (hs : stageComputation s q u i) :
    (rangeTheoryPresentation e r w).syn.logicalAxiom.Holds
      (computationAxiomString q s u i) := by
  have hshape : RangeLogicalAxiomShape e r
      (computationAxiomString q s u i) :=
    Or.inr (Or.inl ((computationAxiomShape_iff _).mpr
      ⟨q, s, u, i, hs, rfl⟩))
  have htest := (rangeLogicalAxiomTest_eq_true_iff e r _).mpr hshape
  simpa only [rangeTheoryPresentation, StringPredicate.Holds] using htest

theorem rangeIntroAxiom_holds
    (e r : ℕ) (w : ℕ → ℕ → Bool) (u i : ℕ) :
    (rangeTheoryPresentation e r w).syn.logicalAxiom.Holds
      (rangeIntroAxiomString e r u i) := by
  have hshape : RangeLogicalAxiomShape e r
      (rangeIntroAxiomString e r u i) :=
    Or.inr (Or.inr ((rangeIntroAxiomShape_iff e r _).mpr
      ⟨u, i, rfl⟩))
  have htest := (rangeLogicalAxiomTest_eq_true_iff e r _).mpr hshape
  simpa only [rangeTheoryPresentation, StringPredicate.Holds] using htest

theorem proof_T_extended_to_range
    (e r : ℕ) (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (rangeTheoryPresentation e r w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro j hjlt
  obtain ⟨hline, -, hcase⟩ := hj j hjlt
  refine ⟨hline, by simp [rangeTheoryPresentation,
    StringPredicate.Holds], ?_⟩
  rcases hcase with hlog | hax | hmp
  · exact Or.inl (extendedLogicalAxiom_holds_range e r w hlog)
  · exact Or.inr (Or.inl (by
      simpa [extendedTheoryPresentation, rangeTheoryPresentation] using hax))
  · exact Or.inr (Or.inr hmp)

/-! ## The total computation-code-to-proof map -/

/-- First turn the checked computation into the ordinary right-instance graph
tag by the accepted bridge rule. -/
def computationToRightProof (e s u i : ℕ) : ProofSequenceCode :=
  bridgeRight (oneLineProofCode (computationAxiomCode e s u i))
    (computationStage e s u i) e u i

/-- Apply the fixed range-introduction implication to the graph proof. -/
def rangeProof (e r s u i : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (rangeIntroAxiomCode e r u i))
    (computationToRightProof e s u i)

theorem proof_T_computationToRightProof
    (e r : ℕ) (w : ℕ → ℕ → Bool) {s u i : ℕ}
    (hs : stageComputation s e u i) :
    Proof_T (rangeTheoryPresentation e r w)
      (computationToRightProof e s u i) (rightInstanceCode e u i) := by
  apply proof_T_mp _
  · apply proof_T_oneLine_of_logicalAxiom
    rw [computationAxiomCode, decodeFormula_encodeFormula]
    exact computationAxiom_holds e r w hs
  · rw [computationAxiomCode_eq_stage, ← bridgeRightAxiomCode_eq_imp]
    apply proof_T_oneLine_of_logicalAxiom
    rw [bridgeRightAxiomCode, decodeFormula_encodeFormula]
    exact extendedLogicalAxiom_holds_range e r w
      (bridgeRightAxiom_holds w e u i (computationStage e s u i))

theorem proof_T_rangeProof
    (e r : ℕ) (w : ℕ → ℕ → Bool) {s u i : ℕ}
    (hs : stageComputation s e u i) :
    Proof_T (rangeTheoryPresentation e r w)
      (rangeProof e r s u i) (rightInstanceCode r i i) := by
  apply proof_T_mp _ (proof_T_computationToRightProof e r w hs)
  rw [← rangeIntroAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [rangeIntroAxiomCode, decodeFormula_encodeFormula]
  exact rangeIntroAxiom_holds e r w u i

abbrev RangeProofArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

def rangeProofPacked (z : RangeProofArgs) : ProofSequenceCode :=
  rangeProof z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

/-- Primitive recursiveness is uniform in the displayed program indices,
stage, input, and output.  Correctness later fixes the indices and assumes the
range graph derivation. -/
theorem primrec_rangeProof : Primrec rangeProofPacked := by
  let ef : RangeProofArgs → ℕ := fun z => z.1.1.1.1
  let rf : RangeProofArgs → ℕ := fun z => z.1.1.1.2
  let sf : RangeProofArgs → ℕ := fun z => z.1.1.2
  let uf : RangeProofArgs → ℕ := fun z => z.1.2
  let ifn : RangeProofArgs → ℕ := fun z => z.2
  have he : Primrec ef :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hr : Primrec rf :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec sf :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec uf :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec ifn := Primrec.snd
  have hcompArgs : Primrec (fun z : RangeProofArgs =>
      (((ef z, sf z), uf z), ifn z)) :=
    ((he.pair hs).pair hu).pair hi
  have hcompCode := primrec_computationAxiomCode.comp hcompArgs
  have hstage := primrec_computationStage.comp hcompArgs
  have hright : Primrec (fun z : RangeProofArgs =>
      computationToRightProof (ef z) (sf z) (uf z) (ifn z)) := by
    have hbridgeArgs : Primrec (fun z : RangeProofArgs =>
        ((((oneLineProofCode (computationAxiomCode (ef z) (sf z)
          (uf z) (ifn z)), computationStage (ef z) (sf z) (uf z) (ifn z)),
          ef z), uf z), ifn z)) :=
      ((((primrec_oneLineProofCode.comp hcompCode).pair hstage).pair he).pair hu).pair hi
    exact (primrec_bridgeRight.comp hbridgeArgs).of_eq (fun _ => rfl)
  have hrangeArgs : Primrec (fun z : RangeProofArgs =>
      (((ef z, rf z), uf z), ifn z)) :=
    ((he.pair hr).pair hu).pair hi
  have hax := primrec_rangeIntroAxiomCode.comp hrangeArgs
  exact (primrec_mp.comp (primrec_oneLineProofCode.comp hax) hright).of_eq
    (fun _ => rfl)

end FailureOfComposition.NumericalRangeProofs
