/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Arith.Feferman.StructuralProof
public import Mathlib.Tactic.FinCases

/-!
# Numerical specialization and graph-proof transfer

This module gives a small, explicit Feferman presentation for the numerical
core of Appendix B, clause B1(1).  Four tagged formula strings stand for a
uniform graph equality, its closed instance, and the two graph instances.  The
logical axioms are exactly the following three schemes:

* uniform equality implies its closed instance;
* the closed equivalence implies the forward implication;
* the closed equivalence implies the reverse implication.

All formula strings are admitted as candidate formulas.  Nonlogical axioms are
stage-witnessed sentences together with the diagonal graph comparisons; their
arithmetical meaning and soundness are supplied by the concrete consumer.

The proof transformations use the existing numerical `mp`.  Their arithmetic
representatives use `mpGraph` and `proofGraphWithLogicalAxiom`, so the uniform
PA results below concern the same numerical `Proof_T` after the explicit
standard-model adequacy theorem, not the separately selected `proofTFormula`.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Metamath.Feferman
open Arith.Feferman.Structural

set_option autoImplicit false
set_option linter.flexible false

namespace Arith.Feferman.Specialization

/-! ## Tagged formula strings -/

def equalityTag : Token := 1
def leftInstanceTag : Token := 2
def rightInstanceTag : Token := 3
def instanceEqualityTag : Token := 4
def stageTag : Token := 5

def equalityString (q r : ℕ) : FormulaString :=
  [equalityTag, q, r]

def leftInstanceString (q n m : ℕ) : FormulaString :=
  [leftInstanceTag, q, n, m]

def rightInstanceString (r n m : ℕ) : FormulaString :=
  [rightInstanceTag, r, n, m]

def instanceEqualityString (q r n m : ℕ) : FormulaString :=
  [instanceEqualityTag, q, r, n, m]

/-- A stage-witnessed copy of the Foundation sentence whose `Encodable` code
is `a`. -/
def stageString (a s : ℕ) : FormulaString :=
  [stageTag, a, s]

def specializationAxiomString (q r n m : ℕ) : FormulaString :=
  impString (equalityString q r) (instanceEqualityString q r n m)

def forwardAxiomString (q r n m : ℕ) : FormulaString :=
  impString (instanceEqualityString q r n m)
    (impString (leftInstanceString q n m) (rightInstanceString r n m))

def reverseAxiomString (q r n m : ℕ) : FormulaString :=
  impString (instanceEqualityString q r n m)
    (impString (rightInstanceString r n m) (leftInstanceString q n m))

def equalityCode (q r : ℕ) : FormulaCode :=
  encodeFormula (equalityString q r)

def leftInstanceCode (q n m : ℕ) : FormulaCode :=
  encodeFormula (leftInstanceString q n m)

def rightInstanceCode (r n m : ℕ) : FormulaCode :=
  encodeFormula (rightInstanceString r n m)

def instanceEqualityCode (q r n m : ℕ) : FormulaCode :=
  encodeFormula (instanceEqualityString q r n m)

def stageCode (a s : ℕ) : FormulaCode :=
  encodeFormula (stageString a s)

def specializationAxiomCode (q r n m : ℕ) : FormulaCode :=
  encodeFormula (specializationAxiomString q r n m)

def forwardAxiomCode (q r n m : ℕ) : FormulaCode :=
  encodeFormula (forwardAxiomString q r n m)

def reverseAxiomCode (q r n m : ℕ) : FormulaCode :=
  encodeFormula (reverseAxiomString q r n m)

@[simp] theorem specializationAxiomCode_eq_imp (q r n m : ℕ) :
    specializationAxiomCode q r n m =
      imp (equalityCode q r) (instanceEqualityCode q r n m) := by
  simp [specializationAxiomCode, equalityCode, instanceEqualityCode,
    specializationAxiomString, imp]

@[simp] theorem forwardAxiomCode_eq_imp (q r n m : ℕ) :
    forwardAxiomCode q r n m =
      imp (instanceEqualityCode q r n m)
        (imp (leftInstanceCode q n m) (rightInstanceCode r n m)) := by
  simp [forwardAxiomCode, instanceEqualityCode, leftInstanceCode,
    rightInstanceCode, forwardAxiomString, imp]

@[simp] theorem reverseAxiomCode_eq_imp (q r n m : ℕ) :
    reverseAxiomCode q r n m =
      imp (instanceEqualityCode q r n m)
        (imp (rightInstanceCode r n m) (leftInstanceCode q n m)) := by
  simp [reverseAxiomCode, instanceEqualityCode, leftInstanceCode,
    rightInstanceCode, reverseAxiomString, imp]

/-! ## Primitive-recursive builders -/

private theorem primrec_list3 (t : ℕ) :
    Primrec (fun z : ℕ × ℕ ↦ [t, z.1, z.2]) := by
  exact Primrec.list_cons.comp (Primrec.const t)
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

private theorem primrec_list4 (t : ℕ) :
    Primrec (fun z : (ℕ × ℕ) × ℕ ↦ [t, z.1.1, z.1.2, z.2]) := by
  exact Primrec.list_cons.comp (Primrec.const t)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))

private theorem primrec_list5 (t : ℕ) :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      [t, z.1.1.1, z.1.1.2, z.1.2, z.2]) := by
  exact Primrec.list_cons.comp (Primrec.const t)
    (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))))

theorem primrec₂_equalityString : Primrec₂ equalityString :=
  (primrec_list3 equalityTag).to₂

theorem primrec_leftInstanceString :
    Primrec (fun z : (ℕ × ℕ) × ℕ ↦
      leftInstanceString z.1.1 z.1.2 z.2) :=
  primrec_list4 leftInstanceTag

theorem primrec_rightInstanceString :
    Primrec (fun z : (ℕ × ℕ) × ℕ ↦
      rightInstanceString z.1.1 z.1.2 z.2) :=
  primrec_list4 rightInstanceTag

theorem primrec_instanceEqualityString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      instanceEqualityString z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_list5 instanceEqualityTag

theorem primrec₂_stageString : Primrec₂ stageString :=
  (primrec_list3 stageTag).to₂

theorem primrec_specializationAxiomString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      specializationAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  exact primrec_impString.comp
    (primrec₂_equalityString.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    primrec_instanceEqualityString

theorem primrec_forwardAxiomString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      forwardAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hleft : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      leftInstanceString z.1.1.1 z.1.2 z.2) :=
    primrec_leftInstanceString.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hright : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      rightInstanceString z.1.1.2 z.1.2 z.2) :=
    primrec_rightInstanceString.comp
      (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact primrec_impString.comp primrec_instanceEqualityString
    (primrec_impString.comp hleft hright)

theorem primrec_reverseAxiomString :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      reverseAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hleft : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      leftInstanceString z.1.1.1 z.1.2 z.2) :=
    primrec_leftInstanceString.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hright : Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      rightInstanceString z.1.1.2 z.1.2 z.2) :=
    primrec_rightInstanceString.comp
      (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact primrec_impString.comp primrec_instanceEqualityString
    (primrec_impString.comp hright hleft)

theorem primrec₂_equalityCode : Primrec₂ equalityCode :=
  primrec_encodeFormula.comp primrec₂_equalityString

theorem primrec_leftInstanceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ ↦
      leftInstanceCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_leftInstanceString

theorem primrec_rightInstanceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ ↦
      rightInstanceCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_rightInstanceString

theorem primrec_instanceEqualityCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      instanceEqualityCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_instanceEqualityString

theorem primrec₂_stageCode : Primrec₂ stageCode :=
  primrec_encodeFormula.comp primrec₂_stageString

theorem primrec_specializationAxiomCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      specializationAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_specializationAxiomString

theorem primrec_forwardAxiomCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      forwardAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_forwardAxiomString

theorem primrec_reverseAxiomCode :
    Primrec (fun z : ((ℕ × ℕ) × ℕ) × ℕ ↦
      reverseAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_reverseAxiomString

/-! ## The primitive-recursive presentation -/

def tokenAt (i : ℕ) (s : FormulaString) : ℕ := s.getD i 0

abbrev LogicalAxiomShape (s : FormulaString) : Prop :=
  s = specializationAxiomString (tokenAt 3 s) (tokenAt 4 s)
      (tokenAt 8 s) (tokenAt 9 s) ∨
  s = forwardAxiomString (tokenAt 3 s) (tokenAt 4 s)
      (tokenAt 5 s) (tokenAt 6 s) ∨
  s = reverseAxiomString (tokenAt 3 s) (tokenAt 4 s)
      (tokenAt 5 s) (tokenAt 6 s)

def logicalAxiomTest (s : FormulaString) : Bool :=
  decide (LogicalAxiomShape s)

@[simp] theorem logicalAxiomTest_eq_true_iff (s : FormulaString) :
    logicalAxiomTest s = true ↔ LogicalAxiomShape s := by
  simp [logicalAxiomTest]

theorem logicalAxiomShape_iff (s : FormulaString) :
    LogicalAxiomShape s ↔
      (∃ q r n m, s = specializationAxiomString q r n m) ∨
      (∃ q r n m, s = forwardAxiomString q r n m) ∨
      (∃ q r n m, s = reverseAxiomString q r n m) := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl ⟨tokenAt 3 s, tokenAt 4 s, tokenAt 8 s, tokenAt 9 s, h⟩
    · exact Or.inr (Or.inl
        ⟨tokenAt 3 s, tokenAt 4 s, tokenAt 5 s, tokenAt 6 s, h⟩)
    · exact Or.inr (Or.inr
        ⟨tokenAt 3 s, tokenAt 4 s, tokenAt 5 s, tokenAt 6 s, h⟩)
  · rintro (⟨q, r, n, m, rfl⟩ | ⟨q, r, n, m, rfl⟩ |
      ⟨q, r, n, m, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem primrec_tokenAt (i : ℕ) : Primrec (tokenAt i) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)

theorem primrecPred_logicalAxiomShape : PrimrecPred LogicalAxiomShape := by
  have hspec : Primrec (fun s : FormulaString ↦
      specializationAxiomString (tokenAt 3 s) (tokenAt 4 s)
        (tokenAt 8 s) (tokenAt 9 s)) :=
    primrec_specializationAxiomString.comp
      ((((primrec_tokenAt 3).pair (primrec_tokenAt 4)).pair
        (primrec_tokenAt 8)).pair (primrec_tokenAt 9))
  have hfwd : Primrec (fun s : FormulaString ↦
      forwardAxiomString (tokenAt 3 s) (tokenAt 4 s)
        (tokenAt 5 s) (tokenAt 6 s)) :=
    primrec_forwardAxiomString.comp
      ((((primrec_tokenAt 3).pair (primrec_tokenAt 4)).pair
        (primrec_tokenAt 5)).pair (primrec_tokenAt 6))
  have hrev : Primrec (fun s : FormulaString ↦
      reverseAxiomString (tokenAt 3 s) (tokenAt 4 s)
        (tokenAt 5 s) (tokenAt 6 s)) :=
    primrec_reverseAxiomString.comp
      ((((primrec_tokenAt 3).pair (primrec_tokenAt 4)).pair
        (primrec_tokenAt 5)).pair (primrec_tokenAt 6))
  exact (Primrec.eq.comp Primrec.id hspec).or
    ((Primrec.eq.comp Primrec.id hfwd).or
      (Primrec.eq.comp Primrec.id hrev))

theorem primrec_logicalAxiomTest : Primrec logicalAxiomTest :=
  PrimrecPred.decide primrecPred_logicalAxiomShape

abbrev AxiomShape (w : ℕ → ℕ → Bool) (s : FormulaString) : Prop :=
  (s = stageString (tokenAt 1 s) (tokenAt 2 s) ∧
      w (tokenAt 1 s) (tokenAt 2 s) = true) ∨
  s = equalityString (tokenAt 1 s) (tokenAt 1 s)

def axiomTest (w : ℕ → ℕ → Bool) (s : FormulaString) : Bool :=
  decide (AxiomShape w s)

@[simp] theorem axiomTest_eq_true_iff (w : ℕ → ℕ → Bool)
    (s : FormulaString) :
    axiomTest w s = true ↔ AxiomShape w s := by
  simp [axiomTest]

theorem axiomShape_iff (w : ℕ → ℕ → Bool) (s : FormulaString) :
    AxiomShape w s ↔
      (∃ a k, w a k = true ∧ s = stageString a k) ∨
      (∃ q, s = equalityString q q) := by
  constructor
  · rintro (⟨h, hw⟩ | h)
    · exact Or.inl ⟨tokenAt 1 s, tokenAt 2 s, hw, h⟩
    · exact Or.inr ⟨tokenAt 1 s, h⟩
  · rintro (⟨a, k, hw, rfl⟩ | ⟨q, rfl⟩)
    · exact Or.inl ⟨rfl, hw⟩
    · exact Or.inr rfl

theorem primrecPred_axiomShape
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    PrimrecPred (AxiomShape w) := by
  have hstage : Primrec (fun s : FormulaString ↦
      stageString (tokenAt 1 s) (tokenAt 2 s)) :=
    primrec₂_stageString.comp (primrec_tokenAt 1) (primrec_tokenAt 2)
  have hw' : Primrec (fun s : FormulaString ↦
      w (tokenAt 1 s) (tokenAt 2 s)) :=
    hw.comp ((primrec_tokenAt 1).pair (primrec_tokenAt 2))
  have heq : Primrec (fun s : FormulaString ↦
      equalityString (tokenAt 1 s) (tokenAt 1 s)) :=
    primrec₂_equalityString.comp (primrec_tokenAt 1) (primrec_tokenAt 1)
  exact ((Primrec.eq.comp Primrec.id hstage).and
      (Primrec.eq.comp hw' (Primrec.const true))).or
    (Primrec.eq.comp Primrec.id heq)

theorem primrec_axiomTest
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    Primrec (axiomTest w) :=
  PrimrecPred.decide (primrecPred_axiomShape w hw)

def specializationTheoryPresentation (w : ℕ → ℕ → Bool) :
    TheoryPresentation where
  syn := {
    formula := ⟨fun _ ↦ true⟩
    logicalAxiom := ⟨logicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def specializationPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := specializationTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_logicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem specializationAxiom_holds (w : ℕ → ℕ → Bool) (q r n m : ℕ) :
    (specializationTheoryPresentation w).syn.logicalAxiom.Holds
      (specializationAxiomString q r n m) := by
  change logicalAxiomTest (specializationAxiomString q r n m) = true
  rw [logicalAxiomTest_eq_true_iff, logicalAxiomShape_iff]
  exact Or.inl ⟨q, r, n, m, rfl⟩

theorem forwardAxiom_holds (w : ℕ → ℕ → Bool) (q r n m : ℕ) :
    (specializationTheoryPresentation w).syn.logicalAxiom.Holds
      (forwardAxiomString q r n m) := by
  change logicalAxiomTest (forwardAxiomString q r n m) = true
  rw [logicalAxiomTest_eq_true_iff, logicalAxiomShape_iff]
  exact Or.inr (Or.inl ⟨q, r, n, m, rfl⟩)

theorem reverseAxiom_holds (w : ℕ → ℕ → Bool) (q r n m : ℕ) :
    (specializationTheoryPresentation w).syn.logicalAxiom.Holds
      (reverseAxiomString q r n m) := by
  change logicalAxiomTest (reverseAxiomString q r n m) = true
  rw [logicalAxiomTest_eq_true_iff, logicalAxiomShape_iff]
  exact Or.inr (Or.inr ⟨q, r, n, m, rfl⟩)

theorem stageAxiom_holds (w : ℕ → ℕ → Bool) (a s : ℕ)
    (h : w a s = true) :
    (specializationTheoryPresentation w).ax.Holds (stageString a s) := by
  change axiomTest w (stageString a s) = true
  rw [axiomTest_eq_true_iff, axiomShape_iff]
  exact Or.inl ⟨a, s, h, rfl⟩

theorem diagonalEqualityAxiom_holds (w : ℕ → ℕ → Bool) (q : ℕ) :
    (specializationTheoryPresentation w).ax.Holds (equalityString q q) := by
  change axiomTest w (equalityString q q) = true
  rw [axiomTest_eq_true_iff, axiomShape_iff]
  exact Or.inr ⟨q, rfl⟩

/-! ## Numerical proof transformations -/

/-- The singleton proof-sequence code whose only line is `decodeFormula a`. -/
def oneLineProofCode (a : FormulaCode) : ProofSequenceCode :=
  encodeProof [decodeFormula a]

theorem primrec_oneLineProofCode : Primrec oneLineProofCode :=
  primrec_encodeProof.comp
    (Primrec.list_cons.comp primrec_decodeFormula
      (Primrec.const ([] : ProofSequence)))

private theorem isProofList_singleton
    {Th : TheoryPresentation} {φ : FormulaString}
    (hform : Th.syn.formula.Holds φ)
    (hjust : Th.syn.logicalAxiom.Holds φ ∨ Th.ax.Holds φ) :
    IsProofList Th [φ] φ := by
  refine ⟨List.cons_ne_nil _ _, rfl, ?_⟩
  intro i hi
  have hi1 : i < 1 := by simpa using hi
  have hi0 : i = 0 := by omega
  subst i
  refine ⟨by simp, by simpa using hform, ?_⟩
  simpa using hjust

theorem proof_T_oneLine_of_logicalAxiom
    {Th : TheoryPresentation} {a : FormulaCode}
    (h : Th.syn.logicalAxiom.Holds (decodeFormula a)) :
    Proof_T Th (oneLineProofCode a) a := by
  change IsProofList Th (decodeProof (oneLineProofCode a)) (decodeFormula a)
  rw [oneLineProofCode, decodeProof_encodeProof]
  exact isProofList_singleton (Th.syn.logicalAxiom_formula h) (Or.inl h)

theorem proof_T_oneLine_of_axiom
    {Th : TheoryPresentation} {a : FormulaCode}
    (h : Th.ax.Holds (decodeFormula a)) :
    Proof_T Th (oneLineProofCode a) a := by
  change IsProofList Th (decodeProof (oneLineProofCode a)) (decodeFormula a)
  rw [oneLineProofCode, decodeProof_encodeProof]
  exact isProofList_singleton (Th.ax_formula h) (Or.inr h)

def specialize (p q r n m : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (specializationAxiomCode q r n m)) p

def transferForward (p h q r n m : ℕ) : ProofSequenceCode :=
  mp
    (mp (oneLineProofCode (forwardAxiomCode q r n m))
      (specialize p q r n m))
    h

def transferReverse (p h q r n m : ℕ) : ProofSequenceCode :=
  mp
    (mp (oneLineProofCode (reverseAxiomCode q r n m))
      (specialize p q r n m))
    h

theorem proof_T_specialize
    (w : ℕ → ℕ → Bool) {p q r n m : ℕ}
    (hp : Proof_T (specializationTheoryPresentation w) p
      (equalityCode q r)) :
    Proof_T (specializationTheoryPresentation w)
      (specialize p q r n m) (instanceEqualityCode q r n m) := by
  apply proof_T_mp _ hp
  rw [← specializationAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [specializationAxiomCode, decodeFormula_encodeFormula]
  exact specializationAxiom_holds w q r n m

theorem proof_T_transferForward
    (w : ℕ → ℕ → Bool) {p h q r n m : ℕ}
    (hp : Proof_T (specializationTheoryPresentation w) p
      (equalityCode q r))
    (hh : Proof_T (specializationTheoryPresentation w) h
      (leftInstanceCode q n m)) :
    Proof_T (specializationTheoryPresentation w)
      (transferForward p h q r n m) (rightInstanceCode r n m) := by
  apply proof_T_mp _ hh
  apply proof_T_mp _ (proof_T_specialize w hp)
  rw [← forwardAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [forwardAxiomCode, decodeFormula_encodeFormula]
  exact forwardAxiom_holds w q r n m

theorem proof_T_transferReverse
    (w : ℕ → ℕ → Bool) {p h q r n m : ℕ}
    (hp : Proof_T (specializationTheoryPresentation w) p
      (equalityCode q r))
    (hh : Proof_T (specializationTheoryPresentation w) h
      (rightInstanceCode r n m)) :
    Proof_T (specializationTheoryPresentation w)
      (transferReverse p h q r n m) (leftInstanceCode q n m) := by
  apply proof_T_mp _ hh
  apply proof_T_mp _ (proof_T_specialize w hp)
  rw [← reverseAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [reverseAxiomCode, decodeFormula_encodeFormula]
  exact reverseAxiom_holds w q r n m

abbrev SpecializeArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)
abbrev TransferArgs := (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
abbrev SchemaArgs := (((ℕ × ℕ) × ℕ) × ℕ)

/-- Packed convention `((((p,q),r),n),m)`. -/
def specializePacked (z : SpecializeArgs) : ProofSequenceCode :=
  specialize z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

/-- Packed convention `(((((p,h),q),r),n),m)`. -/
def transferForwardPacked (z : TransferArgs) : ProofSequenceCode :=
  transferForward z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

/-- Packed convention `(((((p,h),q),r),n),m)`. -/
def transferReversePacked (z : TransferArgs) : ProofSequenceCode :=
  transferReverse z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

private def specializeSchemaArgs (z : SpecializeArgs) : SchemaArgs :=
  (((z.1.1.1.2, z.1.1.2), z.1.2), z.2)

private def transferSpecializeArgs (z : TransferArgs) : SpecializeArgs :=
  ((((z.1.1.1.1.1, z.1.1.1.2), z.1.1.2), z.1.2), z.2)

private def transferSchemaArgs (z : TransferArgs) : SchemaArgs :=
  (((z.1.1.1.2, z.1.1.2), z.1.2), z.2)

private theorem primrec_specializeSchemaArgs : Primrec specializeSchemaArgs := by
  exact ((((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

private theorem primrec_transferSpecializeArgs :
    Primrec transferSpecializeArgs := by
  exact (((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))).pair
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

private theorem primrec_transferSchemaArgs : Primrec transferSchemaArgs := by
  exact ((((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
    (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

theorem primrec_specialize : Primrec specializePacked := by
  have hax := primrec_specializationAxiomCode.comp primrec_specializeSchemaArgs
  exact (primrec_mp.comp (primrec_oneLineProofCode.comp hax)
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).of_eq
      (fun _ ↦ rfl)

theorem primrec_transferForward : Primrec transferForwardPacked := by
  have hp := primrec_specialize.comp primrec_transferSpecializeArgs
  have hax := primrec_forwardAxiomCode.comp primrec_transferSchemaArgs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hax) hp)
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst))))).of_eq (fun _ ↦ rfl)

theorem primrec_transferReverse : Primrec transferReversePacked := by
  have hp := primrec_specialize.comp primrec_transferSpecializeArgs
  have hax := primrec_reverseAxiomCode.comp primrec_transferSchemaArgs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hax) hp)
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst))))).of_eq (fun _ ↦ rfl)

/-! ## Arithmetic graphs of the tagged builders -/

noncomputable def taggedTwoCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (a b : V) : V :=
  listEncodeValue (ORingStructure.numeral tag ∷ a ∷ b ∷ 0)

noncomputable def taggedThreeCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (a b c : V) : V :=
  listEncodeValue (ORingStructure.numeral tag ∷ a ∷ b ∷ c ∷ 0)

noncomputable def taggedFourCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (a b c d : V) : V :=
  listEncodeValue (ORingStructure.numeral tag ∷ a ∷ b ∷ c ∷ d ∷ 0)

noncomputable def taggedTwoCodeGraph (tag : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b.
    ∃ vb, !adjoinDef vb b 0 ∧
    ∃ va, !adjoinDef va a vb ∧
    ∃ vt, !adjoinDef vt !!(tag) va ∧
      !listEncodeGraph y vt”

noncomputable def taggedThreeCodeGraph (tag : ℕ) : 𝚺₁.Semisentence 4 := .mkSigma
  “y a b c.
    ∃ vc, !adjoinDef vc c 0 ∧
    ∃ vb, !adjoinDef vb b vc ∧
    ∃ va, !adjoinDef va a vb ∧
    ∃ vt, !adjoinDef vt !!(tag) va ∧
      !listEncodeGraph y vt”

noncomputable def taggedFourCodeGraph (tag : ℕ) : 𝚺₁.Semisentence 5 := .mkSigma
  “y a b c d.
    ∃ vd, !adjoinDef vd d 0 ∧
    ∃ vc, !adjoinDef vc c vd ∧
    ∃ vb, !adjoinDef vb b vc ∧
    ∃ va, !adjoinDef va a vb ∧
    ∃ vt, !adjoinDef vt !!(tag) va ∧
      !listEncodeGraph y vt”

theorem taggedTwoCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (y a b : V) :
    Semiformula.Evalb (M := V) ![y, a, b] (taggedTwoCodeGraph tag).val ↔
      y = taggedTwoCodeValue tag a b := by
  simp [taggedTwoCodeGraph, taggedTwoCodeValue,
    listEncodeGraph_iff_listEncodeValue]

theorem taggedThreeCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (y a b c : V) :
    Semiformula.Evalb (M := V) ![y, a, b, c]
        (taggedThreeCodeGraph tag).val ↔
      y = taggedThreeCodeValue tag a b c := by
  simp [taggedThreeCodeGraph, taggedThreeCodeValue,
    listEncodeGraph_iff_listEncodeValue]

theorem taggedFourCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag : ℕ) (y a b c d : V) :
    Semiformula.Evalb (M := V) ![y, a, b, c, d]
        (taggedFourCodeGraph tag).val ↔
      y = taggedFourCodeValue tag a b c d := by
  simp [taggedFourCodeGraph, taggedFourCodeValue,
    listEncodeGraph_iff_listEncodeValue]

noncomputable def equalityCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V := taggedTwoCodeValue equalityTag q r

noncomputable def leftInstanceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q n m : V) : V := taggedThreeCodeValue leftInstanceTag q n m

noncomputable def rightInstanceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r n m : V) : V := taggedThreeCodeValue rightInstanceTag r n m

noncomputable def instanceEqualityCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) : V := taggedFourCodeValue instanceEqualityTag q r n m

noncomputable def stageCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a s : V) : V := taggedTwoCodeValue stageTag a s

noncomputable def equalityCodeGraph : 𝚺₁.Semisentence 3 :=
  taggedTwoCodeGraph equalityTag

noncomputable def leftInstanceCodeGraph : 𝚺₁.Semisentence 4 :=
  taggedThreeCodeGraph leftInstanceTag

noncomputable def rightInstanceCodeGraph : 𝚺₁.Semisentence 4 :=
  taggedThreeCodeGraph rightInstanceTag

noncomputable def instanceEqualityCodeGraph : 𝚺₁.Semisentence 5 :=
  taggedFourCodeGraph instanceEqualityTag

noncomputable def stageCodeGraph : 𝚺₁.Semisentence 3 :=
  taggedTwoCodeGraph stageTag

theorem equalityCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] equalityCodeGraph.val ↔
      y = equalityCodeValue q r := by
  simpa [equalityCodeGraph, equalityCodeValue] using
    (taggedTwoCodeGraph_iff equalityTag y q r)

theorem leftInstanceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q n m : V) :
    Semiformula.Evalb (M := V) ![y, q, n, m] leftInstanceCodeGraph.val ↔
      y = leftInstanceCodeValue q n m := by
  simpa [leftInstanceCodeGraph, leftInstanceCodeValue] using
    (taggedThreeCodeGraph_iff leftInstanceTag y q n m)

theorem rightInstanceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y r n m : V) :
    Semiformula.Evalb (M := V) ![y, r, n, m] rightInstanceCodeGraph.val ↔
      y = rightInstanceCodeValue r n m := by
  simpa [rightInstanceCodeGraph, rightInstanceCodeValue] using
    (taggedThreeCodeGraph_iff rightInstanceTag y r n m)

theorem instanceEqualityCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        instanceEqualityCodeGraph.val ↔
      y = instanceEqualityCodeValue q r n m := by
  simpa [instanceEqualityCodeGraph, instanceEqualityCodeValue] using
    (taggedFourCodeGraph_iff instanceEqualityTag y q r n m)

theorem stageCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a s : V) :
    Semiformula.Evalb (M := V) ![y, a, s] stageCodeGraph.val ↔
      y = stageCodeValue a s := by
  simpa [stageCodeGraph, stageCodeValue] using
    (taggedTwoCodeGraph_iff stageTag y a s)

noncomputable def specializationAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) : V :=
  impValue (equalityCodeValue q r) (instanceEqualityCodeValue q r n m)

noncomputable def forwardAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) : V :=
  impValue (instanceEqualityCodeValue q r n m)
    (impValue (leftInstanceCodeValue q n m) (rightInstanceCodeValue r n m))

noncomputable def reverseAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) : V :=
  impValue (instanceEqualityCodeValue q r n m)
    (impValue (rightInstanceCodeValue r n m) (leftInstanceCodeValue q n m))

noncomputable def specializationAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y q r n m.
    ∃ e, !equalityCodeGraph e q r ∧
    ∃ i, !instanceEqualityCodeGraph i q r n m ∧
      !impGraph y e i”

noncomputable def forwardAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y q r n m.
    ∃ i, !instanceEqualityCodeGraph i q r n m ∧
    ∃ f, !leftInstanceCodeGraph f q n m ∧
    ∃ g, !rightInstanceCodeGraph g r n m ∧
    ∃ c, !impGraph c f g ∧
      !impGraph y i c”

noncomputable def reverseAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y q r n m.
    ∃ i, !instanceEqualityCodeGraph i q r n m ∧
    ∃ f, !leftInstanceCodeGraph f q n m ∧
    ∃ g, !rightInstanceCodeGraph g r n m ∧
    ∃ c, !impGraph c g f ∧
      !impGraph y i c”

private theorem specializationAxiomCodeGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        specializationAxiomCodeGraph.val ↔
      ∃ e : V,
        Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val ∧
      ∃ i : V,
        Semiformula.Evalb (M := V) ![i, q, r, n, m]
          instanceEqualityCodeGraph.val ∧
        Semiformula.Evalb (M := V) ![y, e, i] impGraph.val := by
  simp [specializationAxiomCodeGraph]
  apply exists_congr
  intro e
  apply and_congr Iff.rfl
  apply exists_congr
  intro i
  apply and_congr ?_ Iff.rfl
  apply Iff.of_eq
  congr 2
  funext j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j

private theorem forwardAxiomCodeGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        forwardAxiomCodeGraph.val ↔
      ∃ i : V,
        Semiformula.Evalb (M := V) ![i, q, r, n, m]
          instanceEqualityCodeGraph.val ∧
      ∃ f : V,
        Semiformula.Evalb (M := V) ![f, q, n, m]
          leftInstanceCodeGraph.val ∧
      ∃ g : V,
        Semiformula.Evalb (M := V) ![g, r, n, m]
          rightInstanceCodeGraph.val ∧
      ∃ c : V,
        Semiformula.Evalb (M := V) ![c, f, g] impGraph.val ∧
        Semiformula.Evalb (M := V) ![y, i, c] impGraph.val := by
  simp [forwardAxiomCodeGraph]
  apply exists_congr
  intro i
  apply and_congr ?_ Iff.rfl
  apply Iff.of_eq
  congr 2
  funext j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j

private theorem reverseAxiomCodeGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        reverseAxiomCodeGraph.val ↔
      ∃ i : V,
        Semiformula.Evalb (M := V) ![i, q, r, n, m]
          instanceEqualityCodeGraph.val ∧
      ∃ f : V,
        Semiformula.Evalb (M := V) ![f, q, n, m]
          leftInstanceCodeGraph.val ∧
      ∃ g : V,
        Semiformula.Evalb (M := V) ![g, r, n, m]
          rightInstanceCodeGraph.val ∧
      ∃ c : V,
        Semiformula.Evalb (M := V) ![c, g, f] impGraph.val ∧
        Semiformula.Evalb (M := V) ![y, i, c] impGraph.val := by
  simp [reverseAxiomCodeGraph]
  apply exists_congr
  intro i
  apply and_congr ?_ Iff.rfl
  apply Iff.of_eq
  congr 2
  funext j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j

theorem specializationAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        specializationAxiomCodeGraph.val ↔
      y = specializationAxiomCodeValue q r n m := by
  rw [specializationAxiomCodeGraph_raw_iff]
  simp [specializationAxiomCodeValue, equalityCodeGraph_iff,
    instanceEqualityCodeGraph_iff, impGraph_iff_impValue]

theorem forwardAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        forwardAxiomCodeGraph.val ↔
      y = forwardAxiomCodeValue q r n m := by
  rw [forwardAxiomCodeGraph_raw_iff]
  simp [forwardAxiomCodeValue, instanceEqualityCodeGraph_iff,
    leftInstanceCodeGraph_iff, rightInstanceCodeGraph_iff,
    impGraph_iff_impValue]

theorem reverseAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r n m : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n, m]
        reverseAxiomCodeGraph.val ↔
      y = reverseAxiomCodeValue q r n m := by
  rw [reverseAxiomCodeGraph_raw_iff]
  simp [reverseAxiomCodeValue, instanceEqualityCodeGraph_iff,
    leftInstanceCodeGraph_iff, rightInstanceCodeGraph_iff,
    impGraph_iff_impValue]

/-! ### Standard-model agreement for formula-code builders -/

theorem equalityCodeValue_nat (q r : ℕ) :
    equalityCodeValue q r = equalityCode q r := by
  simpa [equalityCodeValue, taggedTwoCodeValue, equalityCode, equalityString,
    encodeFormula] using
      (listEncodeValue_natVecOfList [equalityTag, q, r])

theorem leftInstanceCodeValue_nat (q n m : ℕ) :
    leftInstanceCodeValue q n m = leftInstanceCode q n m := by
  simpa [leftInstanceCodeValue, taggedThreeCodeValue, leftInstanceCode,
    leftInstanceString, encodeFormula] using
      (listEncodeValue_natVecOfList [leftInstanceTag, q, n, m])

theorem rightInstanceCodeValue_nat (r n m : ℕ) :
    rightInstanceCodeValue r n m = rightInstanceCode r n m := by
  simpa [rightInstanceCodeValue, taggedThreeCodeValue, rightInstanceCode,
    rightInstanceString, encodeFormula] using
      (listEncodeValue_natVecOfList [rightInstanceTag, r, n, m])

theorem instanceEqualityCodeValue_nat (q r n m : ℕ) :
    instanceEqualityCodeValue q r n m = instanceEqualityCode q r n m := by
  simpa [instanceEqualityCodeValue, taggedFourCodeValue, instanceEqualityCode,
    instanceEqualityString, encodeFormula] using
      (listEncodeValue_natVecOfList [instanceEqualityTag, q, r, n, m])

theorem stageCodeValue_nat (a s : ℕ) :
    stageCodeValue a s = stageCode a s := by
  simpa [stageCodeValue, taggedTwoCodeValue, stageCode, stageString,
    encodeFormula] using
      (listEncodeValue_natVecOfList [stageTag, a, s])

theorem specializationAxiomCodeValue_nat (q r n m : ℕ) :
    specializationAxiomCodeValue q r n m =
      specializationAxiomCode q r n m := by
  rw [specializationAxiomCodeValue, impValue_nat,
    equalityCodeValue_nat, instanceEqualityCodeValue_nat,
    specializationAxiomCode_eq_imp]

theorem forwardAxiomCodeValue_nat (q r n m : ℕ) :
    forwardAxiomCodeValue q r n m = forwardAxiomCode q r n m := by
  rw [forwardAxiomCodeValue, impValue_nat, impValue_nat,
    instanceEqualityCodeValue_nat, leftInstanceCodeValue_nat,
    rightInstanceCodeValue_nat, forwardAxiomCode_eq_imp]

theorem reverseAxiomCodeValue_nat (q r n m : ℕ) :
    reverseAxiomCodeValue q r n m = reverseAxiomCode q r n m := by
  rw [reverseAxiomCodeValue, impValue_nat, impValue_nat,
    instanceEqualityCodeValue_nat, leftInstanceCodeValue_nat,
    rightInstanceCodeValue_nat, reverseAxiomCode_eq_imp]

/-! ## Graphs of the proof transformations -/

noncomputable def oneLineProofValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) : V :=
  listEncodeValue (a ∷ 0)

noncomputable def oneLineProofGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y a.
    ∃ v, !adjoinDef v a 0 ∧
      !listEncodeGraph y v”

theorem oneLineProofGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a : V) :
    Semiformula.Evalb (M := V) ![y, a] oneLineProofGraph.val ↔
      y = oneLineProofValue a := by
  simp [oneLineProofGraph, oneLineProofValue,
    listEncodeGraph_iff_listEncodeValue]

theorem oneLineProofValue_nat (a : ℕ) :
    oneLineProofValue a = oneLineProofCode a := by
  rw [oneLineProofValue, show a ∷ (0 : ℕ) = natVecOfList [a] from rfl,
    listEncodeValue_natVecOfList]
  simp [oneLineProofCode, encodeProof]

theorem mpValue_nat (r p : ℕ) :
    mpValue r p = mp r p := by
  rw [mpValue, listDecodeValue_nat r, listDecodeValue_nat p,
    lastValue_natVecOfList, rhsValue_nat]
  change listEncodeValue
      (vecAppendValue (natVecOfList (listDecode r))
        (vecAppendValue (natVecOfList (listDecode p))
          (natVecOfList [rhs ((listDecode r).getLastD 0)]))) = mp r p
  rw [vecAppendValue_natVecOfList, vecAppendValue_natVecOfList,
    listEncodeValue_natVecOfList]
  have hlast :
      (Option.map decodeFormula (listDecode r).getLast?).getD [] =
        decodeFormula ((listDecode r).getLast?.getD 0) := by
    cases (listDecode r).getLast? <;> simp [decodeFormula]
  simp [mp, mpList, encodeProof, decodeProof, rhs, List.map_append,
    Function.comp_def, List.append_assoc, hlast]

noncomputable def specializeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p q r n m : V) : V :=
  mpValue (oneLineProofValue (specializationAxiomCodeValue q r n m)) p

noncomputable def transferForwardValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p h q r n m : V) : V :=
  mpValue
    (mpValue (oneLineProofValue (forwardAxiomCodeValue q r n m))
      (specializeValue p q r n m))
    h

noncomputable def transferReverseValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p h q r n m : V) : V :=
  mpValue
    (mpValue (oneLineProofValue (reverseAxiomCodeValue q r n m))
      (specializeValue p q r n m))
    h

noncomputable def specializeGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y p q r n m.
    ∃ c, !specializationAxiomCodeGraph c q r n m ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def transferForwardGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y p h q r n m.
    ∃ s, !specializeGraph s p q r n m ∧
    ∃ c, !forwardAxiomCodeGraph c q r n m ∧
    ∃ u, !oneLineProofGraph u c ∧
    ∃ d, !mpGraph d u s ∧
      !mpGraph y d h”

noncomputable def transferReverseGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y p h q r n m.
    ∃ s, !specializeGraph s p q r n m ∧
    ∃ c, !reverseAxiomCodeGraph c q r n m ∧
    ∃ u, !oneLineProofGraph u c ∧
    ∃ d, !mpGraph d u s ∧
      !mpGraph y d h”

private theorem specializeGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n, m] specializeGraph.val ↔
      ∃ c : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          specializationAxiomCodeGraph.val ∧
      ∃ u : V,
        Semiformula.Evalb (M := V) ![u, c] oneLineProofGraph.val ∧
        Semiformula.Evalb (M := V) ![y, u, p] mpGraph.val := by
  simp [specializeGraph]
  apply exists_congr
  intro c
  apply and_congr ?_ Iff.rfl
  apply Iff.of_eq
  congr 2
  funext j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ ?_) j
  refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j

private theorem transferForwardGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, h, q, r, n, m]
        transferForwardGraph.val ↔
      ∃ s : V,
        Semiformula.Evalb (M := V) ![s, p, q, r, n, m] specializeGraph.val ∧
      ∃ c : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          forwardAxiomCodeGraph.val ∧
      ∃ u : V,
        Semiformula.Evalb (M := V) ![u, c] oneLineProofGraph.val ∧
      ∃ d : V,
        Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val ∧
        Semiformula.Evalb (M := V) ![y, d, h] mpGraph.val := by
  simp [transferForwardGraph]
  apply exists_congr
  intro s
  apply and_congr
  · exact Iff.of_eq (congrArg
      (fun e ↦ Semiformula.Evalb (M := V) e specializeGraph.val)
      (by
        funext j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
  · apply exists_congr
    intro c
    apply and_congr
    · exact Iff.of_eq (congrArg
        (fun e ↦ Semiformula.Evalb (M := V) e forwardAxiomCodeGraph.val)
        (by
          funext j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
    · exact Iff.rfl

private theorem transferReverseGraph_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, h, q, r, n, m]
        transferReverseGraph.val ↔
      ∃ s : V,
        Semiformula.Evalb (M := V) ![s, p, q, r, n, m] specializeGraph.val ∧
      ∃ c : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          reverseAxiomCodeGraph.val ∧
      ∃ u : V,
        Semiformula.Evalb (M := V) ![u, c] oneLineProofGraph.val ∧
      ∃ d : V,
        Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val ∧
        Semiformula.Evalb (M := V) ![y, d, h] mpGraph.val := by
  simp [transferReverseGraph]
  apply exists_congr
  intro s
  apply and_congr
  · exact Iff.of_eq (congrArg
      (fun e ↦ Semiformula.Evalb (M := V) e specializeGraph.val)
      (by
        funext j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
  · apply exists_congr
    intro c
    apply and_congr
    · exact Iff.of_eq (congrArg
        (fun e ↦ Semiformula.Evalb (M := V) e reverseAxiomCodeGraph.val)
        (by
          funext j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
    · exact Iff.rfl

theorem specializeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n, m] specializeGraph.val ↔
      y = specializeValue p q r n m := by
  rw [specializeGraph_raw_iff]
  simp [specializeValue, specializationAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem transferForwardGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, h, q, r, n, m]
        transferForwardGraph.val ↔
      y = transferForwardValue p h q r n m := by
  rw [transferForwardGraph_raw_iff]
  simp [transferForwardValue, specializeGraph_iff,
    forwardAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem transferReverseGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h q r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, h, q, r, n, m]
        transferReverseGraph.val ↔
      y = transferReverseValue p h q r n m := by
  rw [transferReverseGraph_raw_iff]
  simp [transferReverseValue, specializeGraph_iff,
    reverseAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem specializeValue_nat (p q r n m : ℕ) :
    specializeValue p q r n m = specialize p q r n m := by
  simp [specializeValue, specialize, oneLineProofValue_nat,
    specializationAxiomCodeValue_nat, mpValue_nat]

theorem transferForwardValue_nat (p h q r n m : ℕ) :
    transferForwardValue p h q r n m = transferForward p h q r n m := by
  simp [transferForwardValue, transferForward, specializeValue_nat,
    oneLineProofValue_nat, forwardAxiomCodeValue_nat, mpValue_nat]

theorem transferReverseValue_nat (p h q r n m : ℕ) :
    transferReverseValue p h q r n m = transferReverse p h q r n m := by
  simp [transferReverseValue, transferReverse, specializeValue_nat,
    oneLineProofValue_nat, reverseAxiomCodeValue_nat, mpValue_nat]

/-! ## The explicit logical-axiom leaf -/

noncomputable def specializationLogicalAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c.
    (∃ q r n m, !specializationAxiomCodeGraph c q r n m) ∨
    (∃ q r n m, !forwardAxiomCodeGraph c q r n m) ∨
    (∃ q r n m, !reverseAxiomCodeGraph c q r n m)”

private theorem specializationLogicalAxiomLeaf_raw_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] specializationLogicalAxiomLeaf.val ↔
      (∃ q r n m : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          specializationAxiomCodeGraph.val) ∨
      (∃ q r n m : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          forwardAxiomCodeGraph.val) ∨
      (∃ q r n m : V,
        Semiformula.Evalb (M := V) ![c, q, r, n, m]
          reverseAxiomCodeGraph.val) := by
  simp [specializationLogicalAxiomLeaf]
  apply or_congr
  · apply exists_congr
    intro q
    apply exists_congr
    intro r
    apply exists_congr
    intro n
    apply exists_congr
    intro m
    exact Iff.of_eq (congrArg
      (fun e ↦ Semiformula.Evalb (M := V) e specializationAxiomCodeGraph.val)
      (by
        funext j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ ?_) j
        refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
  · apply or_congr
    · apply exists_congr
      intro q
      apply exists_congr
      intro r
      apply exists_congr
      intro n
      apply exists_congr
      intro m
      exact Iff.of_eq (congrArg
        (fun e ↦ Semiformula.Evalb (M := V) e forwardAxiomCodeGraph.val)
        (by
          funext j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))
    · apply exists_congr
      intro q
      apply exists_congr
      intro r
      apply exists_congr
      intro n
      apply exists_congr
      intro m
      exact Iff.of_eq (congrArg
        (fun e ↦ Semiformula.Evalb (M := V) e reverseAxiomCodeGraph.val)
        (by
          funext j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ ?_) j
          refine Fin.cases rfl (fun j ↦ Fin.elim0 j) j))

theorem specializationLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] specializationLogicalAxiomLeaf.val ↔
      (∃ q r n m : V, c = specializationAxiomCodeValue q r n m) ∨
      (∃ q r n m : V, c = forwardAxiomCodeValue q r n m) ∨
      (∃ q r n m : V, c = reverseAxiomCodeValue q r n m) := by
  rw [specializationLogicalAxiomLeaf_raw_iff]
  simp [specializationAxiomCodeGraph_iff, forwardAxiomCodeGraph_iff,
    reverseAxiomCodeGraph_iff]

theorem specializationLogicalAxiomLeaf_specialization
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V) ![specializationAxiomCodeValue q r n m]
      specializationLogicalAxiomLeaf.val :=
  (specializationLogicalAxiomLeaf_iff _).mpr
    (Or.inl ⟨q, r, n, m, rfl⟩)

theorem specializationLogicalAxiomLeaf_forward
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V) ![forwardAxiomCodeValue q r n m]
      specializationLogicalAxiomLeaf.val :=
  (specializationLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inl ⟨q, r, n, m, rfl⟩))

theorem specializationLogicalAxiomLeaf_reverse
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V) ![reverseAxiomCodeValue q r n m]
      specializationLogicalAxiomLeaf.val :=
  (specializationLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr ⟨q, r, n, m, rfl⟩))

theorem specializationLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c] specializationLogicalAxiomLeaf.val ↔
      (specializationTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [specializationLogicalAxiomLeaf_iff]
  simp only [specializationAxiomCodeValue_nat, forwardAxiomCodeValue_nat,
    reverseAxiomCodeValue_nat]
  change _ ↔ logicalAxiomTest (decodeFormula c) = true
  rw [logicalAxiomTest_eq_true_iff, logicalAxiomShape_iff]
  have hcode (s : FormulaString) :
      c = encodeFormula s ↔ decodeFormula c = s := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula s
    · intro h
      calc
        c = encodeFormula (decodeFormula c) :=
          (encodeFormula_decodeFormula c).symm
        _ = encodeFormula s := by rw [h]
  simp only [specializationAxiomCode, forwardAxiomCode, reverseAxiomCode,
    hcode]

theorem specializationProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (proofGraphWithLogicalAxiom
          (specializationPRTheoryPresentation w hw)
          specializationLogicalAxiomLeaf).val ↔
      Proof_T (specializationTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (specializationPRTheoryPresentation w hw)
    specializationLogicalAxiomLeaf
    (specializationLogicalAxiomLeaf_nat_iff w) p a

/-! ## Proof preservation in arbitrary arithmetic models -/

theorem proofGraphWithLogicalAxiom_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      specializationLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th specializationLogicalAxiomLeaf).val := by
  rw [proofGraphWithLogicalAxiom_iff]
  have hdecode : listDecodeValue (oneLineProofValue a) = a ∷ (0 : V) := by
    exact listDecodeValue_leftInverse (a ∷ (0 : V))
  rw [hdecode]
  refine ⟨by simp, ?_, ?_⟩
  · simp [lastValue, takeLast_adjoin]
  · intro i hi
    have hi' : i < (1 : V) := by simpa using hi
    have hi0 : i = 0 :=
      le_antisymm (lt_succ_iff_le.mp (by simpa using hi'))
        (Arithmetic.zero_le i)
    subst i
    rw [lineCheckWithLogicalAxiom_iff]
    exact ⟨a, by simp, Or.inl ha⟩

noncomputable def specializationProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (specializationPRTheoryPresentation w hw)
    specializationLogicalAxiomLeaf

theorem proofGraph_of_specializeGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2))
    (p q r n m e i s : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hi : Semiformula.Evalb (M := V) ![i, q, r, n, m]
      instanceEqualityCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (specializationProofGraph w hw).val)
    (hs : Semiformula.Evalb (M := V) ![s, p, q, r, n, m]
      specializeGraph.val) :
    Semiformula.Evalb (M := V) ![s, i]
      (specializationProofGraph w hw).val := by
  have heq : e = equalityCodeValue q r :=
    (equalityCodeGraph_iff e q r).mp he
  have hiq : i = instanceEqualityCodeValue q r n m :=
    (instanceEqualityCodeGraph_iff i q r n m).mp hi
  have hsq : s = specializeValue p q r n m :=
    (specializeGraph_iff s p q r n m).mp hs
  subst e
  subst i
  subst s
  let Th := specializationPRTheoryPresentation w hw
  let c := specializationAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V)
      ![c, equalityCodeValue q r, instanceEqualityCodeValue q r n m]
      impGraph.val := by
    exact (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th specializationLogicalAxiomLeaf).val := by
    exact proofGraphWithLogicalAxiom_oneLine Th c
      (specializationLogicalAxiomLeaf_specialization q r n m)
  have hmp : Semiformula.Evalb (M := V)
      ![specializeValue p q r n m, u, p] mpGraph.val := by
    exact (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th specializationLogicalAxiomLeaf
    p (equalityCodeValue q r) c (instanceEqualityCodeValue q r n m)
    u (specializeValue p q r n m) hp hc hu hmp

theorem proofGraph_of_transferForwardGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2))
    (p h q r n m e f g t : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (specializationProofGraph w hw).val)
    (hh : Semiformula.Evalb (M := V) ![h, f]
      (specializationProofGraph w hw).val)
    (ht : Semiformula.Evalb (M := V) ![t, p, h, q, r, n, m]
      transferForwardGraph.val) :
    Semiformula.Evalb (M := V) ![t, g]
      (specializationProofGraph w hw).val := by
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hfq := (leftInstanceCodeGraph_iff f q n m).mp hf
  have hgq := (rightInstanceCodeGraph_iff g r n m).mp hg
  have htq := (transferForwardGraph_iff t p h q r n m).mp ht
  subst e
  subst f
  subst g
  subst t
  let Th := specializationPRTheoryPresentation w hw
  let prf := proofGraphWithLogicalAxiom Th specializationLogicalAxiomLeaf
  let i := instanceEqualityCodeValue (V := V) q r n m
  let f := leftInstanceCodeValue (V := V) q n m
  let g := rightInstanceCodeValue (V := V) r n m
  let c := forwardAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  let s := specializeValue (V := V) p q r n m
  let d := mpValue u s
  have hs : Semiformula.Evalb (M := V) ![s, i] prf.val := by
    exact proofGraph_of_specializeGraph w hw p q r n m
      (equalityCodeValue q r) i s
      ((equalityCodeGraph_iff _ _ _).mpr rfl)
      ((instanceEqualityCodeGraph_iff _ _ _ _ _).mpr rfl) hp
      ((specializeGraph_iff _ _ _ _ _ _).mpr rfl)
  have hu : Semiformula.Evalb (M := V) ![u, c] prf.val := by
    exact proofGraphWithLogicalAxiom_oneLine Th c
      (specializationLogicalAxiomLeaf_forward q r n m)
  have hc : Semiformula.Evalb (M := V) ![c, i, impValue f g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hdmp : Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hd : Semiformula.Evalb (M := V) ![d, impValue f g] prf.val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th specializationLogicalAxiomLeaf
      s i c (impValue f g) u d hs hc hu hdmp
  have hfg : Semiformula.Evalb (M := V) ![impValue f g, f, g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hout : Semiformula.Evalb (M := V)
      ![transferForwardValue p h q r n m, d, h] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th specializationLogicalAxiomLeaf
    h f (impValue f g) g d (transferForwardValue p h q r n m)
    hh hfg hd hout

theorem proofGraph_of_transferReverseGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2))
    (p h q r n m e f g t : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (specializationProofGraph w hw).val)
    (hh : Semiformula.Evalb (M := V) ![h, g]
      (specializationProofGraph w hw).val)
    (ht : Semiformula.Evalb (M := V) ![t, p, h, q, r, n, m]
      transferReverseGraph.val) :
    Semiformula.Evalb (M := V) ![t, f]
      (specializationProofGraph w hw).val := by
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hfq := (leftInstanceCodeGraph_iff f q n m).mp hf
  have hgq := (rightInstanceCodeGraph_iff g r n m).mp hg
  have htq := (transferReverseGraph_iff t p h q r n m).mp ht
  subst e
  subst f
  subst g
  subst t
  let Th := specializationPRTheoryPresentation w hw
  let prf := proofGraphWithLogicalAxiom Th specializationLogicalAxiomLeaf
  let i := instanceEqualityCodeValue (V := V) q r n m
  let f := leftInstanceCodeValue (V := V) q n m
  let g := rightInstanceCodeValue (V := V) r n m
  let c := reverseAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  let s := specializeValue (V := V) p q r n m
  let d := mpValue u s
  have hs : Semiformula.Evalb (M := V) ![s, i] prf.val := by
    exact proofGraph_of_specializeGraph w hw p q r n m
      (equalityCodeValue q r) i s
      ((equalityCodeGraph_iff _ _ _).mpr rfl)
      ((instanceEqualityCodeGraph_iff _ _ _ _ _).mpr rfl) hp
      ((specializeGraph_iff _ _ _ _ _ _).mpr rfl)
  have hu : Semiformula.Evalb (M := V) ![u, c] prf.val := by
    exact proofGraphWithLogicalAxiom_oneLine Th c
      (specializationLogicalAxiomLeaf_reverse q r n m)
  have hc : Semiformula.Evalb (M := V) ![c, i, impValue g f] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hdmp : Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hd : Semiformula.Evalb (M := V) ![d, impValue g f] prf.val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th specializationLogicalAxiomLeaf
      s i c (impValue g f) u d hs hc hu hdmp
  have hgf : Semiformula.Evalb (M := V) ![impValue g f, g, f] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hout : Semiformula.Evalb (M := V)
      ![transferReverseValue p h q r n m, d, h] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th specializationLogicalAxiomLeaf
    h g (impValue g f) f d (transferReverseValue p h q r n m)
    hh hgf hd hout

/-! ## Uniform preservation sentences -/

noncomputable def specializationPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSemisentence 8 :=
  let prf := specializationProofGraph w hw
  “p q r n m e i s.
    !equalityCodeGraph e q r ∧
    !instanceEqualityCodeGraph i q r n m ∧
    !prf p e ∧
    !specializeGraph s p q r n m →
    !prf s i”

noncomputable def forwardTransferPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSemisentence 10 :=
  let prf := specializationProofGraph w hw
  “p h q r n m e f g t.
    !equalityCodeGraph e q r ∧
    !leftInstanceCodeGraph f q n m ∧
    !rightInstanceCodeGraph g r n m ∧
    !prf p e ∧
    !prf h f ∧
    !transferForwardGraph t p h q r n m →
    !prf t g”

noncomputable def reverseTransferPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSemisentence 10 :=
  let prf := specializationProofGraph w hw
  “p h q r n m e f g t.
    !equalityCodeGraph e q r ∧
    !leftInstanceCodeGraph f q n m ∧
    !rightInstanceCodeGraph g r n m ∧
    !prf p e ∧
    !prf h g ∧
    !transferReverseGraph t p h q r n m →
    !prf t f”

/-- The universal closure is kept separate from the eight-place matrix.  This
avoids constructing a deeply nested substitution environment when the
semantic preservation theorem is elaborated. -/
noncomputable def uniformSpecializationPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSentence :=
  ∀¹* specializationPreservationMatrix w hw

noncomputable def uniformForwardTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSentence :=
  ∀¹* forwardTransferPreservationMatrix w hw

noncomputable def uniformReverseTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) : ArithmeticSentence :=
  ∀¹* reverseTransferPreservationMatrix w hw

theorem models_uniformSpecializationPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformSpecializationPreservation w hw := by
  rw [models_iff, uniformSpecializationPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [specializationPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact proofGraph_of_specializeGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    h.1 h.2.1 h.2.2.1 h.2.2.2

theorem models_uniformForwardTransferPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformForwardTransferPreservation w hw := by
  rw [models_iff, uniformForwardTransferPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [forwardTransferPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact proofGraph_of_transferForwardGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem models_uniformReverseTransferPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformReverseTransferPreservation w hw := by
  rw [models_iff, uniformReverseTransferPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [reverseTransferPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact proofGraph_of_transferReverseGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem provable_PA_uniformSpecializationPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformSpecializationPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_uniformSpecializationPreservation (V := V) w hw

theorem provable_PA_uniformForwardTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformForwardTransferPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_uniformForwardTransferPreservation (V := V) w hw

theorem provable_PA_uniformReverseTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformReverseTransferPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_uniformReverseTransferPreservation (V := V) w hw

end Arith.Feferman.Specialization
