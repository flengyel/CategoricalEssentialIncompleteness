/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.ProofSearchMembership

/-!
# An additive checker for equality-proof transport

The production `PrfEq` checker has modus ponens, but it has no logical-axiom
scheme whose conclusion transports two equality tags.  This module leaves that
checker unchanged and defines a separately named extension with exactly one new
scheme:

`E(y,y') -> E(y,d) -> E(y',d)`.

The resulting proof-code constructor is total and primitive recursive in both
input proof codes and all three program indices.  Its correctness theorem is
deliberately about `transportRepairTheoryPresentation`, not the production
presentation.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.PrfEqTransportRepair

open NumericalProofBridge NumericalSpecialization ProofSearch
open ProofSearchMembership UniformIndexQuotient

/-! ## The direct transport scheme and its recognizer -/

/-- The direct equality-tag transport scheme.  All three indices are external
natural-number parameters at this numerical layer. -/
def transportAxiomString (y y' d : ℕ) : FormulaString :=
  impString (equalityString y y')
    (impString (equalityString y d) (equalityString y' d))

def transportAxiomCode (y y' d : ℕ) : FormulaCode :=
  encodeFormula (transportAxiomString y y' d)

@[simp] theorem transportAxiomCode_eq_imp (y y' d : ℕ) :
    transportAxiomCode y y' d =
      imp (equalityCode y y')
        (imp (equalityCode y d) (equalityCode y' d)) := by
  unfold transportAxiomCode transportAxiomString Metamath.Feferman.imp
  simp only [equalityCode, decodeFormula_encodeFormula]

abbrev TransportSchemaArgs := (ℕ × ℕ) × ℕ

theorem primrec_transportAxiomString :
    Primrec (fun z : TransportSchemaArgs =>
      transportAxiomString z.1.1 z.1.2 z.2) := by
  have hy : Primrec (fun z : TransportSchemaArgs => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hy' : Primrec (fun z : TransportSchemaArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun z : TransportSchemaArgs => z.2) := Primrec.snd
  exact primrec_impString.comp
    (primrec₂_equalityString.comp hy hy')
    (primrec_impString.comp
      (primrec₂_equalityString.comp hy hd)
      (primrec₂_equalityString.comp hy' hd))

theorem primrec_transportAxiomCode :
    Primrec (fun z : TransportSchemaArgs =>
      transportAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_transportAxiomString

def transportTokenAt (i : ℕ) (s : FormulaString) : ℕ :=
  s.getD i 0

private theorem primrec_transportTokenAt (i : ℕ) :
    Primrec (transportTokenAt i) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)

def recoveredTransportLeft (s : FormulaString) : ℕ :=
  transportTokenAt 1 (lhsString s)

def recoveredTransportMiddle (s : FormulaString) : ℕ :=
  transportTokenAt 2 (lhsString s)

def recoveredTransportRight (s : FormulaString) : ℕ :=
  transportTokenAt 2 (lhsString (rhsString s))

private theorem primrec_recoveredTransportLeft :
    Primrec recoveredTransportLeft :=
  (primrec_transportTokenAt 1).comp primrec_lhsString

private theorem primrec_recoveredTransportMiddle :
    Primrec recoveredTransportMiddle :=
  (primrec_transportTokenAt 2).comp primrec_lhsString

private theorem primrec_recoveredTransportRight :
    Primrec recoveredTransportRight :=
  (primrec_transportTokenAt 2).comp
    (primrec_lhsString.comp primrec_rhsString)

def transportAxiomCandidate (s : FormulaString) : FormulaString :=
  transportAxiomString (recoveredTransportLeft s)
    (recoveredTransportMiddle s) (recoveredTransportRight s)

private theorem primrec_transportAxiomCandidate :
    Primrec transportAxiomCandidate := by
  have hargs : Primrec (fun s : FormulaString =>
      ((recoveredTransportLeft s, recoveredTransportMiddle s),
        recoveredTransportRight s)) :=
    (primrec_recoveredTransportLeft.pair
      primrec_recoveredTransportMiddle).pair primrec_recoveredTransportRight
  exact (primrec_transportAxiomString.comp hargs).of_eq (fun _ => rfl)

def TransportAxiomShape (s : FormulaString) : Prop :=
  s = transportAxiomCandidate s

def transportAxiomTest (s : FormulaString) : Bool :=
  s == transportAxiomCandidate s

@[simp] theorem transportAxiomTest_eq_true_iff (s : FormulaString) :
    transportAxiomTest s = true ↔ TransportAxiomShape s := by
  simp [transportAxiomTest, TransportAxiomShape]

theorem transportAxiomShape_iff (s : FormulaString) :
    TransportAxiomShape s ↔
      ∃ y y' d, s = transportAxiomString y y' d := by
  constructor
  · intro h
    exact ⟨recoveredTransportLeft s, recoveredTransportMiddle s,
      recoveredTransportRight s, h⟩
  · rintro ⟨y, y', d, rfl⟩
    simp [TransportAxiomShape, transportAxiomCandidate,
      recoveredTransportLeft, recoveredTransportMiddle,
      recoveredTransportRight, transportTokenAt, transportAxiomString,
      equalityString]

theorem primrec_transportAxiomTest : Primrec transportAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_transportAxiomCandidate).of_eq
    (fun s => by simp [transportAxiomTest])

/-! ## The additive presentation -/

def TransportRepairLogicalAxiomShape (s : FormulaString) : Prop :=
  ExtendedLogicalAxiomShape s ∨ TransportAxiomShape s

def transportRepairLogicalAxiomTest (s : FormulaString) : Bool :=
  extendedLogicalAxiomTest s || transportAxiomTest s

@[simp] theorem transportRepairLogicalAxiomTest_eq_true_iff
    (s : FormulaString) :
    transportRepairLogicalAxiomTest s = true ↔
      TransportRepairLogicalAxiomShape s := by
  simp [transportRepairLogicalAxiomTest, TransportRepairLogicalAxiomShape]

theorem primrec_transportRepairLogicalAxiomTest :
    Primrec transportRepairLogicalAxiomTest :=
  Primrec.or.comp primrec_extendedLogicalAxiomTest
    primrec_transportAxiomTest

/-- The production extended presentation plus the direct transport scheme.
The formula and theory-axiom tests are unchanged. -/
def transportRepairTheoryPresentation (w : ℕ → ℕ → Bool) :
    TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨transportRepairLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def transportRepairPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := transportRepairTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_transportRepairLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem extendedLogicalAxiom_holds_transportRepair
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds s) :
    (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change extendedLogicalAxiomTest s = true at h
  change transportRepairLogicalAxiomTest s = true
  simp [transportRepairLogicalAxiomTest, h]

private theorem transportAxiomShape_holds
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : TransportAxiomShape s) :
    (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change transportRepairLogicalAxiomTest s = true
  exact (transportRepairLogicalAxiomTest_eq_true_iff s).mpr (Or.inr h)

theorem transportAxiom_holds
    (w : ℕ → ℕ → Bool) (y y' d : ℕ) :
    (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds
      (transportAxiomString y y' d) := by
  apply transportAxiomShape_holds
  rw [transportAxiomShape_iff]
  exact ⟨y, y', d, rfl⟩

/-- Production extended proofs embed into the repair checker without changing
their numerical proof codes. -/
theorem proof_T_extended_to_transportRepair
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (transportRepairTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro i hi
  obtain ⟨hline, _hformula, hcase⟩ := hj i hi
  refine ⟨hline, ?_, ?_⟩
  · simp [transportRepairTheoryPresentation, StringPredicate.Holds]
  · rcases hcase with hlog | hax | hmp
    · exact Or.inl (extendedLogicalAxiom_holds_transportRepair w hlog)
    · exact Or.inr (Or.inl (by
        simpa [extendedTheoryPresentation, transportRepairTheoryPresentation]
          using hax))
    · exact Or.inr (Or.inr hmp)

/-! ## The total proof-code constructor -/

/-- Two numerical applications of modus ponens to a one-line scheme proof.
The function is total; malformed input proof codes are merely outside the
hypotheses of its correctness theorem. -/
def transport (e p y y' d : ℕ) : ProofSequenceCode :=
  mp (mp (oneLineProofCode (transportAxiomCode y y' d)) e) p

theorem proof_T_transport
    (w : ℕ → ℕ → Bool) {e p y y' d : ℕ}
    (he : Proof_T (transportRepairTheoryPresentation w) e
      (equalityCode y y'))
    (hp : Proof_T (transportRepairTheoryPresentation w) p
      (equalityCode y d)) :
    Proof_T (transportRepairTheoryPresentation w) (transport e p y y' d)
      (equalityCode y' d) := by
  apply proof_T_mp _ hp
  apply proof_T_mp _ he
  rw [← transportAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [transportAxiomCode, decodeFormula_encodeFormula]
  exact transportAxiom_holds w y y' d

/-- Packed in the production order `((((e,p),y),y'),d)`. -/
def transportPacked (z : PrfEqTransportArgs) : ProofSequenceCode :=
  transport z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

theorem primrec_transport : Primrec transportPacked := by
  have he : Primrec (fun z : PrfEqTransportArgs => z.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec (fun z : PrfEqTransportArgs => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hy : Primrec (fun z : PrfEqTransportArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hy' : Primrec (fun z : PrfEqTransportArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun z : PrfEqTransportArgs => z.2) := Primrec.snd
  have hargs : Primrec (fun z : PrfEqTransportArgs =>
      ((z.1.1.2, z.1.2), z.2)) := (hy.pair hy').pair hd
  have hax := primrec_transportAxiomCode.comp hargs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hax) he) hp).of_eq
      (fun _ => rfl)

/-! ## The repaired endpoint for an r.e. theory -/

noncomputable def reTheoryTransportRepairPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  transportRepairTheoryPresentation (reTheoryStageWitness T hRE)

def RepairPrfEq
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : ℕ) : Prop :=
  Proof_T (reTheoryTransportRepairPresentation T hRE) p
    (equalityCode q r)

theorem prfEq_to_repairPrfEq
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r : ℕ} (hp : PrfEq T hRE p q r) :
    RepairPrfEq T hRE p q r := by
  exact proof_T_extended_to_transportRepair
    (reTheoryStageWitness T hRE) hp

theorem repairPrfEq_transport
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {e p y y' d : ℕ}
    (he : RepairPrfEq T hRE e y y')
    (hp : RepairPrfEq T hRE p y d) :
    RepairPrfEq T hRE (transport e p y y' d) y' d :=
  proof_T_transport (reTheoryStageWitness T hRE) he hp

/-- Production premises embed unchanged and the constructor then produces a
repair-checker proof.  Only the conclusion changes checker. -/
theorem prfEq_inputs_to_repairTransport
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {e p y y' d : ℕ}
    (he : PrfEq T hRE e y y')
    (hp : PrfEq T hRE p y d) :
    RepairPrfEq T hRE (transport e p y y' d) y' d :=
  repairPrfEq_transport T hRE
    (prfEq_to_repairPrfEq T hRE he)
    (prfEq_to_repairPrfEq T hRE hp)

/-- The exact packed correctness statement obtained by the repair.  This is
not `PrfEqTransportCorrect`, whose premises and conclusion use the unchanged
production checker. -/
theorem transportPacked_correct_repair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ∀ e p y y' d : ℕ,
      RepairPrfEq T hRE e y y' →
        RepairPrfEq T hRE p y d →
          RepairPrfEq T hRE (transportPacked ((((e, p), y), y'), d)) y' d := by
  intro e p y y' d he hp
  exact repairPrfEq_transport T hRE he hp

end FailureOfComposition.PrfEqTransportRepair
