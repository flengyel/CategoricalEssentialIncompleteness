/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.FiniteExtensionChecker
import FailureOfComposition.NumericalDomainOrder.Core

/-!
# Numerical proof conversions for the finite-extension checker

This module extends the domain-order proof presentation by two implication
schemes.  For external `c` and `i`, let `u = Nat.pair c i`.  The endpoints are

* `checkerInstanceCode c i = R(extensionCheckerIndex,u,u)`, and
* `extensionInstanceCode c i = R(zeroTestIndex,u,0)`.

The second endpoint is still a tagged eventual-graph instance.  Its arithmetic
meaning is PA-equivalent to the independently defined formula
`extensionFormula`; it is not definitionally a native syntax code for that
formula.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionProofs

open FiniteExtensionChecker NumericalDomainOrder NumericalProofBridge
open NumericalProductProofs

noncomputable section

/-! ## Exact graph-tag endpoints -/

/-- The checker fixed-point tag `C(c,i)`. -/
def checkerInstanceString (c i : ℕ) : FormulaString :=
  let u := Nat.pair c i
  rightInstanceString extensionCheckerIndex u u

/-- The zero-test tag `X(c,i)`.  This is a graph tag, not a native code of
`extensionFormula`. -/
def extensionInstanceString (c i : ℕ) : FormulaString :=
  rightInstanceString zeroTestIndex (Nat.pair c i) 0

def checkerInstanceCode (c i : ℕ) : FormulaCode :=
  encodeFormula (checkerInstanceString c i)

def extensionInstanceCode (c i : ℕ) : FormulaCode :=
  encodeFormula (extensionInstanceString c i)

@[simp] theorem checkerInstanceCode_eq_right (c i : ℕ) :
    checkerInstanceCode c i =
      rightInstanceCode extensionCheckerIndex (Nat.pair c i)
        (Nat.pair c i) := by
  simp [checkerInstanceCode, checkerInstanceString, rightInstanceCode]

@[simp] theorem extensionInstanceCode_eq_right (c i : ℕ) :
    extensionInstanceCode c i =
      rightInstanceCode zeroTestIndex (Nat.pair c i) 0 := by
  simp [extensionInstanceCode, extensionInstanceString, rightInstanceCode]

theorem primrec_checkerInstanceString :
    Primrec (fun z : ℕ × ℕ => checkerInstanceString z.1 z.2) := by
  have hu : Primrec (fun z : ℕ × ℕ => Nat.pair z.1 z.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  exact primrec_rightInstanceString.comp
    (((Primrec.const extensionCheckerIndex).pair hu).pair hu)

theorem primrec_extensionInstanceString :
    Primrec (fun z : ℕ × ℕ => extensionInstanceString z.1 z.2) := by
  have hu : Primrec (fun z : ℕ × ℕ => Nat.pair z.1 z.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  exact primrec_rightInstanceString.comp
    (((Primrec.const zeroTestIndex).pair hu).pair (Primrec.const 0))

theorem primrec_checkerInstanceCode :
    Primrec (fun z : ℕ × ℕ => checkerInstanceCode z.1 z.2) :=
  primrec_encodeFormula.comp primrec_checkerInstanceString

theorem primrec_extensionInstanceCode :
    Primrec (fun z : ℕ × ℕ => extensionInstanceCode z.1 z.2) :=
  primrec_encodeFormula.comp primrec_extensionInstanceString

/-! ## The two implication schemes -/

def checkerToExtensionAxiomString (c i : ℕ) : FormulaString :=
  impString (checkerInstanceString c i) (extensionInstanceString c i)

def extensionToCheckerAxiomString (c i : ℕ) : FormulaString :=
  impString (extensionInstanceString c i) (checkerInstanceString c i)

def checkerToExtensionAxiomCode (c i : ℕ) : FormulaCode :=
  encodeFormula (checkerToExtensionAxiomString c i)

def extensionToCheckerAxiomCode (c i : ℕ) : FormulaCode :=
  encodeFormula (extensionToCheckerAxiomString c i)

@[simp] theorem checkerToExtensionAxiomCode_eq_imp (c i : ℕ) :
    checkerToExtensionAxiomCode c i =
      imp (checkerInstanceCode c i) (extensionInstanceCode c i) := by
  simp [checkerToExtensionAxiomCode, checkerToExtensionAxiomString,
    checkerInstanceCode, extensionInstanceCode, imp]

@[simp] theorem extensionToCheckerAxiomCode_eq_imp (c i : ℕ) :
    extensionToCheckerAxiomCode c i =
      imp (extensionInstanceCode c i) (checkerInstanceCode c i) := by
  simp [extensionToCheckerAxiomCode, extensionToCheckerAxiomString,
    checkerInstanceCode, extensionInstanceCode, imp]

theorem primrec_checkerToExtensionAxiomString :
    Primrec (fun z : ℕ × ℕ =>
      checkerToExtensionAxiomString z.1 z.2) :=
  primrec_impString.comp primrec_checkerInstanceString
    primrec_extensionInstanceString

theorem primrec_extensionToCheckerAxiomString :
    Primrec (fun z : ℕ × ℕ =>
      extensionToCheckerAxiomString z.1 z.2) :=
  primrec_impString.comp primrec_extensionInstanceString
    primrec_checkerInstanceString

theorem primrec_checkerToExtensionAxiomCode :
    Primrec (fun z : ℕ × ℕ =>
      checkerToExtensionAxiomCode z.1 z.2) :=
  primrec_encodeFormula.comp primrec_checkerToExtensionAxiomString

theorem primrec_extensionToCheckerAxiomCode :
    Primrec (fun z : ℕ × ℕ =>
      extensionToCheckerAxiomCode z.1 z.2) :=
  primrec_encodeFormula.comp primrec_extensionToCheckerAxiomString

/-! ## Exact primitive-recursive recognition -/

private def extensionTokenAt (j : ℕ) (x : FormulaString) : ℕ :=
  x.getD j 0

private theorem primrec_extensionTokenAt (j : ℕ) :
    Primrec (extensionTokenAt j) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const j)

private def recoveredPairCode (x : FormulaString) : ℕ :=
  extensionTokenAt 2 (lhsString x)

private def recoveredFiniteCode (x : FormulaString) : ℕ :=
  (recoveredPairCode x).unpair.1

private def recoveredProgramIndex (x : FormulaString) : ℕ :=
  (recoveredPairCode x).unpair.2

private theorem primrec_recoveredPairCode : Primrec recoveredPairCode :=
  primrec_extensionTokenAt 2 |>.comp primrec_lhsString

private theorem primrec_recoveredFiniteCode :
    Primrec recoveredFiniteCode :=
  (Primrec.fst.comp (Primrec.unpair.comp primrec_recoveredPairCode)).of_eq
    (fun _ => rfl)

private theorem primrec_recoveredProgramIndex :
    Primrec recoveredProgramIndex :=
  (Primrec.snd.comp (Primrec.unpair.comp primrec_recoveredPairCode)).of_eq
    (fun _ => rfl)

@[simp] private theorem recoveredFiniteCode_checkerToExtension
    (c i : ℕ) :
    recoveredFiniteCode (checkerToExtensionAxiomString c i) = c := by
  simp [recoveredFiniteCode, recoveredPairCode, checkerToExtensionAxiomString,
    checkerInstanceString, rightInstanceString, extensionTokenAt]

@[simp] private theorem recoveredProgramIndex_checkerToExtension
    (c i : ℕ) :
    recoveredProgramIndex (checkerToExtensionAxiomString c i) = i := by
  simp [recoveredProgramIndex, recoveredPairCode,
    checkerToExtensionAxiomString, checkerInstanceString,
    rightInstanceString, extensionTokenAt]

@[simp] private theorem recoveredFiniteCode_extensionToChecker
    (c i : ℕ) :
    recoveredFiniteCode (extensionToCheckerAxiomString c i) = c := by
  simp [recoveredFiniteCode, recoveredPairCode, extensionToCheckerAxiomString,
    extensionInstanceString, rightInstanceString, extensionTokenAt]

@[simp] private theorem recoveredProgramIndex_extensionToChecker
    (c i : ℕ) :
    recoveredProgramIndex (extensionToCheckerAxiomString c i) = i := by
  simp [recoveredProgramIndex, recoveredPairCode,
    extensionToCheckerAxiomString, extensionInstanceString,
    rightInstanceString, extensionTokenAt]

private def checkerToExtensionCandidate
    (x : FormulaString) : FormulaString :=
  checkerToExtensionAxiomString (recoveredFiniteCode x)
    (recoveredProgramIndex x)

private def extensionToCheckerCandidate
    (x : FormulaString) : FormulaString :=
  extensionToCheckerAxiomString (recoveredFiniteCode x)
    (recoveredProgramIndex x)

private theorem primrec_checkerToExtensionCandidate :
    Primrec checkerToExtensionCandidate :=
  primrec_checkerToExtensionAxiomString.comp
    (primrec_recoveredFiniteCode.pair primrec_recoveredProgramIndex)

private theorem primrec_extensionToCheckerCandidate :
    Primrec extensionToCheckerCandidate :=
  primrec_extensionToCheckerAxiomString.comp
    (primrec_recoveredFiniteCode.pair primrec_recoveredProgramIndex)

/-- Exact shape of the two added schemes.  Reconstructing the complete string
checks the fixed program indices and every repeated occurrence of `c` and
`i`. -/
def ExtensionAxiomShape (x : FormulaString) : Prop :=
  x = checkerToExtensionCandidate x ∨
    x = extensionToCheckerCandidate x

def extensionAxiomTest (x : FormulaString) : Bool :=
  (x == checkerToExtensionCandidate x) ||
    (x == extensionToCheckerCandidate x)

@[simp] theorem extensionAxiomTest_eq_true_iff (x : FormulaString) :
    extensionAxiomTest x = true ↔ ExtensionAxiomShape x := by
  simp [extensionAxiomTest, ExtensionAxiomShape]

theorem extensionAxiomShape_iff (x : FormulaString) :
    ExtensionAxiomShape x ↔
      (∃ c i, x = checkerToExtensionAxiomString c i) ∨
      (∃ c i, x = extensionToCheckerAxiomString c i) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨recoveredFiniteCode x, recoveredProgramIndex x, h⟩
    · exact Or.inr ⟨recoveredFiniteCode x, recoveredProgramIndex x, h⟩
  · rintro (⟨c, i, rfl⟩ | ⟨c, i, rfl⟩)
    · exact Or.inl (by simp [checkerToExtensionCandidate])
    · exact Or.inr (by simp [extensionToCheckerCandidate])

theorem primrec_extensionAxiomTest : Primrec extensionAxiomTest := by
  have hchecker : Primrec (fun x : FormulaString =>
      x == checkerToExtensionCandidate x) :=
    (Primrec.beq.comp Primrec.id
      primrec_checkerToExtensionCandidate).of_eq (fun x => by simp)
  have hextension : Primrec (fun x : FormulaString =>
      x == extensionToCheckerCandidate x) :=
    (Primrec.beq.comp Primrec.id
      primrec_extensionToCheckerCandidate).of_eq (fun x => by simp)
  exact (Primrec.or.comp hchecker hextension).of_eq
    (fun _ => rfl)

/-! ## The finite-extension proof presentation -/

def FiniteExtensionLogicalAxiomShape (x : FormulaString) : Prop :=
  DomainOrderLogicalAxiomShape x ∨ ExtensionAxiomShape x

def finiteExtensionLogicalAxiomTest (x : FormulaString) : Bool :=
  domainOrderLogicalAxiomTest x || extensionAxiomTest x

@[simp] theorem finiteExtensionLogicalAxiomTest_eq_true_iff
    (x : FormulaString) :
    finiteExtensionLogicalAxiomTest x = true ↔
      FiniteExtensionLogicalAxiomShape x := by
  simp [finiteExtensionLogicalAxiomTest, FiniteExtensionLogicalAxiomShape]

theorem primrec_finiteExtensionLogicalAxiomTest :
    Primrec finiteExtensionLogicalAxiomTest :=
  Primrec.or.comp primrec_domainOrderLogicalAxiomTest
    primrec_extensionAxiomTest

/-- The distinctly named proof presentation used by both conversions. -/
def finiteExtensionTheoryPresentation
    (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨finiteExtensionLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def finiteExtensionPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := finiteExtensionTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_finiteExtensionLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem domainOrderLogicalAxiom_holds_finiteExtension
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds x) :
    (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change domainOrderLogicalAxiomTest x = true at h
  change finiteExtensionLogicalAxiomTest x = true
  simp [finiteExtensionLogicalAxiomTest, h]

theorem checkerToExtensionAxiom_holds
    (w : ℕ → ℕ → Bool) (c i : ℕ) :
    (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds
      (checkerToExtensionAxiomString c i) := by
  change finiteExtensionLogicalAxiomTest
    (checkerToExtensionAxiomString c i) = true
  rw [finiteExtensionLogicalAxiomTest_eq_true_iff]
  exact Or.inr ((extensionAxiomShape_iff _).mpr
    (Or.inl ⟨c, i, rfl⟩))

theorem extensionToCheckerAxiom_holds
    (w : ℕ → ℕ → Bool) (c i : ℕ) :
    (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds
      (extensionToCheckerAxiomString c i) := by
  change finiteExtensionLogicalAxiomTest
    (extensionToCheckerAxiomString c i) = true
  rw [finiteExtensionLogicalAxiomTest_eq_true_iff]
  exact Or.inr ((extensionAxiomShape_iff _).mpr
    (Or.inr ⟨c, i, rfl⟩))

/-- Domain-order proofs embed without changing their proof-sequence codes. -/
theorem proof_T_domainOrder_to_finiteExtension
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (domainOrderTheoryPresentation w) p a) :
    Proof_T (finiteExtensionTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro j hjlt
  obtain ⟨hline, -, hcase⟩ := hj j hjlt
  refine ⟨hline, by simp [finiteExtensionTheoryPresentation,
    StringPredicate.Holds], ?_⟩
  rcases hcase with hlog | hax | hmp
  · exact Or.inl (domainOrderLogicalAxiom_holds_finiteExtension w hlog)
  · exact Or.inr (Or.inl (by
      simpa [domainOrderTheoryPresentation,
        finiteExtensionTheoryPresentation] using hax))
  · exact Or.inr (Or.inr hmp)

/-- Product-presentation proofs embed code-preservingly through the accepted
domain-order extension. -/
theorem proof_T_product_to_finiteExtension
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p a) :
    Proof_T (finiteExtensionTheoryPresentation w) p a :=
  proof_T_domainOrder_to_finiteExtension w
    (proof_T_product_to_domainOrder w hp)

/-- Proofs from the original graph-tag bridge presentation also embed with
the same numerical code. -/
theorem proof_T_extended_to_finiteExtension
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (finiteExtensionTheoryPresentation w) p a :=
  proof_T_domainOrder_to_finiteExtension w
    (proof_T_extended_to_domainOrder w hp)

/-! ## The two total proof transformations -/

def checkerToExt (p c i : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (checkerToExtensionAxiomCode c i)) p

def extToChecker (p c i : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (extensionToCheckerAxiomCode c i)) p

theorem proof_T_checkerToExt
    (w : ℕ → ℕ → Bool) {p c i : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p
      (checkerInstanceCode c i)) :
    Proof_T (finiteExtensionTheoryPresentation w) (checkerToExt p c i)
      (extensionInstanceCode c i) := by
  apply proof_T_mp _ hp
  rw [← checkerToExtensionAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [checkerToExtensionAxiomCode, decodeFormula_encodeFormula]
  exact checkerToExtensionAxiom_holds w c i

theorem proof_T_extToChecker
    (w : ℕ → ℕ → Bool) {p c i : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p
      (extensionInstanceCode c i)) :
    Proof_T (finiteExtensionTheoryPresentation w) (extToChecker p c i)
      (checkerInstanceCode c i) := by
  apply proof_T_mp _ hp
  rw [← extensionToCheckerAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [extensionToCheckerAxiomCode, decodeFormula_encodeFormula]
  exact extensionToCheckerAxiom_holds w c i

abbrev ExtensionTransferArgs := (ℕ × ℕ) × ℕ

def checkerToExtPacked (z : ExtensionTransferArgs) : ProofSequenceCode :=
  checkerToExt z.1.1 z.1.2 z.2

def extToCheckerPacked (z : ExtensionTransferArgs) : ProofSequenceCode :=
  extToChecker z.1.1 z.1.2 z.2

theorem primrec_checkerToExt : Primrec checkerToExtPacked := by
  have hp : Primrec (fun z : ExtensionTransferArgs => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun z : ExtensionTransferArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ExtensionTransferArgs => z.2) := Primrec.snd
  have hcode := primrec_checkerToExtensionAxiomCode.comp (hc.pair hi)
  exact (primrec_mp.comp
    (primrec_oneLineProofCode.comp hcode) hp).of_eq (fun _ => rfl)

theorem primrec_extToChecker : Primrec extToCheckerPacked := by
  have hp : Primrec (fun z : ExtensionTransferArgs => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun z : ExtensionTransferArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ExtensionTransferArgs => z.2) := Primrec.snd
  have hcode := primrec_extensionToCheckerAxiomCode.comp (hc.pair hi)
  exact (primrec_mp.comp
    (primrec_oneLineProofCode.comp hcode) hp).of_eq (fun _ => rfl)

end


end FailureOfComposition.NumericalExtensionProofs
