/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProductProofs.Core

/-!
# Numerical transfer along a domain inequality

This module adds one implication scheme to the product proof presentation.  Its
antecedents say that the composite index `compIndex s r` has the same graph as
`r`, and that `r` fixes `i`; its consequent says that `s` fixes `i`.  The
resulting proof transformation consists of a one-line scheme proof followed by
two applications of numerical modus ponens.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.NumericalDomainOrder

open NumericalProofBridge NumericalProductProofs TypedProgramCategory
open UniformIndexQuotient

/-! ## The domain-order implication scheme -/

/-- The formula string

`E(compIndex s r,r) -> (R(r,i,i) -> R(s,i,i))`.

Here `E(q,r)` compares the first-success graph of `q` with the eventual graph
of `r`, while `R(q,n,m)` is a closed eventual-graph instance. -/
def domainOrderAxiomString (s r i : ℕ) : FormulaString :=
  impString (equalityString (compIndex s r) r)
    (impString (rightInstanceString r i i)
      (rightInstanceString s i i))

/-- The numerical code of `domainOrderAxiomString`. -/
def domainOrderAxiomCode (s r i : ℕ) : FormulaCode :=
  encodeFormula (domainOrderAxiomString s r i)

@[simp] theorem domainOrderAxiomCode_eq_imp (s r i : ℕ) :
    domainOrderAxiomCode s r i =
      imp (equalityCode (compIndex s r) r)
        (imp (rightInstanceCode r i i) (rightInstanceCode s i i)) := by
  simp [domainOrderAxiomCode, domainOrderAxiomString, equalityCode,
    rightInstanceCode, imp]

abbrev DomainOrderSchemaArgs := (ℕ × ℕ) × ℕ

theorem primrec_domainOrderAxiomString :
    Primrec (fun z : DomainOrderSchemaArgs =>
      domainOrderAxiomString z.1.1 z.1.2 z.2) := by
  have hs : Primrec (fun z : DomainOrderSchemaArgs => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun z : DomainOrderSchemaArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : DomainOrderSchemaArgs => z.2) := Primrec.snd
  have hc := TypedProgramCategory.primrec₂_compIndex.comp hs hr
  have he := primrec₂_equalityString.comp hc hr
  have hrr := primrec_rightInstanceString.comp ((hr.pair hi).pair hi)
  have hrs := primrec_rightInstanceString.comp ((hs.pair hi).pair hi)
  exact primrec_impString.comp he (primrec_impString.comp hrr hrs)

theorem primrec_domainOrderAxiomCode :
    Primrec (fun z : DomainOrderSchemaArgs =>
      domainOrderAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_domainOrderAxiomString

/-! ## Exact primitive-recursive recognition -/

private def domainOrderTokenAt (j : ℕ) (x : FormulaString) : ℕ :=
  x.getD j 0

private theorem primrec_domainOrderTokenAt (j : ℕ) :
    Primrec (domainOrderTokenAt j) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const j)

private def recoveredOuterProgram (x : FormulaString) : ℕ :=
  domainOrderTokenAt 1 (rhsString (rhsString x))

private def recoveredInnerProgram (x : FormulaString) : ℕ :=
  domainOrderTokenAt 2 (lhsString x)

private def recoveredInput (x : FormulaString) : ℕ :=
  domainOrderTokenAt 2 (lhsString (rhsString x))

private theorem primrec_recoveredOuterProgram :
    Primrec recoveredOuterProgram :=
  primrec_domainOrderTokenAt 1 |>.comp
    (primrec_rhsString.comp primrec_rhsString)

private theorem primrec_recoveredInnerProgram :
    Primrec recoveredInnerProgram :=
  primrec_domainOrderTokenAt 2 |>.comp primrec_lhsString

private theorem primrec_recoveredInput : Primrec recoveredInput :=
  primrec_domainOrderTokenAt 2 |>.comp
    (primrec_lhsString.comp primrec_rhsString)

@[simp] private theorem recoveredOuterProgram_axiomString (s r i : ℕ) :
    recoveredOuterProgram (domainOrderAxiomString s r i) = s := by
  simp [recoveredOuterProgram, domainOrderAxiomString, domainOrderTokenAt,
    rightInstanceString]

@[simp] private theorem recoveredInnerProgram_axiomString (s r i : ℕ) :
    recoveredInnerProgram (domainOrderAxiomString s r i) = r := by
  simp [recoveredInnerProgram, domainOrderAxiomString, domainOrderTokenAt,
    equalityString]

@[simp] private theorem recoveredInput_axiomString (s r i : ℕ) :
    recoveredInput (domainOrderAxiomString s r i) = i := by
  simp [recoveredInput, domainOrderAxiomString, domainOrderTokenAt,
    rightInstanceString]

private def domainOrderAxiomCandidate (x : FormulaString) : FormulaString :=
  domainOrderAxiomString (recoveredOuterProgram x)
    (recoveredInnerProgram x) (recoveredInput x)

private theorem primrec_domainOrderAxiomCandidate :
    Primrec domainOrderAxiomCandidate := by
  exact (primrec_domainOrderAxiomString.comp
    ((primrec_recoveredOuterProgram.pair primrec_recoveredInnerProgram).pair
      primrec_recoveredInput)).of_eq (fun _ => rfl)

/-- Exact shape of the one added scheme.  Reconstruction of the complete
string rejects malformed strings and inconsistent repeated parameters. -/
def DomainOrderAxiomShape (x : FormulaString) : Prop :=
  x = domainOrderAxiomCandidate x

def domainOrderAxiomTest (x : FormulaString) : Bool :=
  x == domainOrderAxiomCandidate x

@[simp] theorem domainOrderAxiomTest_eq_true_iff (x : FormulaString) :
    domainOrderAxiomTest x = true ↔ DomainOrderAxiomShape x := by
  simp [domainOrderAxiomTest, DomainOrderAxiomShape]

theorem domainOrderAxiomShape_iff (x : FormulaString) :
    DomainOrderAxiomShape x ↔
      ∃ s r i, x = domainOrderAxiomString s r i := by
  constructor
  · intro h
    exact ⟨recoveredOuterProgram x, recoveredInnerProgram x,
      recoveredInput x, h⟩
  · rintro ⟨s, r, i, rfl⟩
    simp [DomainOrderAxiomShape, domainOrderAxiomCandidate]

theorem primrec_domainOrderAxiomTest : Primrec domainOrderAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_domainOrderAxiomCandidate).of_eq
    (fun x => by simp [domainOrderAxiomTest])

/-! ## Extension of the product presentation -/

def DomainOrderLogicalAxiomShape (x : FormulaString) : Prop :=
  ProductLogicalAxiomShape x ∨ DomainOrderAxiomShape x

def domainOrderLogicalAxiomTest (x : FormulaString) : Bool :=
  productLogicalAxiomTest x || domainOrderAxiomTest x

@[simp] theorem domainOrderLogicalAxiomTest_eq_true_iff
    (x : FormulaString) :
    domainOrderLogicalAxiomTest x = true ↔
      DomainOrderLogicalAxiomShape x := by
  simp [domainOrderLogicalAxiomTest, DomainOrderLogicalAxiomShape]

theorem primrec_domainOrderLogicalAxiomTest :
    Primrec domainOrderLogicalAxiomTest :=
  Primrec.or.comp primrec_productLogicalAxiomTest
    primrec_domainOrderAxiomTest

/-- The product presentation extended by the domain-order implication scheme.
The theory-axiom test remains unchanged. -/
def domainOrderTheoryPresentation
    (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨domainOrderLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def domainOrderPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := domainOrderTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_domainOrderLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem productLogicalAxiom_holds_domainOrder
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (productTheoryPresentation w).syn.logicalAxiom.Holds x) :
    (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change productLogicalAxiomTest x = true at h
  change domainOrderLogicalAxiomTest x = true
  simp [domainOrderLogicalAxiomTest, h]

theorem domainOrderAxiom_holds
    (w : ℕ → ℕ → Bool) (s r i : ℕ) :
    (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds
      (domainOrderAxiomString s r i) := by
  change domainOrderLogicalAxiomTest (domainOrderAxiomString s r i) = true
  rw [domainOrderLogicalAxiomTest_eq_true_iff]
  exact Or.inr ((domainOrderAxiomShape_iff _).mpr ⟨s, r, i, rfl⟩)

/-- Product proofs embed in the new presentation without changing their
numerical codes. -/
theorem proof_T_product_to_domainOrder
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p a) :
    Proof_T (domainOrderTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro j hjlt
  obtain ⟨hline, -, hcase⟩ := hj j hjlt
  refine ⟨hline, by simp [domainOrderTheoryPresentation,
    StringPredicate.Holds], ?_⟩
  rcases hcase with hlog | hax | hmp
  · exact Or.inl (productLogicalAxiom_holds_domainOrder w hlog)
  · exact Or.inr (Or.inl (by
      simpa [productTheoryPresentation, domainOrderTheoryPresentation]
        using hax))
  · exact Or.inr (Or.inr hmp)

/-- Proofs from the original bridge presentation also embed code-preservingly
through the accepted product extension. -/
theorem proof_T_extended_to_domainOrder
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (domainOrderTheoryPresentation w) p a :=
  proof_T_product_to_domainOrder w (proof_T_extended_to_product w hp)

/-! ## The total numerical proof transformation -/

def domainOrderTransfer (e p s r i : ℕ) : ProofSequenceCode :=
  mp (mp (oneLineProofCode (domainOrderAxiomCode s r i)) e) p

theorem proof_T_domainOrderTransfer
    (w : ℕ → ℕ → Bool) {e p s r i : ℕ}
    (he : Proof_T (domainOrderTheoryPresentation w) e
      (equalityCode (compIndex s r) r))
    (hp : Proof_T (domainOrderTheoryPresentation w) p
      (rightInstanceCode r i i)) :
    Proof_T (domainOrderTheoryPresentation w)
      (domainOrderTransfer e p s r i) (rightInstanceCode s i i) := by
  apply proof_T_mp _ hp
  apply proof_T_mp _ he
  rw [← domainOrderAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [domainOrderAxiomCode, decodeFormula_encodeFormula]
  exact domainOrderAxiom_holds w s r i

abbrev DomainOrderTransferArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

def domainOrderTransferPacked
    (z : DomainOrderTransferArgs) : ProofSequenceCode :=
  domainOrderTransfer z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

/-- Uniform primitive recursiveness in the two supplied proof codes, the two
program indices, and the numeral. -/
theorem primrec_domainOrderTransfer :
    Primrec domainOrderTransferPacked := by
  have he : Primrec (fun z : DomainOrderTransferArgs => z.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec (fun z : DomainOrderTransferArgs => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec (fun z : DomainOrderTransferArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun z : DomainOrderTransferArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : DomainOrderTransferArgs => z.2) := Primrec.snd
  have hargs : Primrec (fun z : DomainOrderTransferArgs =>
      ((z.1.1.2, z.1.2), z.2)) := (hs.pair hr).pair hi
  have hcode := primrec_domainOrderAxiomCode.comp hargs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hcode) he) hp).of_eq
      (fun _ => rfl)

end FailureOfComposition.NumericalDomainOrder
