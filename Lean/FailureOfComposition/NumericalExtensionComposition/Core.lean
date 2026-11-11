/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionProofs.Core

/-!
# Numerical composition of the B1(7) proof transformations

This module fixes the two implication schemes missing from the accepted
product and finite-extension presentations.  External natural numbers denote
program indices and closed numerals throughout.  The first scheme turns mixed
first-success/eventual equality and a value proof into a domain tag.  The
second scheme turns the two component values and the checker fixed-point
equation into the finite-extension checker tag.

The presentation defined below extends `finiteExtensionTheoryPresentation`
without changing any previously accepted proof code.  The four advertised
maps use only the two new schemes, numerical modus ponens, and the existing
`project1ToPair`, `pairToLeft`, and `checkerToExt` transformations.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionComposition

open FiniteExtensionChecker NumericalDomainOrder NumericalExtensionProofs
open NumericalProofBridge NumericalProductProofs TypedNearProduct
open TypedProgramCategory UniformIndexQuotient

noncomputable section

/-! ## The two missing implication schemes -/

/-- The formula string

`E(a,b) -> (R(b,t,i) -> D(a,t))`.

The first endpoint is a mixed first-success/eventual equality, and the last
endpoint is the accepted domain-graph tag for existential definedness. -/
def projectionDefinednessAxiomString
    (a b t i : ℕ) : FormulaString :=
  impString (equalityString a b)
    (impString (rightInstanceString b t i) (definednessString a t))

/-- The formula string

`E(compIndex k (pairIndex q r), pairIndex q r) ->
  (R(q,t,c) -> (R(r,t,i) -> C(c,i)))`,

where `k` is the fixed finite-extension checker index. -/
def componentValuesToCheckerAxiomString
    (q r t c i : ℕ) : FormulaString :=
  let p := pairIndex q r
  impString (equalityString (compIndex extensionCheckerIndex p) p)
    (impString (rightInstanceString q t c)
      (impString (rightInstanceString r t i)
        (checkerInstanceString c i)))

def projectionDefinednessAxiomCode (a b t i : ℕ) : FormulaCode :=
  encodeFormula (projectionDefinednessAxiomString a b t i)

def componentValuesToCheckerAxiomCode
    (q r t c i : ℕ) : FormulaCode :=
  encodeFormula (componentValuesToCheckerAxiomString q r t c i)

@[simp] theorem projectionDefinednessAxiomCode_eq_imp
    (a b t i : ℕ) :
    projectionDefinednessAxiomCode a b t i =
      imp (equalityCode a b)
        (imp (rightInstanceCode b t i) (definednessTag a t)) := by
  simp [projectionDefinednessAxiomCode, projectionDefinednessAxiomString,
    equalityCode, rightInstanceCode, definednessTag_eq_encode, imp]

@[simp] theorem componentValuesToCheckerAxiomCode_eq_imp
    (q r t c i : ℕ) :
    componentValuesToCheckerAxiomCode q r t c i =
      imp (equalityCode
          (compIndex extensionCheckerIndex (pairIndex q r))
          (pairIndex q r))
        (imp (rightInstanceCode q t c)
          (imp (rightInstanceCode r t i) (checkerInstanceCode c i))) := by
  simp [componentValuesToCheckerAxiomCode,
    componentValuesToCheckerAxiomString, equalityCode, rightInstanceCode,
    checkerInstanceCode, imp]

abbrev ProjectionDefinednessSchemaArgs := (((ℕ × ℕ) × ℕ) × ℕ)
abbrev ComponentCheckerSchemaArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

theorem primrec_projectionDefinednessAxiomString :
    Primrec (fun z : ProjectionDefinednessSchemaArgs =>
      projectionDefinednessAxiomString z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have ha : Primrec (fun z : ProjectionDefinednessSchemaArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec (fun z : ProjectionDefinednessSchemaArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun z : ProjectionDefinednessSchemaArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ProjectionDefinednessSchemaArgs => z.2) :=
    Primrec.snd
  have he := primrec₂_equalityString.comp ha hb
  have hr := primrec_rightInstanceString.comp ((hb.pair ht).pair hi)
  have hd := primrec₂_definednessString.comp ha ht
  exact primrec_impString.comp he (primrec_impString.comp hr hd)

theorem primrec_componentValuesToCheckerAxiomString :
    Primrec (fun z : ComponentCheckerSchemaArgs =>
      componentValuesToCheckerAxiomString
        z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
  have hq : Primrec (fun z : ComponentCheckerSchemaArgs => z.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hr : Primrec (fun z : ComponentCheckerSchemaArgs => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have ht : Primrec (fun z : ComponentCheckerSchemaArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun z : ComponentCheckerSchemaArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ComponentCheckerSchemaArgs => z.2) :=
    Primrec.snd
  have hp := primrec₂_pairIndex.comp hq hr
  have hcomp := TypedProgramCategory.primrec₂_compIndex.comp
    (Primrec.const extensionCheckerIndex) hp
  have he := primrec₂_equalityString.comp hcomp hp
  have hqv := primrec_rightInstanceString.comp ((hq.pair ht).pair hc)
  have hrv := primrec_rightInstanceString.comp ((hr.pair ht).pair hi)
  have hcheck := primrec_checkerInstanceString.comp (hc.pair hi)
  exact primrec_impString.comp he
    (primrec_impString.comp hqv (primrec_impString.comp hrv hcheck))

theorem primrec_projectionDefinednessAxiomCode :
    Primrec (fun z : ProjectionDefinednessSchemaArgs =>
      projectionDefinednessAxiomCode z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_projectionDefinednessAxiomString

theorem primrec_componentValuesToCheckerAxiomCode :
    Primrec (fun z : ComponentCheckerSchemaArgs =>
      componentValuesToCheckerAxiomCode
        z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_componentValuesToCheckerAxiomString

/-! ## Exact primitive-recursive recognition -/

def compositionTokenAt (j : ℕ) (x : FormulaString) : ℕ :=
  x.getD j 0

private theorem primrec_compositionTokenAt (j : ℕ) :
    Primrec (compositionTokenAt j) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const j)

def recoveredProjectionOuter (x : FormulaString) : ℕ :=
  compositionTokenAt 1 (lhsString x)

def recoveredProjectionInner (x : FormulaString) : ℕ :=
  compositionTokenAt 2 (lhsString x)

def recoveredProjectionInput (x : FormulaString) : ℕ :=
  compositionTokenAt 2 (lhsString (rhsString x))

def recoveredProjectionValue (x : FormulaString) : ℕ :=
  compositionTokenAt 3 (lhsString (rhsString x))

private theorem primrec_recoveredProjectionOuter :
    Primrec recoveredProjectionOuter :=
  (primrec_compositionTokenAt 1).comp primrec_lhsString

private theorem primrec_recoveredProjectionInner :
    Primrec recoveredProjectionInner :=
  (primrec_compositionTokenAt 2).comp primrec_lhsString

private theorem primrec_recoveredProjectionInput :
    Primrec recoveredProjectionInput :=
  (primrec_compositionTokenAt 2).comp
    (primrec_lhsString.comp primrec_rhsString)

private theorem primrec_recoveredProjectionValue :
    Primrec recoveredProjectionValue :=
  (primrec_compositionTokenAt 3).comp
    (primrec_lhsString.comp primrec_rhsString)

@[simp] private theorem recoveredProjectionOuter_axiomString
    (a b t i : ℕ) :
    recoveredProjectionOuter (projectionDefinednessAxiomString a b t i) =
      a := by
  simp [recoveredProjectionOuter, projectionDefinednessAxiomString,
    compositionTokenAt, equalityString]

@[simp] private theorem recoveredProjectionInner_axiomString
    (a b t i : ℕ) :
    recoveredProjectionInner (projectionDefinednessAxiomString a b t i) =
      b := by
  simp [recoveredProjectionInner, projectionDefinednessAxiomString,
    compositionTokenAt, equalityString]

@[simp] private theorem recoveredProjectionInput_axiomString
    (a b t i : ℕ) :
    recoveredProjectionInput (projectionDefinednessAxiomString a b t i) =
      t := by
  simp [recoveredProjectionInput, projectionDefinednessAxiomString,
    compositionTokenAt, rightInstanceString]

@[simp] private theorem recoveredProjectionValue_axiomString
    (a b t i : ℕ) :
    recoveredProjectionValue (projectionDefinednessAxiomString a b t i) =
      i := by
  simp [recoveredProjectionValue, projectionDefinednessAxiomString,
    compositionTokenAt, rightInstanceString]

def projectionDefinednessAxiomCandidate
    (x : FormulaString) : FormulaString :=
  projectionDefinednessAxiomString (recoveredProjectionOuter x)
    (recoveredProjectionInner x) (recoveredProjectionInput x)
    (recoveredProjectionValue x)

private theorem primrec_projectionDefinednessAxiomCandidate :
    Primrec projectionDefinednessAxiomCandidate := by
  exact (primrec_projectionDefinednessAxiomString.comp
    (((primrec_recoveredProjectionOuter.pair
      primrec_recoveredProjectionInner).pair
      primrec_recoveredProjectionInput).pair
      primrec_recoveredProjectionValue)).of_eq (fun _ => rfl)

def recoveredComponentLeft (x : FormulaString) : ℕ :=
  compositionTokenAt 1 (lhsString (rhsString x))

def recoveredComponentRight (x : FormulaString) : ℕ :=
  compositionTokenAt 1 (lhsString (rhsString (rhsString x)))

def recoveredComponentInput (x : FormulaString) : ℕ :=
  compositionTokenAt 2 (lhsString (rhsString x))

def recoveredComponentLeftValue (x : FormulaString) : ℕ :=
  compositionTokenAt 3 (lhsString (rhsString x))

def recoveredComponentRightValue (x : FormulaString) : ℕ :=
  compositionTokenAt 3 (lhsString (rhsString (rhsString x)))

private theorem primrec_recoveredComponentLeft :
    Primrec recoveredComponentLeft :=
  (primrec_compositionTokenAt 1).comp
    (primrec_lhsString.comp primrec_rhsString)

private theorem primrec_recoveredComponentRight :
    Primrec recoveredComponentRight :=
  (primrec_compositionTokenAt 1).comp
    (primrec_lhsString.comp (primrec_rhsString.comp primrec_rhsString))

private theorem primrec_recoveredComponentInput :
    Primrec recoveredComponentInput :=
  (primrec_compositionTokenAt 2).comp
    (primrec_lhsString.comp primrec_rhsString)

private theorem primrec_recoveredComponentLeftValue :
    Primrec recoveredComponentLeftValue :=
  (primrec_compositionTokenAt 3).comp
    (primrec_lhsString.comp primrec_rhsString)

private theorem primrec_recoveredComponentRightValue :
    Primrec recoveredComponentRightValue :=
  (primrec_compositionTokenAt 3).comp
    (primrec_lhsString.comp (primrec_rhsString.comp primrec_rhsString))

@[simp] private theorem recoveredComponentLeft_axiomString
    (q r t c i : ℕ) :
    recoveredComponentLeft
      (componentValuesToCheckerAxiomString q r t c i) = q := by
  simp [recoveredComponentLeft, componentValuesToCheckerAxiomString,
    compositionTokenAt, rightInstanceString]

@[simp] private theorem recoveredComponentRight_axiomString
    (q r t c i : ℕ) :
    recoveredComponentRight
      (componentValuesToCheckerAxiomString q r t c i) = r := by
  simp [recoveredComponentRight, componentValuesToCheckerAxiomString,
    compositionTokenAt, rightInstanceString]

@[simp] private theorem recoveredComponentInput_axiomString
    (q r t c i : ℕ) :
    recoveredComponentInput
      (componentValuesToCheckerAxiomString q r t c i) = t := by
  simp [recoveredComponentInput, componentValuesToCheckerAxiomString,
    compositionTokenAt, rightInstanceString]

@[simp] private theorem recoveredComponentLeftValue_axiomString
    (q r t c i : ℕ) :
    recoveredComponentLeftValue
      (componentValuesToCheckerAxiomString q r t c i) = c := by
  simp [recoveredComponentLeftValue, componentValuesToCheckerAxiomString,
    compositionTokenAt, rightInstanceString]

@[simp] private theorem recoveredComponentRightValue_axiomString
    (q r t c i : ℕ) :
    recoveredComponentRightValue
      (componentValuesToCheckerAxiomString q r t c i) = i := by
  simp [recoveredComponentRightValue, componentValuesToCheckerAxiomString,
    compositionTokenAt, rightInstanceString]

def componentValuesToCheckerAxiomCandidate
    (x : FormulaString) : FormulaString :=
  componentValuesToCheckerAxiomString (recoveredComponentLeft x)
    (recoveredComponentRight x) (recoveredComponentInput x)
    (recoveredComponentLeftValue x) (recoveredComponentRightValue x)

private theorem primrec_componentValuesToCheckerAxiomCandidate :
    Primrec componentValuesToCheckerAxiomCandidate := by
  exact (primrec_componentValuesToCheckerAxiomString.comp
    ((((primrec_recoveredComponentLeft.pair
      primrec_recoveredComponentRight).pair
      primrec_recoveredComponentInput).pair
      primrec_recoveredComponentLeftValue).pair
      primrec_recoveredComponentRightValue)).of_eq (fun _ => rfl)

/-- Exact shape of the two added schemes.  Complete reconstruction checks
fixed indices and every repeated parameter, so malformed strings are not
accepted merely because they have a suggestive prefix. -/
def ExtensionCompositionAxiomShape (x : FormulaString) : Prop :=
  x = projectionDefinednessAxiomCandidate x ∨
    x = componentValuesToCheckerAxiomCandidate x

def extensionCompositionAxiomTest (x : FormulaString) : Bool :=
  (x == projectionDefinednessAxiomCandidate x) ||
    (x == componentValuesToCheckerAxiomCandidate x)

@[simp] theorem extensionCompositionAxiomTest_eq_true_iff
    (x : FormulaString) :
    extensionCompositionAxiomTest x = true ↔
      ExtensionCompositionAxiomShape x := by
  simp [extensionCompositionAxiomTest, ExtensionCompositionAxiomShape]

theorem extensionCompositionAxiomShape_iff (x : FormulaString) :
    ExtensionCompositionAxiomShape x ↔
      (∃ a b t i, x = projectionDefinednessAxiomString a b t i) ∨
      (∃ q r t c i,
        x = componentValuesToCheckerAxiomString q r t c i) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨recoveredProjectionOuter x,
        recoveredProjectionInner x, recoveredProjectionInput x,
        recoveredProjectionValue x, h⟩
    · exact Or.inr ⟨recoveredComponentLeft x, recoveredComponentRight x,
        recoveredComponentInput x, recoveredComponentLeftValue x,
        recoveredComponentRightValue x, h⟩
  · rintro (⟨a, b, t, i, rfl⟩ | ⟨q, r, t, c, i, rfl⟩)
    · exact Or.inl (by simp [projectionDefinednessAxiomCandidate])
    · exact Or.inr (by simp [componentValuesToCheckerAxiomCandidate])

theorem primrec_extensionCompositionAxiomTest :
    Primrec extensionCompositionAxiomTest := by
  have hprojection : Primrec (fun x : FormulaString =>
      x == projectionDefinednessAxiomCandidate x) :=
    (Primrec.beq.comp Primrec.id
      primrec_projectionDefinednessAxiomCandidate).of_eq
      (fun x => by simp)
  have hcomponent : Primrec (fun x : FormulaString =>
      x == componentValuesToCheckerAxiomCandidate x) :=
    (Primrec.beq.comp Primrec.id
      primrec_componentValuesToCheckerAxiomCandidate).of_eq
      (fun x => by simp)
  exact (Primrec.or.comp hprojection hcomponent).of_eq (fun _ => rfl)

/-! ## Extension of the finite-extension presentation -/

def ExtensionCompositionLogicalAxiomShape (x : FormulaString) : Prop :=
  FiniteExtensionLogicalAxiomShape x ∨ ExtensionCompositionAxiomShape x

def extensionCompositionLogicalAxiomTest (x : FormulaString) : Bool :=
  finiteExtensionLogicalAxiomTest x || extensionCompositionAxiomTest x

@[simp] theorem extensionCompositionLogicalAxiomTest_eq_true_iff
    (x : FormulaString) :
    extensionCompositionLogicalAxiomTest x = true ↔
      ExtensionCompositionLogicalAxiomShape x := by
  simp [extensionCompositionLogicalAxiomTest,
    ExtensionCompositionLogicalAxiomShape]

theorem primrec_extensionCompositionLogicalAxiomTest :
    Primrec extensionCompositionLogicalAxiomTest :=
  Primrec.or.comp primrec_finiteExtensionLogicalAxiomTest
    primrec_extensionCompositionAxiomTest

/-- The common proof presentation used by every transformation in this
checkpoint. -/
def extensionCompositionTheoryPresentation
    (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨extensionCompositionLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def extensionCompositionPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := extensionCompositionTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_extensionCompositionLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem finiteExtensionLogicalAxiom_holds_extensionComposition
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds x) :
    (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change finiteExtensionLogicalAxiomTest x = true at h
  change extensionCompositionLogicalAxiomTest x = true
  simp [extensionCompositionLogicalAxiomTest, h]

private theorem extensionCompositionAxiomShape_holds
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : ExtensionCompositionAxiomShape x) :
    (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change extensionCompositionLogicalAxiomTest x = true
  rw [extensionCompositionLogicalAxiomTest_eq_true_iff]
  exact Or.inr h

theorem projectionDefinednessAxiom_holds
    (w : ℕ → ℕ → Bool) (a b t i : ℕ) :
    (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
      (projectionDefinednessAxiomString a b t i) := by
  apply extensionCompositionAxiomShape_holds
  rw [extensionCompositionAxiomShape_iff]
  exact Or.inl ⟨a, b, t, i, rfl⟩

theorem componentValuesToCheckerAxiom_holds
    (w : ℕ → ℕ → Bool) (q r t c i : ℕ) :
    (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
      (componentValuesToCheckerAxiomString q r t c i) := by
  apply extensionCompositionAxiomShape_holds
  rw [extensionCompositionAxiomShape_iff]
  exact Or.inr ⟨q, r, t, c, i, rfl⟩

/-- Finite-extension proofs embed without changing their numerical proof
sequence codes. -/
theorem proof_T_finiteExtension_to_extensionComposition
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p a) :
    Proof_T (extensionCompositionTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro j hjlt
  obtain ⟨hline, -, hcase⟩ := hj j hjlt
  refine ⟨hline, by simp [extensionCompositionTheoryPresentation,
    StringPredicate.Holds], ?_⟩
  rcases hcase with hlog | hax | hmp
  · exact Or.inl (finiteExtensionLogicalAxiom_holds_extensionComposition
      w hlog)
  · exact Or.inr (Or.inl (by
      simpa [finiteExtensionTheoryPresentation,
        extensionCompositionTheoryPresentation] using hax))
  · exact Or.inr (Or.inr hmp)

theorem proof_T_product_to_extensionComposition
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p a) :
    Proof_T (extensionCompositionTheoryPresentation w) p a :=
  proof_T_finiteExtension_to_extensionComposition w
    (proof_T_product_to_finiteExtension w hp)

theorem proof_T_extended_to_extensionComposition
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (extensionCompositionTheoryPresentation w) p a :=
  proof_T_finiteExtension_to_extensionComposition w
    (proof_T_extended_to_finiteExtension w hp)

/-! ## Total numerical proof transformations -/

/-- Two MP steps for the first new scheme. -/
def equalityValueToDefinedness
    (u p a b t i : ℕ) : ProofSequenceCode :=
  mp (mp (oneLineProofCode
    (projectionDefinednessAxiomCode a b t i)) u) p

/-- From `E(J,r)` and `R(r,t,i)`, first obtain `D(J,t)` and then use the
accepted projection rule to obtain `D(P,t)`. -/
def projectionEqualityToPair
    (u p q r t i : ℕ) : ProofSequenceCode :=
  project1ToPair
    (equalityValueToDefinedness u p (project1PairIndex q r) r t i)
    q r t

/-- Continue the preceding transformation through the accepted left-factor
rule to obtain `D(q,t)`. -/
def projectionEqualityToLeft
    (u p q r t i : ℕ) : ProofSequenceCode :=
  pairToLeft (projectionEqualityToPair u p q r t i) q r t

/-- Three MP steps for the second new scheme. -/
def componentValuesToChecker
    (v a b q r t c i : ℕ) : ProofSequenceCode :=
  mp (mp (mp (oneLineProofCode
    (componentValuesToCheckerAxiomCode q r t c i)) v) a) b

/-- Convert the exact checker endpoint produced above to the accepted
zero-test extension tag. -/
def componentValuesToExt
    (v a b q r t c i : ℕ) : ProofSequenceCode :=
  checkerToExt (componentValuesToChecker v a b q r t c i) c i

theorem proof_T_equalityValueToDefinedness
    (w : ℕ → ℕ → Bool) {u p a b t i : ℕ}
    (hu : Proof_T (extensionCompositionTheoryPresentation w) u
      (equalityCode a b))
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (rightInstanceCode b t i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (equalityValueToDefinedness u p a b t i) (definednessTag a t) := by
  apply proof_T_mp _ hp
  apply proof_T_mp _ hu
  rw [← projectionDefinednessAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [projectionDefinednessAxiomCode, decodeFormula_encodeFormula]
  exact projectionDefinednessAxiom_holds w a b t i

/-- The existing projection map is valid for arbitrary input proofs accepted
by the common checker; no converse checker conversion is used. -/
theorem proof_T_project1ToPair_extensionComposition
    (w : ℕ → ℕ → Bool) {p q r t : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (definednessTag (project1PairIndex q r) t)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (project1ToPair p q r t) (definednessTag (pairIndex q r) t) := by
  apply proof_T_mp _ hp
  rw [← project1ToPairAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [project1ToPairAxiomCode, decodeFormula_encodeFormula]
  apply finiteExtensionLogicalAxiom_holds_extensionComposition
  apply domainOrderLogicalAxiom_holds_finiteExtension
  apply productLogicalAxiom_holds_domainOrder
  exact project1ToPairAxiom_holds w q r t

/-- The existing left-factor map is likewise re-established inside the common
checker. -/
theorem proof_T_pairToLeft_extensionComposition
    (w : ℕ → ℕ → Bool) {p q r t : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (definednessTag (pairIndex q r) t)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (pairToLeft p q r t) (definednessTag q t) := by
  apply proof_T_mp _ hp
  rw [← pairToLeftAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [pairToLeftAxiomCode, decodeFormula_encodeFormula]
  apply finiteExtensionLogicalAxiom_holds_extensionComposition
  apply domainOrderLogicalAxiom_holds_finiteExtension
  apply productLogicalAxiom_holds_domainOrder
  exact pairToLeftAxiom_holds w q r t

/-- The accepted checker-to-extension conversion is re-established for
arbitrary proofs accepted by the common checker. -/
theorem proof_T_checkerToExt_extensionComposition
    (w : ℕ → ℕ → Bool) {p c i : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (checkerInstanceCode c i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (checkerToExt p c i) (extensionInstanceCode c i) := by
  apply proof_T_mp _ hp
  rw [← checkerToExtensionAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [checkerToExtensionAxiomCode, decodeFormula_encodeFormula]
  apply finiteExtensionLogicalAxiom_holds_extensionComposition
  exact checkerToExtensionAxiom_holds w c i

theorem proof_T_projectionEqualityToPair
    (w : ℕ → ℕ → Bool) {u p q r t i : ℕ}
    (hu : Proof_T (extensionCompositionTheoryPresentation w) u
      (equalityCode (project1PairIndex q r) r))
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (rightInstanceCode r t i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (projectionEqualityToPair u p q r t i)
      (definednessTag (pairIndex q r) t) :=
  proof_T_project1ToPair_extensionComposition w
    (proof_T_equalityValueToDefinedness w hu hp)

theorem proof_T_projectionEqualityToLeft
    (w : ℕ → ℕ → Bool) {u p q r t i : ℕ}
    (hu : Proof_T (extensionCompositionTheoryPresentation w) u
      (equalityCode (project1PairIndex q r) r))
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p
      (rightInstanceCode r t i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (projectionEqualityToLeft u p q r t i) (definednessTag q t) :=
  proof_T_pairToLeft_extensionComposition w
    (proof_T_projectionEqualityToPair w hu hp)

theorem proof_T_componentValuesToChecker
    (w : ℕ → ℕ → Bool) {v a b q r t c i : ℕ}
    (hv : Proof_T (extensionCompositionTheoryPresentation w) v
      (equalityCode
        (compIndex extensionCheckerIndex (pairIndex q r))
        (pairIndex q r)))
    (ha : Proof_T (extensionCompositionTheoryPresentation w) a
      (rightInstanceCode q t c))
    (hb : Proof_T (extensionCompositionTheoryPresentation w) b
      (rightInstanceCode r t i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (componentValuesToChecker v a b q r t c i)
      (checkerInstanceCode c i) := by
  apply proof_T_mp _ hb
  apply proof_T_mp _ ha
  apply proof_T_mp _ hv
  rw [← componentValuesToCheckerAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [componentValuesToCheckerAxiomCode, decodeFormula_encodeFormula]
  exact componentValuesToCheckerAxiom_holds w q r t c i

theorem proof_T_componentValuesToExt
    (w : ℕ → ℕ → Bool) {v a b q r t c i : ℕ}
    (hv : Proof_T (extensionCompositionTheoryPresentation w) v
      (equalityCode
        (compIndex extensionCheckerIndex (pairIndex q r))
        (pairIndex q r)))
    (ha : Proof_T (extensionCompositionTheoryPresentation w) a
      (rightInstanceCode q t c))
    (hb : Proof_T (extensionCompositionTheoryPresentation w) b
      (rightInstanceCode r t i)) :
    Proof_T (extensionCompositionTheoryPresentation w)
      (componentValuesToExt v a b q r t c i)
      (extensionInstanceCode c i) :=
  proof_T_checkerToExt_extensionComposition w
    (proof_T_componentValuesToChecker w hv ha hb)

/-! ## Primitive recursiveness of all displayed maps -/

abbrev ProjectionMapArgs := (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
abbrev ComponentMapArgs := (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)

def equalityValueToDefinednessPacked
    (z : ProjectionMapArgs) : ProofSequenceCode :=
  equalityValueToDefinedness z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

def projectionEqualityToPairPacked
    (z : ProjectionMapArgs) : ProofSequenceCode :=
  projectionEqualityToPair z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

def projectionEqualityToLeftPacked
    (z : ProjectionMapArgs) : ProofSequenceCode :=
  projectionEqualityToLeft z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2
    z.1.1.2 z.1.2 z.2

def componentValuesToCheckerPacked
    (z : ComponentMapArgs) : ProofSequenceCode :=
  componentValuesToChecker z.1.1.1.1.1.1.1 z.1.1.1.1.1.1.2
    z.1.1.1.1.1.2 z.1.1.1.1.2 z.1.1.1.2 z.1.1.2 z.1.2 z.2

def componentValuesToExtPacked
    (z : ComponentMapArgs) : ProofSequenceCode :=
  componentValuesToExt z.1.1.1.1.1.1.1 z.1.1.1.1.1.1.2
    z.1.1.1.1.1.2 z.1.1.1.1.2 z.1.1.1.2 z.1.1.2 z.1.2 z.2

private theorem primrec_projectionMapComponents :
    let u : ProjectionMapArgs → ℕ := fun z => z.1.1.1.1.1
    let p : ProjectionMapArgs → ℕ := fun z => z.1.1.1.1.2
    let q : ProjectionMapArgs → ℕ := fun z => z.1.1.1.2
    let r : ProjectionMapArgs → ℕ := fun z => z.1.1.2
    let t : ProjectionMapArgs → ℕ := fun z => z.1.2
    let i : ProjectionMapArgs → ℕ := fun z => z.2
    Primrec u ∧ Primrec p ∧ Primrec q ∧ Primrec r ∧ Primrec t ∧
      Primrec i := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))),
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

private theorem primrec_componentMapComponents :
    let v : ComponentMapArgs → ℕ := fun z => z.1.1.1.1.1.1.1
    let a : ComponentMapArgs → ℕ := fun z => z.1.1.1.1.1.1.2
    let b : ComponentMapArgs → ℕ := fun z => z.1.1.1.1.1.2
    let q : ComponentMapArgs → ℕ := fun z => z.1.1.1.1.2
    let r : ComponentMapArgs → ℕ := fun z => z.1.1.1.2
    let t : ComponentMapArgs → ℕ := fun z => z.1.1.2
    let c : ComponentMapArgs → ℕ := fun z => z.1.2
    let i : ComponentMapArgs → ℕ := fun z => z.2
    Primrec v ∧ Primrec a ∧ Primrec b ∧ Primrec q ∧ Primrec r ∧
      Primrec t ∧ Primrec c ∧ Primrec i := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))),
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

theorem primrec_equalityValueToDefinedness :
    Primrec equalityValueToDefinednessPacked := by
  obtain ⟨hu, hp, ha, hb, ht, hi⟩ := primrec_projectionMapComponents
  have hargs : Primrec (fun z : ProjectionMapArgs =>
      (((z.1.1.1.2, z.1.1.2), z.1.2), z.2)) :=
    ((ha.pair hb).pair ht).pair hi
  have hcode := primrec_projectionDefinednessAxiomCode.comp hargs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hcode) hu) hp).of_eq
      (fun _ => rfl)

theorem primrec_projectionEqualityToPair :
    Primrec projectionEqualityToPairPacked := by
  obtain ⟨hu, hp, hq, hr, ht, hi⟩ := primrec_projectionMapComponents
  have hj := primrec₂_project1PairIndex.comp hq hr
  have hbaseArgs : Primrec (fun z : ProjectionMapArgs =>
      (((((z.1.1.1.1.1, z.1.1.1.1.2),
        project1PairIndex z.1.1.1.2 z.1.1.2), z.1.1.2),
        z.1.2), z.2)) :=
    ((((hu.pair hp).pair hj).pair hr).pair ht).pair hi
  have hbase := primrec_equalityValueToDefinedness.comp hbaseArgs
  have hargs : Primrec (fun z : ProjectionMapArgs =>
      (((equalityValueToDefinedness z.1.1.1.1.1 z.1.1.1.1.2
          (project1PairIndex z.1.1.1.2 z.1.1.2) z.1.1.2 z.1.2 z.2,
        z.1.1.1.2),
        z.1.1.2), z.1.2)) :=
    ((hbase.pair hq).pair hr).pair ht
  exact (primrec_project1ToPair.comp hargs).of_eq (fun _ => rfl)

theorem primrec_projectionEqualityToLeft :
    Primrec projectionEqualityToLeftPacked := by
  obtain ⟨-, -, hq, hr, ht, -⟩ := primrec_projectionMapComponents
  have hargs : Primrec (fun z : ProjectionMapArgs =>
      (((projectionEqualityToPairPacked z, z.1.1.1.2),
        z.1.1.2), z.1.2)) :=
    ((primrec_projectionEqualityToPair.pair hq).pair hr).pair ht
  exact (primrec_pairToLeft.comp hargs).of_eq (fun _ => rfl)

theorem primrec_componentValuesToChecker :
    Primrec componentValuesToCheckerPacked := by
  obtain ⟨hv, ha, hb, hq, hr, ht, hc, hi⟩ :=
    primrec_componentMapComponents
  have hargs : Primrec (fun z : ComponentMapArgs =>
      ((((z.1.1.1.1.2, z.1.1.1.2), z.1.1.2), z.1.2), z.2)) :=
    (((hq.pair hr).pair ht).pair hc).pair hi
  have hcode := primrec_componentValuesToCheckerAxiomCode.comp hargs
  exact (primrec_mp.comp (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hcode) hv) ha) hb).of_eq
      (fun _ => rfl)

theorem primrec_componentValuesToExt :
    Primrec componentValuesToExtPacked := by
  obtain ⟨-, -, -, -, -, -, hc, hi⟩ := primrec_componentMapComponents
  have hargs : Primrec (fun z : ComponentMapArgs =>
      ((componentValuesToCheckerPacked z, z.1.2), z.2)) :=
    (primrec_componentValuesToChecker.pair hc).pair hi
  exact (primrec_checkerToExt.comp hargs).of_eq (fun _ => rfl)

end

end FailureOfComposition.NumericalExtensionComposition
