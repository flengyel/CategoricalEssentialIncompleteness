/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.Core

/-!
# Numerical proof transformations for the B1(8) theta computation

For a program index `q`, `thetaIndex q` first tensors `q` with the identity,
then applies the finite-extension checker, and finally takes the second
projection.  Thus its input is a coded pair `(t,i)`, rather than a common
input supplied to two programs.

This module extends the accepted extension-composition presentation by the
single scheme

`R(q,t,c) -> (C(c,i) -> H(q,t,i))`,

where `H(q,t,i)` is the graph tag for `thetaIndex q` at `(pair(t,i),i)`.
The presentation and both proof transformations below are numerical: all
displayed parameters are external natural numbers.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionTheta

open FiniteExtensionChecker NumericalExtensionComposition
open NumericalExtensionProofs NumericalProofBridge NumericalProductProofs
open TypedNearProduct TypedProgramCategory UniformIndexQuotient

noncomputable section

/-! ## The explicit theta program -/

/-- The production-numbering representative of
`p1 >> extensionChecker >> (q tensor identity)`, written in program
composition order.  `compIndex f g` applies `g` first and then `f`. -/
def thetaIndex (q : ℕ) : ℕ :=
  compIndex secondProjectionIndex
    (compIndex extensionCheckerIndex
      (tensorIndex q Kleene.identityIndex))

/-- The explicit theta representative depends primitive recursively on its
component-program index. -/
theorem primrec_thetaIndex : Primrec thetaIndex := by
  exact TypedProgramCategory.primrec₂_compIndex.comp
    (Primrec.const secondProjectionIndex)
    (TypedProgramCategory.primrec₂_compIndex.comp
      (Primrec.const extensionCheckerIndex)
      (primrec₂_tensorIndex.comp Primrec.id
        (Primrec.const Kleene.identityIndex)))

/-! ## Exact endpoints and the theta scheme -/

/-- The output tag `H(q,t,i)`. -/
def thetaInstanceString (q t i : ℕ) : FormulaString :=
  rightInstanceString (thetaIndex q) (Nat.pair t i) i

def thetaInstanceCode (q t i : ℕ) : FormulaCode :=
  encodeFormula (thetaInstanceString q t i)

@[simp] theorem thetaInstanceCode_eq_right (q t i : ℕ) :
    thetaInstanceCode q t i =
      rightInstanceCode (thetaIndex q) (Nat.pair t i) i := by
  simp [thetaInstanceCode, thetaInstanceString, rightInstanceCode]

theorem primrec_thetaInstanceString :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      thetaInstanceString z.1.1 z.1.2 z.2) := by
  have htheta : Primrec (fun z : (ℕ × ℕ) × ℕ => thetaIndex z.1.1) :=
    primrec_thetaIndex.comp (Primrec.fst.comp Primrec.fst)
  have hpair : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      Nat.pair z.1.2 z.2) :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact primrec_rightInstanceString.comp
    ((htheta.pair hpair).pair Primrec.snd)

theorem primrec_thetaInstanceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      thetaInstanceCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_thetaInstanceString

/-- The sole new implication scheme. -/
def componentAndCheckerToThetaAxiomString
    (q t c i : ℕ) : FormulaString :=
  impString (rightInstanceString q t c)
    (impString (checkerInstanceString c i)
      (thetaInstanceString q t i))

def componentAndCheckerToThetaAxiomCode
    (q t c i : ℕ) : FormulaCode :=
  encodeFormula (componentAndCheckerToThetaAxiomString q t c i)

@[simp] theorem componentAndCheckerToThetaAxiomCode_eq_imp
    (q t c i : ℕ) :
    componentAndCheckerToThetaAxiomCode q t c i =
      imp (rightInstanceCode q t c)
        (imp (checkerInstanceCode c i) (thetaInstanceCode q t i)) := by
  simp [componentAndCheckerToThetaAxiomCode,
    componentAndCheckerToThetaAxiomString, rightInstanceCode,
    checkerInstanceCode, thetaInstanceCode, imp]

abbrev ThetaSchemaArgs := (((ℕ × ℕ) × ℕ) × ℕ)

theorem primrec_componentAndCheckerToThetaAxiomString :
    Primrec (fun z : ThetaSchemaArgs =>
      componentAndCheckerToThetaAxiomString
        z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hq : Primrec (fun z : ThetaSchemaArgs => z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ht : Primrec (fun z : ThetaSchemaArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun z : ThetaSchemaArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : ThetaSchemaArgs => z.2) := Primrec.snd
  have hr := primrec_rightInstanceString.comp ((hq.pair ht).pair hc)
  have hcheck := primrec_checkerInstanceString.comp (hc.pair hi)
  have htheta := primrec_thetaInstanceString.comp ((hq.pair ht).pair hi)
  exact primrec_impString.comp hr (primrec_impString.comp hcheck htheta)

theorem primrec_componentAndCheckerToThetaAxiomCode :
    Primrec (fun z : ThetaSchemaArgs =>
      componentAndCheckerToThetaAxiomCode
        z.1.1.1 z.1.1.2 z.1.2 z.2) :=
  primrec_encodeFormula.comp
    primrec_componentAndCheckerToThetaAxiomString

/-! ## Exact primitive-recursive recognition -/

def thetaTokenAt (j : ℕ) (x : FormulaString) : ℕ :=
  x.getD j 0

private theorem primrec_thetaTokenAt (j : ℕ) :
    Primrec (thetaTokenAt j) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const j)

def recoveredThetaProgram (x : FormulaString) : ℕ :=
  thetaTokenAt 1 (lhsString x)

def recoveredThetaInput (x : FormulaString) : ℕ :=
  thetaTokenAt 2 (lhsString x)

def recoveredThetaComponent (x : FormulaString) : ℕ :=
  thetaTokenAt 3 (lhsString x)

def recoveredThetaParameter (x : FormulaString) : ℕ :=
  thetaTokenAt 3 (rhsString (rhsString x))

private theorem primrec_recoveredThetaProgram :
    Primrec recoveredThetaProgram :=
  (primrec_thetaTokenAt 1).comp primrec_lhsString

private theorem primrec_recoveredThetaInput :
    Primrec recoveredThetaInput :=
  (primrec_thetaTokenAt 2).comp primrec_lhsString

private theorem primrec_recoveredThetaComponent :
    Primrec recoveredThetaComponent :=
  (primrec_thetaTokenAt 3).comp primrec_lhsString

private theorem primrec_recoveredThetaParameter :
    Primrec recoveredThetaParameter :=
  (primrec_thetaTokenAt 3).comp
    (primrec_rhsString.comp primrec_rhsString)

@[simp] private theorem recoveredThetaProgram_axiomString
    (q t c i : ℕ) :
    recoveredThetaProgram (componentAndCheckerToThetaAxiomString q t c i) =
      q := by
  simp [recoveredThetaProgram, componentAndCheckerToThetaAxiomString,
    thetaTokenAt, rightInstanceString]

@[simp] private theorem recoveredThetaInput_axiomString
    (q t c i : ℕ) :
    recoveredThetaInput (componentAndCheckerToThetaAxiomString q t c i) =
      t := by
  simp [recoveredThetaInput, componentAndCheckerToThetaAxiomString,
    thetaTokenAt, rightInstanceString]

@[simp] private theorem recoveredThetaComponent_axiomString
    (q t c i : ℕ) :
    recoveredThetaComponent
        (componentAndCheckerToThetaAxiomString q t c i) = c := by
  simp [recoveredThetaComponent, componentAndCheckerToThetaAxiomString,
    thetaTokenAt, rightInstanceString]

@[simp] private theorem recoveredThetaParameter_axiomString
    (q t c i : ℕ) :
    recoveredThetaParameter
        (componentAndCheckerToThetaAxiomString q t c i) = i := by
  simp [recoveredThetaParameter, componentAndCheckerToThetaAxiomString,
    thetaInstanceString, thetaTokenAt, rightInstanceString]

def componentAndCheckerToThetaAxiomCandidate
    (x : FormulaString) : FormulaString :=
  componentAndCheckerToThetaAxiomString (recoveredThetaProgram x)
    (recoveredThetaInput x) (recoveredThetaComponent x)
    (recoveredThetaParameter x)

private theorem primrec_componentAndCheckerToThetaAxiomCandidate :
    Primrec componentAndCheckerToThetaAxiomCandidate := by
  exact (primrec_componentAndCheckerToThetaAxiomString.comp
    (((primrec_recoveredThetaProgram.pair
      primrec_recoveredThetaInput).pair
      primrec_recoveredThetaComponent).pair
      primrec_recoveredThetaParameter)).of_eq (fun _ => rfl)

/-- Exact shape of the new scheme.  Reconstructing the complete formula checks
the repeated component, input, and parameter occurrences, as well as both
fixed program constructors. -/
def ExtensionThetaAxiomShape (x : FormulaString) : Prop :=
  x = componentAndCheckerToThetaAxiomCandidate x

def extensionThetaAxiomTest (x : FormulaString) : Bool :=
  x == componentAndCheckerToThetaAxiomCandidate x

@[simp] theorem extensionThetaAxiomTest_eq_true_iff
    (x : FormulaString) :
    extensionThetaAxiomTest x = true ↔ ExtensionThetaAxiomShape x := by
  simp [extensionThetaAxiomTest, ExtensionThetaAxiomShape]

theorem extensionThetaAxiomShape_iff (x : FormulaString) :
    ExtensionThetaAxiomShape x ↔
      ∃ q t c i, x = componentAndCheckerToThetaAxiomString q t c i := by
  constructor
  · intro h
    exact ⟨recoveredThetaProgram x, recoveredThetaInput x,
      recoveredThetaComponent x, recoveredThetaParameter x, h⟩
  · rintro ⟨q, t, c, i, rfl⟩
    simp [ExtensionThetaAxiomShape,
      componentAndCheckerToThetaAxiomCandidate]

theorem primrec_extensionThetaAxiomTest :
    Primrec extensionThetaAxiomTest :=
  (Primrec.beq.comp Primrec.id
    primrec_componentAndCheckerToThetaAxiomCandidate).of_eq
    (fun x => by simp [extensionThetaAxiomTest])

/-! ## Extension of the B1(7) presentation -/

def ExtensionThetaLogicalAxiomShape (x : FormulaString) : Prop :=
  ExtensionCompositionLogicalAxiomShape x ∨ ExtensionThetaAxiomShape x

def extensionThetaLogicalAxiomTest (x : FormulaString) : Bool :=
  extensionCompositionLogicalAxiomTest x || extensionThetaAxiomTest x

@[simp] theorem extensionThetaLogicalAxiomTest_eq_true_iff
    (x : FormulaString) :
    extensionThetaLogicalAxiomTest x = true ↔
      ExtensionThetaLogicalAxiomShape x := by
  simp [extensionThetaLogicalAxiomTest,
    ExtensionThetaLogicalAxiomShape]

theorem primrec_extensionThetaLogicalAxiomTest :
    Primrec extensionThetaLogicalAxiomTest :=
  Primrec.or.comp primrec_extensionCompositionLogicalAxiomTest
    primrec_extensionThetaAxiomTest

/-- The common proof presentation for both B1(8) transformations. -/
def extensionThetaTheoryPresentation
    (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨extensionThetaLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def extensionThetaPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := extensionThetaTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_extensionThetaLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem extensionCompositionLogicalAxiom_holds_extensionTheta
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
      x) :
    (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change extensionCompositionLogicalAxiomTest x = true at h
  change extensionThetaLogicalAxiomTest x = true
  simp [extensionThetaLogicalAxiomTest, h]

private theorem extensionThetaAxiomShape_holds
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : ExtensionThetaAxiomShape x) :
    (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds x := by
  change extensionThetaLogicalAxiomTest x = true
  rw [extensionThetaLogicalAxiomTest_eq_true_iff]
  exact Or.inr h

theorem componentAndCheckerToThetaAxiom_holds
    (w : ℕ → ℕ → Bool) (q t c i : ℕ) :
    (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds
      (componentAndCheckerToThetaAxiomString q t c i) := by
  apply extensionThetaAxiomShape_holds
  rw [extensionThetaAxiomShape_iff]
  exact ⟨q, t, c, i, rfl⟩

/-- Accepted B1(7) proofs embed without changing their proof-sequence codes. -/
theorem proof_T_extensionComposition_to_extensionTheta
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p a) :
    Proof_T (extensionThetaTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro j hjlt
  obtain ⟨hline, -, hcase⟩ := hj j hjlt
  refine ⟨hline, by simp [extensionThetaTheoryPresentation,
    StringPredicate.Holds], ?_⟩
  rcases hcase with hlog | hax | hmp
  · exact Or.inl
      (extensionCompositionLogicalAxiom_holds_extensionTheta w hlog)
  · exact Or.inr (Or.inl (by
      simpa [extensionCompositionTheoryPresentation,
        extensionThetaTheoryPresentation] using hax))
  · exact Or.inr (Or.inr hmp)

theorem proof_T_finiteExtension_to_extensionTheta
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p a) :
    Proof_T (extensionThetaTheoryPresentation w) p a :=
  proof_T_extensionComposition_to_extensionTheta w
    (proof_T_finiteExtension_to_extensionComposition w hp)

theorem proof_T_extended_to_extensionTheta
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (extensionThetaTheoryPresentation w) p a :=
  proof_T_extensionComposition_to_extensionTheta w
    (proof_T_extended_to_extensionComposition w hp)

/-! ## Supplied-code proof transformations -/

/-- Two modus-ponens steps implementing the theta scheme. -/
def componentAndCheckerToTheta
    (p s q t c i : ℕ) : ProofSequenceCode :=
  mp (mp (oneLineProofCode
    (componentAndCheckerToThetaAxiomCode q t c i)) p) s

/-- Convert an `X(c,i)` proof to `C(c,i)` and then apply the theta map. -/
def componentAndExtToTheta
    (p s q t c i : ℕ) : ProofSequenceCode :=
  componentAndCheckerToTheta p (extToChecker s c i) q t c i

/-- The accepted extension-to-checker step is valid for every input proof
admitted by the new common checker. -/
theorem proof_T_extToChecker_extensionTheta
    (w : ℕ → ℕ → Bool) {p c i : ℕ}
    (hp : Proof_T (extensionThetaTheoryPresentation w) p
      (extensionInstanceCode c i)) :
    Proof_T (extensionThetaTheoryPresentation w)
      (extToChecker p c i) (checkerInstanceCode c i) := by
  apply proof_T_mp _ hp
  rw [← extensionToCheckerAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [extensionToCheckerAxiomCode, decodeFormula_encodeFormula]
  apply extensionCompositionLogicalAxiom_holds_extensionTheta
  apply finiteExtensionLogicalAxiom_holds_extensionComposition
  exact extensionToCheckerAxiom_holds w c i

theorem proof_T_componentAndCheckerToTheta
    (w : ℕ → ℕ → Bool) {p s q t c i : ℕ}
    (hp : Proof_T (extensionThetaTheoryPresentation w) p
      (rightInstanceCode q t c))
    (hs : Proof_T (extensionThetaTheoryPresentation w) s
      (checkerInstanceCode c i)) :
    Proof_T (extensionThetaTheoryPresentation w)
      (componentAndCheckerToTheta p s q t c i)
      (thetaInstanceCode q t i) := by
  apply proof_T_mp _ hs
  apply proof_T_mp _ hp
  rw [← componentAndCheckerToThetaAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [componentAndCheckerToThetaAxiomCode,
    decodeFormula_encodeFormula]
  exact componentAndCheckerToThetaAxiom_holds w q t c i

theorem proof_T_componentAndExtToTheta
    (w : ℕ → ℕ → Bool) {p s q t c i : ℕ}
    (hp : Proof_T (extensionThetaTheoryPresentation w) p
      (rightInstanceCode q t c))
    (hs : Proof_T (extensionThetaTheoryPresentation w) s
      (extensionInstanceCode c i)) :
    Proof_T (extensionThetaTheoryPresentation w)
      (componentAndExtToTheta p s q t c i)
      (thetaInstanceCode q t i) :=
  proof_T_componentAndCheckerToTheta w hp
    (proof_T_extToChecker_extensionTheta w hs)

/-! ## Primitive recursiveness of both maps -/

abbrev ThetaMapArgs := (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)

def componentAndCheckerToThetaPacked
    (z : ThetaMapArgs) : ProofSequenceCode :=
  componentAndCheckerToTheta z.1.1.1.1.1 z.1.1.1.1.2
    z.1.1.1.2 z.1.1.2 z.1.2 z.2

def componentAndExtToThetaPacked
    (z : ThetaMapArgs) : ProofSequenceCode :=
  componentAndExtToTheta z.1.1.1.1.1 z.1.1.1.1.2
    z.1.1.1.2 z.1.1.2 z.1.2 z.2

private theorem primrec_thetaMapComponents :
    let p : ThetaMapArgs → ℕ := fun z => z.1.1.1.1.1
    let s : ThetaMapArgs → ℕ := fun z => z.1.1.1.1.2
    let q : ThetaMapArgs → ℕ := fun z => z.1.1.1.2
    let t : ThetaMapArgs → ℕ := fun z => z.1.1.2
    let c : ThetaMapArgs → ℕ := fun z => z.1.2
    let i : ThetaMapArgs → ℕ := fun z => z.2
    Primrec p ∧ Primrec s ∧ Primrec q ∧ Primrec t ∧ Primrec c ∧
      Primrec i := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))),
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

theorem primrec_componentAndCheckerToTheta :
    Primrec componentAndCheckerToThetaPacked := by
  obtain ⟨hp, hs, hq, ht, hc, hi⟩ := primrec_thetaMapComponents
  have hargs : Primrec (fun z : ThetaMapArgs =>
      (((z.1.1.1.2, z.1.1.2), z.1.2), z.2)) :=
    ((hq.pair ht).pair hc).pair hi
  have hcode := primrec_componentAndCheckerToThetaAxiomCode.comp hargs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hcode) hp) hs).of_eq
      (fun _ => rfl)

theorem primrec_componentAndExtToTheta :
    Primrec componentAndExtToThetaPacked := by
  obtain ⟨hp, hs, hq, ht, hc, hi⟩ := primrec_thetaMapComponents
  have hextArgs : Primrec (fun z : ThetaMapArgs =>
      ((z.1.1.1.1.2, z.1.2), z.2)) :=
    (hs.pair hc).pair hi
  have hext := primrec_extToChecker.comp hextArgs
  have hargs : Primrec (fun z : ThetaMapArgs =>
      (((((z.1.1.1.1.1, extToChecker z.1.1.1.1.2 z.1.2 z.2),
        z.1.1.1.2), z.1.1.2), z.1.2), z.2)) :=
    ((((hp.pair hext).pair hq).pair ht).pair hc).pair hi
  exact (primrec_componentAndCheckerToTheta.comp hargs).of_eq
    (fun _ => rfl)

end

end FailureOfComposition.NumericalExtensionTheta
