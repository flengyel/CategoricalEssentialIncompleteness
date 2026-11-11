/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.RETheory
public import FailureOfComposition.TypedNearProduct

/-!
# Numerical product-definedness proof rules

This module defines the numerical tag for program definedness, the five
product-definedness implication schemes, their primitive-recursive
presentation, and the induced maps on numerical proof codes.  It extends the
accepted numerical proof bridge without changing any old proof code.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.ArithmeticCode
open CategoricalRiceShapiro.Evaluator
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.NumericalProductProofs

open ConcreteEvaluator ProofSearch
open NumericalProofBridge TypedNearProduct TypedProgramCategory
open UniformIndexQuotient

/-! ## Definedness and the selected program indices -/

/-- The one-input formula saying that program `q` has an output.  The program
index is an external natural number; the input and witness range over the
ambient arithmetic model. -/
def definednessFormula (q : ℕ) : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ y, !(eventualGraph q).val x y”

/-- The diagonal instance of the computation-domain graph.  Its closed numeral
instance is the arithmetic meaning of `definednessTag`. -/
def domainDefinednessFormula (q : ℕ) : 𝚺₁.Semisentence 1 :=
  (eventualGraph (domainIndex q)).rew
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 1),
      (#0 : ArithmeticSemiterm Empty 1)])

@[simp] theorem definednessFormula_eval
    {M : Type*} [ORingStructure M] (q : ℕ) (x : M) :
    (definednessFormula q).val.Evalb ![x] ↔
      ∃ y : M, (eventualGraph q).val.Evalb ![x, y] := by
  simp [definednessFormula]

@[simp] theorem definednessFormula_instance_eval
    {M : Type*} [ORingStructure M] (q n : ℕ) :
    ((definednessFormula q).val/[n]).Evalb (M := M) ![] ↔
      (definednessFormula q).val.Evalb
        ![(ORingStructure.numeral n : M)] := by
  simp

@[simp] theorem domainDefinednessFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (x : M) :
    (domainDefinednessFormula q).val.Evalb ![x] ↔
      ∃ y : M, (eventualGraph q).val.Evalb ![x, y] := by
  have hb : (fun i : Fin 2 => Semiterm.val ![x]
      (Empty.elim : Empty → M)
      ((Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 1),
        (#0 : ArithmeticSemiterm Empty 1)])
        (#i : ArithmeticSemiterm Empty 2))) = ![x, x] := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp
  have hf : (fun i : Empty => Semiterm.val ![x]
      (Empty.elim : Empty → M)
      ((Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 1),
        (#0 : ArithmeticSemiterm Empty 1)])
        (&i : ArithmeticSemiterm Empty 2))) = Empty.elim :=
    funext (fun i => i.elim)
  simp only [domainDefinednessFormula,
    HierarchySymbol.Semiformula.val_rew, Semiformula.eval_rew,
    Function.comp_def, hb, hf]
  rw [eventualGraph_domainIndex_eval]
  constructor
  · exact And.right
  · intro h
    exact ⟨rfl, h⟩

/-- PA proves that the selected domain-graph formula and ordinary existential
definedness agree at every (possibly nonstandard) input. -/
noncomputable def definednessEquivalenceSentence (q : ℕ) :
    ArithmeticSentence :=
  “∀ x, !(domainDefinednessFormula q) x ↔ !(definednessFormula q) x”

theorem pa_proves_definednessEquivalence (q : ℕ) :
    𝗣𝗔 ⊢ definednessEquivalenceSentence q := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, definednessEquivalenceSentence]

/-- The short numerical tag `D(q,n)`.  This is a code in the small proof
language, not the code of the arithmetic graph sentence itself. -/
def definednessTag (q n : ℕ) : FormulaCode :=
  rightInstanceCode (domainIndex q) n n

/-- The formula string represented by `definednessTag`. -/
def definednessString (q n : ℕ) : FormulaString :=
  rightInstanceString (domainIndex q) n n

/-- The actual arithmetic-syntax code of the closed domain-graph instance.
This is distinct from the short tag `definednessTag`. -/
def definednessSentenceCode (q n : ℕ) : ℕ :=
  rightSentenceCode (domainIndex q) n n

@[simp] theorem definednessTag_eq_encode (q n : ℕ) :
    definednessTag q n = encodeFormula (definednessString q n) := by
  rfl

theorem definednessSentenceCode_eq_encode (q n : ℕ) :
    definednessSentenceCode q n =
      Encodable.encode
        ((eventualGraph (domainIndex q)).val/[n, n] : ArithmeticSentence) := by
  rfl

theorem primrec₂_definednessString : Primrec₂ definednessString := by
  have hdom : Primrec (fun z : ℕ × ℕ => domainIndex z.1) :=
    primrec_domainIndex.comp Primrec.fst
  exact (primrec_rightInstanceString.comp
    ((hdom.pair Primrec.snd).pair Primrec.snd)).to₂

theorem primrec₂_definednessTag : Primrec₂ definednessTag :=
  primrec_encodeFormula.comp primrec₂_definednessString

theorem primrec₂_definednessSentenceCode :
    Primrec₂ definednessSentenceCode := by
  have hdom : Primrec (fun z : ℕ × ℕ => domainIndex z.1) :=
    primrec_domainIndex.comp Primrec.fst
  exact (primrec_rightSentenceCode.comp
    ((hdom.pair Primrec.snd).pair Primrec.snd)).to₂

/-- The program that pairs the outputs of `q` and `r` on their common input. -/
abbrev pairedIndex (q r : ℕ) : ℕ := pairIndex q r

/-- First projection after partial program pairing.  Both component programs
must finish before the projection executes. -/
def project0PairIndex (q r : ℕ) : ℕ :=
  compIndex firstProjectionIndex (pairIndex q r)

/-- Second projection after partial program pairing.  Both component programs
must finish before the projection executes. -/
def project1PairIndex (q r : ℕ) : ℕ :=
  compIndex secondProjectionIndex (pairIndex q r)

theorem primrec₂_project0PairIndex : Primrec₂ project0PairIndex :=
  primrec₂_compIndex.comp (Primrec.const firstProjectionIndex)
    primrec₂_pairIndex

theorem primrec₂_project1PairIndex : Primrec₂ project1PairIndex :=
  primrec₂_compIndex.comp (Primrec.const secondProjectionIndex)
    primrec₂_pairIndex

/-! ## The five implication schemes -/

def project0ToPairAxiomString (q r n : ℕ) : FormulaString :=
  impString (definednessString (project0PairIndex q r) n)
    (definednessString (pairIndex q r) n)

def project1ToPairAxiomString (q r n : ℕ) : FormulaString :=
  impString (definednessString (project1PairIndex q r) n)
    (definednessString (pairIndex q r) n)

def pairToLeftAxiomString (q r n : ℕ) : FormulaString :=
  impString (definednessString (pairIndex q r) n)
    (definednessString q n)

def pairToRightAxiomString (q r n : ℕ) : FormulaString :=
  impString (definednessString (pairIndex q r) n)
    (definednessString r n)

def componentsToPairAxiomString (q r n : ℕ) : FormulaString :=
  impString (definednessString q n)
    (impString (definednessString r n)
      (definednessString (pairIndex q r) n))

def project0ToPairAxiomCode (q r n : ℕ) : FormulaCode :=
  encodeFormula (project0ToPairAxiomString q r n)

def project1ToPairAxiomCode (q r n : ℕ) : FormulaCode :=
  encodeFormula (project1ToPairAxiomString q r n)

def pairToLeftAxiomCode (q r n : ℕ) : FormulaCode :=
  encodeFormula (pairToLeftAxiomString q r n)

def pairToRightAxiomCode (q r n : ℕ) : FormulaCode :=
  encodeFormula (pairToRightAxiomString q r n)

def componentsToPairAxiomCode (q r n : ℕ) : FormulaCode :=
  encodeFormula (componentsToPairAxiomString q r n)

@[simp] theorem project0ToPairAxiomCode_eq_imp (q r n : ℕ) :
    project0ToPairAxiomCode q r n =
      imp (definednessTag (project0PairIndex q r) n)
        (definednessTag (pairIndex q r) n) := by
  rw [definednessTag_eq_encode, definednessTag_eq_encode]
  unfold project0ToPairAxiomCode project0ToPairAxiomString
    Metamath.Feferman.imp
  rw [decodeFormula_encodeFormula, decodeFormula_encodeFormula]

@[simp] theorem project1ToPairAxiomCode_eq_imp (q r n : ℕ) :
    project1ToPairAxiomCode q r n =
      imp (definednessTag (project1PairIndex q r) n)
        (definednessTag (pairIndex q r) n) := by
  rw [definednessTag_eq_encode, definednessTag_eq_encode]
  unfold project1ToPairAxiomCode project1ToPairAxiomString
    Metamath.Feferman.imp
  rw [decodeFormula_encodeFormula, decodeFormula_encodeFormula]

@[simp] theorem pairToLeftAxiomCode_eq_imp (q r n : ℕ) :
    pairToLeftAxiomCode q r n =
      imp (definednessTag (pairIndex q r) n) (definednessTag q n) := by
  rw [definednessTag_eq_encode, definednessTag_eq_encode]
  unfold pairToLeftAxiomCode pairToLeftAxiomString
    Metamath.Feferman.imp
  rw [decodeFormula_encodeFormula, decodeFormula_encodeFormula]

@[simp] theorem pairToRightAxiomCode_eq_imp (q r n : ℕ) :
    pairToRightAxiomCode q r n =
      imp (definednessTag (pairIndex q r) n) (definednessTag r n) := by
  rw [definednessTag_eq_encode, definednessTag_eq_encode]
  unfold pairToRightAxiomCode pairToRightAxiomString
    Metamath.Feferman.imp
  rw [decodeFormula_encodeFormula, decodeFormula_encodeFormula]

@[simp] theorem componentsToPairAxiomCode_eq_imp (q r n : ℕ) :
    componentsToPairAxiomCode q r n =
      imp (definednessTag q n)
        (imp (definednessTag r n)
          (definednessTag (pairIndex q r) n)) := by
  rw [definednessTag_eq_encode, definednessTag_eq_encode,
    definednessTag_eq_encode]
  unfold componentsToPairAxiomCode componentsToPairAxiomString
    Metamath.Feferman.imp
  simp only [decodeFormula_encodeFormula]

abbrev ProductSchemaArgs := (ℕ × ℕ) × ℕ

private theorem primrec_productSchemaComponents :
    let q : ProductSchemaArgs → ℕ := fun z => z.1.1
    let r : ProductSchemaArgs → ℕ := fun z => z.1.2
    let n : ProductSchemaArgs → ℕ := fun z => z.2
    Primrec q ∧ Primrec r ∧ Primrec n := by
  exact ⟨Primrec.fst.comp Primrec.fst,
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

theorem primrec_project0ToPairAxiomString :
    Primrec (fun z : ProductSchemaArgs =>
      project0ToPairAxiomString z.1.1 z.1.2 z.2) := by
  obtain ⟨hq, hr, hn⟩ := primrec_productSchemaComponents
  have hp := primrec₂_pairIndex.comp hq hr
  have hproj := primrec₂_project0PairIndex.comp hq hr
  exact primrec_impString.comp
    (primrec₂_definednessString.comp hproj hn)
    (primrec₂_definednessString.comp hp hn)

theorem primrec_project1ToPairAxiomString :
    Primrec (fun z : ProductSchemaArgs =>
      project1ToPairAxiomString z.1.1 z.1.2 z.2) := by
  obtain ⟨hq, hr, hn⟩ := primrec_productSchemaComponents
  have hp := primrec₂_pairIndex.comp hq hr
  have hproj := primrec₂_project1PairIndex.comp hq hr
  exact primrec_impString.comp
    (primrec₂_definednessString.comp hproj hn)
    (primrec₂_definednessString.comp hp hn)

theorem primrec_pairToLeftAxiomString :
    Primrec (fun z : ProductSchemaArgs =>
      pairToLeftAxiomString z.1.1 z.1.2 z.2) := by
  obtain ⟨hq, hr, hn⟩ := primrec_productSchemaComponents
  have hp := primrec₂_pairIndex.comp hq hr
  exact primrec_impString.comp
    (primrec₂_definednessString.comp hp hn)
    (primrec₂_definednessString.comp hq hn)

theorem primrec_pairToRightAxiomString :
    Primrec (fun z : ProductSchemaArgs =>
      pairToRightAxiomString z.1.1 z.1.2 z.2) := by
  obtain ⟨hq, hr, hn⟩ := primrec_productSchemaComponents
  have hp := primrec₂_pairIndex.comp hq hr
  exact primrec_impString.comp
    (primrec₂_definednessString.comp hp hn)
    (primrec₂_definednessString.comp hr hn)

theorem primrec_componentsToPairAxiomString :
    Primrec (fun z : ProductSchemaArgs =>
      componentsToPairAxiomString z.1.1 z.1.2 z.2) := by
  obtain ⟨hq, hr, hn⟩ := primrec_productSchemaComponents
  have hp := primrec₂_pairIndex.comp hq hr
  exact primrec_impString.comp
    (primrec₂_definednessString.comp hq hn)
    (primrec_impString.comp
      (primrec₂_definednessString.comp hr hn)
      (primrec₂_definednessString.comp hp hn))

theorem primrec_project0ToPairAxiomCode :
    Primrec (fun z : ProductSchemaArgs =>
      project0ToPairAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_project0ToPairAxiomString

theorem primrec_project1ToPairAxiomCode :
    Primrec (fun z : ProductSchemaArgs =>
      project1ToPairAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_project1ToPairAxiomString

theorem primrec_pairToLeftAxiomCode :
    Primrec (fun z : ProductSchemaArgs =>
      pairToLeftAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_pairToLeftAxiomString

theorem primrec_pairToRightAxiomCode :
    Primrec (fun z : ProductSchemaArgs =>
      pairToRightAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_pairToRightAxiomString

theorem primrec_componentsToPairAxiomCode :
    Primrec (fun z : ProductSchemaArgs =>
      componentsToPairAxiomCode z.1.1 z.1.2 z.2) :=
  primrec_encodeFormula.comp primrec_componentsToPairAxiomString

/-! ## Exact primitive-recursive schema recognition -/

def productTokenAt (i : ℕ) (s : FormulaString) : ℕ := s.getD i 0

private theorem primrec_productTokenAt (i : ℕ) :
    Primrec (productTokenAt i) :=
  (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)

private theorem primrec_partrecCodePayload : Primrec partrecCodePayload := by
  unfold partrecCodePayload
  exact Primrec.nat_div2.comp (Primrec.nat_div2.comp
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 4)))

private theorem primrec_partrecCodePayload₁ : Primrec partrecCodePayload₁ :=
  Primrec.fst.comp (Primrec.unpair.comp primrec_partrecCodePayload)

private theorem primrec_partrecCodePayload₂ : Primrec partrecCodePayload₂ :=
  Primrec.snd.comp (Primrec.unpair.comp primrec_partrecCodePayload)

/-- Recover the program placed inside a generated definedness tag.  Exact
reconstruction below rejects every malformed use of this decoder. -/
def recoveredDefinednessProgram (s : FormulaString) : ℕ :=
  partrecCodePayload₂ (partrecCodePayload₂ (productTokenAt 1 s))

def recoveredDefinednessInput (s : FormulaString) : ℕ :=
  productTokenAt 2 s

private theorem primrec_recoveredDefinednessProgram :
    Primrec recoveredDefinednessProgram :=
  primrec_partrecCodePayload₂.comp
    (primrec_partrecCodePayload₂.comp (primrec_productTokenAt 1))

private theorem primrec_recoveredDefinednessInput :
    Primrec recoveredDefinednessInput := primrec_productTokenAt 2

@[simp] private theorem recoveredDefinednessProgram_definednessString
    (q n : ℕ) :
    recoveredDefinednessProgram (definednessString q n) = q := by
  simp only [recoveredDefinednessProgram, definednessString, rightInstanceString,
    productTokenAt, List.getD_cons_zero, List.getD_cons_succ,
    domainIndex_eq_canonical]
  rw [canonicalPartrecCompIndex_inner_index,
    pairIndex_eq_canonical, canonicalPartrecPairIndex_right]

@[simp] private theorem recoveredDefinednessInput_definednessString
    (q n : ℕ) :
    recoveredDefinednessInput (definednessString q n) = n := by
  simp [recoveredDefinednessInput, productTokenAt, definednessString,
    rightInstanceString]

def recoveredPairLeft (s : FormulaString) : ℕ :=
  partrecCodePayload₁ (recoveredDefinednessProgram s)

def recoveredPairRight (s : FormulaString) : ℕ :=
  partrecCodePayload₂ (recoveredDefinednessProgram s)

private theorem primrec_recoveredPairLeft : Primrec recoveredPairLeft :=
  primrec_partrecCodePayload₁.comp primrec_recoveredDefinednessProgram

private theorem primrec_recoveredPairRight : Primrec recoveredPairRight :=
  primrec_partrecCodePayload₂.comp primrec_recoveredDefinednessProgram

@[simp] private theorem recoveredPairLeft_pair
    (q r n : ℕ) :
    recoveredPairLeft (definednessString (pairIndex q r) n) = q := by
  simp [recoveredPairLeft, pairIndex_eq_canonical,
    canonicalPartrecPairIndex_left]

@[simp] private theorem recoveredPairRight_pair
    (q r n : ℕ) :
    recoveredPairRight (definednessString (pairIndex q r) n) = r := by
  simp [recoveredPairRight, pairIndex_eq_canonical,
    canonicalPartrecPairIndex_right]

def project0ToPairCandidate (s : FormulaString) : FormulaString :=
  let d := rhsString s
  project0ToPairAxiomString (recoveredPairLeft d) (recoveredPairRight d)
    (recoveredDefinednessInput d)

def project1ToPairCandidate (s : FormulaString) : FormulaString :=
  let d := rhsString s
  project1ToPairAxiomString (recoveredPairLeft d) (recoveredPairRight d)
    (recoveredDefinednessInput d)

def pairToLeftCandidate (s : FormulaString) : FormulaString :=
  let d := lhsString s
  pairToLeftAxiomString (recoveredPairLeft d) (recoveredPairRight d)
    (recoveredDefinednessInput d)

def pairToRightCandidate (s : FormulaString) : FormulaString :=
  let d := lhsString s
  pairToRightAxiomString (recoveredPairLeft d) (recoveredPairRight d)
    (recoveredDefinednessInput d)

def componentsToPairCandidate (s : FormulaString) : FormulaString :=
  let dq := lhsString s
  let dr := lhsString (rhsString s)
  componentsToPairAxiomString (recoveredDefinednessProgram dq)
    (recoveredDefinednessProgram dr) (recoveredDefinednessInput dq)

private theorem primrec_project0ToPairCandidate :
    Primrec project0ToPairCandidate := by
  have hd := primrec_rhsString
  exact (primrec_project0ToPairAxiomString.comp
    (((primrec_recoveredPairLeft.comp hd).pair
      (primrec_recoveredPairRight.comp hd)).pair
        (primrec_recoveredDefinednessInput.comp hd))).of_eq (fun _ => rfl)

private theorem primrec_project1ToPairCandidate :
    Primrec project1ToPairCandidate := by
  have hd := primrec_rhsString
  exact (primrec_project1ToPairAxiomString.comp
    (((primrec_recoveredPairLeft.comp hd).pair
      (primrec_recoveredPairRight.comp hd)).pair
        (primrec_recoveredDefinednessInput.comp hd))).of_eq (fun _ => rfl)

private theorem primrec_pairToLeftCandidate : Primrec pairToLeftCandidate := by
  have hd := primrec_lhsString
  exact (primrec_pairToLeftAxiomString.comp
    (((primrec_recoveredPairLeft.comp hd).pair
      (primrec_recoveredPairRight.comp hd)).pair
        (primrec_recoveredDefinednessInput.comp hd))).of_eq (fun _ => rfl)

private theorem primrec_pairToRightCandidate : Primrec pairToRightCandidate := by
  have hd := primrec_lhsString
  exact (primrec_pairToRightAxiomString.comp
    (((primrec_recoveredPairLeft.comp hd).pair
      (primrec_recoveredPairRight.comp hd)).pair
        (primrec_recoveredDefinednessInput.comp hd))).of_eq (fun _ => rfl)

private theorem primrec_componentsToPairCandidate :
    Primrec componentsToPairCandidate := by
  have hdq := primrec_lhsString
  have hdr := primrec_lhsString.comp primrec_rhsString
  exact (primrec_componentsToPairAxiomString.comp
    (((primrec_recoveredDefinednessProgram.comp hdq).pair
      (primrec_recoveredDefinednessProgram.comp hdr)).pair
        (primrec_recoveredDefinednessInput.comp hdq))).of_eq (fun _ => rfl)

def ProductAxiomShape (s : FormulaString) : Prop :=
  s = project0ToPairCandidate s ∨
  s = project1ToPairCandidate s ∨
  s = pairToLeftCandidate s ∨
  s = pairToRightCandidate s ∨
  s = componentsToPairCandidate s

def project0ToPairAxiomTest (s : FormulaString) : Bool :=
  s == project0ToPairCandidate s

def project1ToPairAxiomTest (s : FormulaString) : Bool :=
  s == project1ToPairCandidate s

def pairToLeftAxiomTest (s : FormulaString) : Bool :=
  s == pairToLeftCandidate s

def pairToRightAxiomTest (s : FormulaString) : Bool :=
  s == pairToRightCandidate s

def componentsToPairAxiomTest (s : FormulaString) : Bool :=
  s == componentsToPairCandidate s

def productAxiomTest (s : FormulaString) : Bool :=
  project0ToPairAxiomTest s ||
  (project1ToPairAxiomTest s ||
    (pairToLeftAxiomTest s ||
      (pairToRightAxiomTest s || componentsToPairAxiomTest s)))

@[simp] theorem productAxiomTest_eq_true_iff (s : FormulaString) :
    productAxiomTest s = true ↔ ProductAxiomShape s := by
  simp [productAxiomTest, project0ToPairAxiomTest,
    project1ToPairAxiomTest, pairToLeftAxiomTest,
    pairToRightAxiomTest, componentsToPairAxiomTest, ProductAxiomShape]

theorem productAxiomShape_iff (s : FormulaString) :
    ProductAxiomShape s ↔
      (∃ q r n, s = project0ToPairAxiomString q r n) ∨
      (∃ q r n, s = project1ToPairAxiomString q r n) ∨
      (∃ q r n, s = pairToLeftAxiomString q r n) ∨
      (∃ q r n, s = pairToRightAxiomString q r n) ∨
      (∃ q r n, s = componentsToPairAxiomString q r n) := by
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl ⟨recoveredPairLeft (rhsString s),
        recoveredPairRight (rhsString s),
        recoveredDefinednessInput (rhsString s), h⟩
    · exact Or.inr (Or.inl ⟨recoveredPairLeft (rhsString s),
        recoveredPairRight (rhsString s),
        recoveredDefinednessInput (rhsString s), h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨recoveredPairLeft (lhsString s),
        recoveredPairRight (lhsString s),
        recoveredDefinednessInput (lhsString s), h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨recoveredPairLeft (lhsString s),
          recoveredPairRight (lhsString s),
          recoveredDefinednessInput (lhsString s), h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨recoveredDefinednessProgram (lhsString s),
          recoveredDefinednessProgram (lhsString (rhsString s)),
          recoveredDefinednessInput (lhsString s), h⟩)))
  · rintro (⟨q, r, n, rfl⟩ | ⟨q, r, n, rfl⟩ | ⟨q, r, n, rfl⟩ |
      ⟨q, r, n, rfl⟩ | ⟨q, r, n, rfl⟩)
    · exact Or.inl (by simp only [project0ToPairCandidate,
        project0ToPairAxiomString, rhsString_impString,
        recoveredPairLeft_pair, recoveredPairRight_pair,
        recoveredDefinednessInput_definednessString])
    · exact Or.inr (Or.inl (by simp only [project1ToPairCandidate,
        project1ToPairAxiomString, rhsString_impString,
        recoveredPairLeft_pair, recoveredPairRight_pair,
        recoveredDefinednessInput_definednessString]))
    · exact Or.inr (Or.inr (Or.inl (by simp only [pairToLeftCandidate,
        pairToLeftAxiomString, lhsString_impString,
        recoveredPairLeft_pair, recoveredPairRight_pair,
        recoveredDefinednessInput_definednessString])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (by simp only [pairToRightCandidate, pairToRightAxiomString,
          lhsString_impString, recoveredPairLeft_pair,
          recoveredPairRight_pair,
          recoveredDefinednessInput_definednessString]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (by simp [componentsToPairCandidate, componentsToPairAxiomString]))))

private theorem primrec_project0ToPairAxiomTest :
    Primrec project0ToPairAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_project0ToPairCandidate).of_eq
    (fun s => by simp [project0ToPairAxiomTest])

private theorem primrec_project1ToPairAxiomTest :
    Primrec project1ToPairAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_project1ToPairCandidate).of_eq
    (fun s => by simp [project1ToPairAxiomTest])

private theorem primrec_pairToLeftAxiomTest : Primrec pairToLeftAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_pairToLeftCandidate).of_eq
    (fun s => by simp [pairToLeftAxiomTest])

private theorem primrec_pairToRightAxiomTest : Primrec pairToRightAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_pairToRightCandidate).of_eq
    (fun s => by simp [pairToRightAxiomTest])

private theorem primrec_componentsToPairAxiomTest :
    Primrec componentsToPairAxiomTest :=
  (Primrec.beq.comp Primrec.id primrec_componentsToPairCandidate).of_eq
    (fun s => by simp [componentsToPairAxiomTest])

theorem primrec_productAxiomTest : Primrec productAxiomTest := by
  unfold productAxiomTest
  exact Primrec.or.comp
    primrec_project0ToPairAxiomTest
    (Primrec.or.comp
      primrec_project1ToPairAxiomTest
      (Primrec.or.comp
        primrec_pairToLeftAxiomTest
        (Primrec.or.comp
          primrec_pairToRightAxiomTest
          primrec_componentsToPairAxiomTest)))

/-! ## The product extension of the accepted presentation -/

def ProductLogicalAxiomShape (s : FormulaString) : Prop :=
  ExtendedLogicalAxiomShape s ∨ ProductAxiomShape s

def productLogicalAxiomTest (s : FormulaString) : Bool :=
  extendedLogicalAxiomTest s || productAxiomTest s

@[simp] theorem productLogicalAxiomTest_eq_true_iff (s : FormulaString) :
    productLogicalAxiomTest s = true ↔ ProductLogicalAxiomShape s := by
  simp [productLogicalAxiomTest, ProductLogicalAxiomShape]

theorem primrec_productLogicalAxiomTest : Primrec productLogicalAxiomTest :=
  Primrec.or.comp primrec_extendedLogicalAxiomTest primrec_productAxiomTest

/-- The accepted extended presentation with the five product-definedness
schemes added as logical axioms.  Its theory-axiom test is unchanged. -/
def productTheoryPresentation (w : ℕ → ℕ → Bool) : TheoryPresentation where
  syn := {
    formula := ⟨fun _ => true⟩
    logicalAxiom := ⟨productLogicalAxiomTest⟩
    logicalAxiom_formula := by simp [StringPredicate.Holds]
    formula_imp_iff := by simp [StringPredicate.Holds]
  }
  ax := ⟨axiomTest w⟩
  ax_formula := by simp [StringPredicate.Holds]

def productPRTheoryPresentation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    PRTheoryPresentation where
  toTheory := productTheoryPresentation w
  formula_prim := Primrec.const true
  logicalAxiom_prim := primrec_productLogicalAxiomTest
  ax_prim := primrec_axiomTest w hw

theorem extendedLogicalAxiom_holds_product
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds s) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change extendedLogicalAxiomTest s = true at h
  change productLogicalAxiomTest s = true
  simp [productLogicalAxiomTest, h]

private theorem productAxiomShape_holds
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : ProductAxiomShape s) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds s := by
  change productLogicalAxiomTest s = true
  exact (productLogicalAxiomTest_eq_true_iff s).mpr (Or.inr h)

theorem project0ToPairAxiom_holds
    (w : ℕ → ℕ → Bool) (q r n : ℕ) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds
      (project0ToPairAxiomString q r n) := by
  apply productAxiomShape_holds
  rw [productAxiomShape_iff]
  exact Or.inl ⟨q, r, n, rfl⟩

theorem project1ToPairAxiom_holds
    (w : ℕ → ℕ → Bool) (q r n : ℕ) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds
      (project1ToPairAxiomString q r n) := by
  apply productAxiomShape_holds
  rw [productAxiomShape_iff]
  exact Or.inr (Or.inl ⟨q, r, n, rfl⟩)

theorem pairToLeftAxiom_holds
    (w : ℕ → ℕ → Bool) (q r n : ℕ) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds
      (pairToLeftAxiomString q r n) := by
  apply productAxiomShape_holds
  rw [productAxiomShape_iff]
  exact Or.inr (Or.inr (Or.inl ⟨q, r, n, rfl⟩))

theorem pairToRightAxiom_holds
    (w : ℕ → ℕ → Bool) (q r n : ℕ) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds
      (pairToRightAxiomString q r n) := by
  apply productAxiomShape_holds
  rw [productAxiomShape_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, r, n, rfl⟩)))

theorem componentsToPairAxiom_holds
    (w : ℕ → ℕ → Bool) (q r n : ℕ) :
    (productTheoryPresentation w).syn.logicalAxiom.Holds
      (componentsToPairAxiomString q r n) := by
  apply productAxiomShape_holds
  rw [productAxiomShape_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, r, n, rfl⟩)))

/-- Old numerical derivations embed without changing their numerical codes. -/
theorem proof_T_extended_to_product
    (w : ℕ → ℕ → Bool) {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    Proof_T (productTheoryPresentation w) p a := by
  obtain ⟨hne, hlast, hj⟩ := hp
  refine ⟨hne, hlast, ?_⟩
  intro i hi
  obtain ⟨hline, hformula, hcase⟩ := hj i hi
  refine ⟨hline, ?_, ?_⟩
  · simp [productTheoryPresentation, StringPredicate.Holds]
  · rcases hcase with hlog | hax | hmp
    · exact Or.inl (extendedLogicalAxiom_holds_product w hlog)
    · exact Or.inr (Or.inl (by
        simpa [extendedTheoryPresentation, productTheoryPresentation] using hax))
    · exact Or.inr (Or.inr hmp)

/-! ## Total primitive-recursive proof maps -/

def project0ToPair (p q r n : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (project0ToPairAxiomCode q r n)) p

def project1ToPair (p q r n : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (project1ToPairAxiomCode q r n)) p

def pairToLeft (p q r n : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (pairToLeftAxiomCode q r n)) p

def pairToRight (p q r n : ℕ) : ProofSequenceCode :=
  mp (oneLineProofCode (pairToRightAxiomCode q r n)) p

def componentsToPair (p h q r n : ℕ) : ProofSequenceCode :=
  mp (mp (oneLineProofCode (componentsToPairAxiomCode q r n)) p) h

theorem proof_T_project0ToPair
    (w : ℕ → ℕ → Bool) {p q r n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p
      (definednessTag (project0PairIndex q r) n)) :
    Proof_T (productTheoryPresentation w) (project0ToPair p q r n)
      (definednessTag (pairIndex q r) n) := by
  apply proof_T_mp _ hp
  rw [← project0ToPairAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [project0ToPairAxiomCode, decodeFormula_encodeFormula]
  exact project0ToPairAxiom_holds w q r n

theorem proof_T_project1ToPair
    (w : ℕ → ℕ → Bool) {p q r n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p
      (definednessTag (project1PairIndex q r) n)) :
    Proof_T (productTheoryPresentation w) (project1ToPair p q r n)
      (definednessTag (pairIndex q r) n) := by
  apply proof_T_mp _ hp
  rw [← project1ToPairAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [project1ToPairAxiomCode, decodeFormula_encodeFormula]
  exact project1ToPairAxiom_holds w q r n

theorem proof_T_pairToLeft
    (w : ℕ → ℕ → Bool) {p q r n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p
      (definednessTag (pairIndex q r) n)) :
    Proof_T (productTheoryPresentation w) (pairToLeft p q r n)
      (definednessTag q n) := by
  apply proof_T_mp _ hp
  rw [← pairToLeftAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [pairToLeftAxiomCode, decodeFormula_encodeFormula]
  exact pairToLeftAxiom_holds w q r n

theorem proof_T_pairToRight
    (w : ℕ → ℕ → Bool) {p q r n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p
      (definednessTag (pairIndex q r) n)) :
    Proof_T (productTheoryPresentation w) (pairToRight p q r n)
      (definednessTag r n) := by
  apply proof_T_mp _ hp
  rw [← pairToRightAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [pairToRightAxiomCode, decodeFormula_encodeFormula]
  exact pairToRightAxiom_holds w q r n

theorem proof_T_componentsToPair
    (w : ℕ → ℕ → Bool) {p h q r n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p (definednessTag q n))
    (hh : Proof_T (productTheoryPresentation w) h (definednessTag r n)) :
    Proof_T (productTheoryPresentation w) (componentsToPair p h q r n)
      (definednessTag (pairIndex q r) n) := by
  apply proof_T_mp _ hh
  apply proof_T_mp _ hp
  rw [← componentsToPairAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [componentsToPairAxiomCode, decodeFormula_encodeFormula]
  exact componentsToPairAxiom_holds w q r n

abbrev UnaryProductMapArgs := (((ℕ × ℕ) × ℕ) × ℕ)
abbrev BinaryProductMapArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

def project0ToPairPacked (z : UnaryProductMapArgs) : ProofSequenceCode :=
  project0ToPair z.1.1.1 z.1.1.2 z.1.2 z.2

def project1ToPairPacked (z : UnaryProductMapArgs) : ProofSequenceCode :=
  project1ToPair z.1.1.1 z.1.1.2 z.1.2 z.2

def pairToLeftPacked (z : UnaryProductMapArgs) : ProofSequenceCode :=
  pairToLeft z.1.1.1 z.1.1.2 z.1.2 z.2

def pairToRightPacked (z : UnaryProductMapArgs) : ProofSequenceCode :=
  pairToRight z.1.1.1 z.1.1.2 z.1.2 z.2

def componentsToPairPacked (z : BinaryProductMapArgs) : ProofSequenceCode :=
  componentsToPair z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

private theorem primrec_unaryProductMapComponents :
    let p : UnaryProductMapArgs → ℕ := fun z => z.1.1.1
    let q : UnaryProductMapArgs → ℕ := fun z => z.1.1.2
    let r : UnaryProductMapArgs → ℕ := fun z => z.1.2
    let n : UnaryProductMapArgs → ℕ := fun z => z.2
    Primrec p ∧ Primrec q ∧ Primrec r ∧ Primrec n := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

private theorem primrec_binaryProductMapComponents :
    let p : BinaryProductMapArgs → ℕ := fun z => z.1.1.1.1
    let h : BinaryProductMapArgs → ℕ := fun z => z.1.1.1.2
    let q : BinaryProductMapArgs → ℕ := fun z => z.1.1.2
    let r : BinaryProductMapArgs → ℕ := fun z => z.1.2
    let n : BinaryProductMapArgs → ℕ := fun z => z.2
    Primrec p ∧ Primrec h ∧ Primrec q ∧ Primrec r ∧ Primrec n := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

private theorem primrec_unaryMapOfSchema
    (schema : ProductSchemaArgs → FormulaCode)
    (hschema : Primrec schema) :
    Primrec (fun z : UnaryProductMapArgs =>
      mp (oneLineProofCode (schema ((z.1.1.2, z.1.2), z.2)))
        z.1.1.1) := by
  obtain ⟨hp, hq, hr, hn⟩ := primrec_unaryProductMapComponents
  have hargs : Primrec (fun z : UnaryProductMapArgs =>
      ((z.1.1.2, z.1.2), z.2)) := (hq.pair hr).pair hn
  exact primrec_mp.comp (primrec_oneLineProofCode.comp (hschema.comp hargs)) hp

theorem primrec_project0ToPair : Primrec project0ToPairPacked :=
  (primrec_unaryMapOfSchema
    (fun z => project0ToPairAxiomCode z.1.1 z.1.2 z.2)
    primrec_project0ToPairAxiomCode).of_eq (fun _ => rfl)

theorem primrec_project1ToPair : Primrec project1ToPairPacked :=
  (primrec_unaryMapOfSchema
    (fun z => project1ToPairAxiomCode z.1.1 z.1.2 z.2)
    primrec_project1ToPairAxiomCode).of_eq (fun _ => rfl)

theorem primrec_pairToLeft : Primrec pairToLeftPacked :=
  (primrec_unaryMapOfSchema
    (fun z => pairToLeftAxiomCode z.1.1 z.1.2 z.2)
    primrec_pairToLeftAxiomCode).of_eq (fun _ => rfl)

theorem primrec_pairToRight : Primrec pairToRightPacked :=
  (primrec_unaryMapOfSchema
    (fun z => pairToRightAxiomCode z.1.1 z.1.2 z.2)
    primrec_pairToRightAxiomCode).of_eq (fun _ => rfl)

theorem primrec_componentsToPair : Primrec componentsToPairPacked := by
  obtain ⟨hp, hh, hq, hr, hn⟩ := primrec_binaryProductMapComponents
  have hargs : Primrec (fun z : BinaryProductMapArgs =>
      ((z.1.1.2, z.1.2), z.2)) := (hq.pair hr).pair hn
  have hax := primrec_componentsToPairAxiomCode.comp hargs
  exact (primrec_mp.comp
    (primrec_mp.comp (primrec_oneLineProofCode.comp hax) hp) hh).of_eq
      (fun _ => rfl)

end FailureOfComposition.NumericalProductProofs
