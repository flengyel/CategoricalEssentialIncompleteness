/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Arith.Feferman.Specialization
public import FailureOfComposition.FirstSuccessGraph
public import FailureOfComposition.TheoryEnumerability
public import Foundation.FirstOrder.Incompleteness.Definability
public import Foundation.FirstOrder.Incompleteness.Halting

/-!
# Numerical specialization for the first-success comparison

This module instantiates the structural specialization calculus with a
primitive-recursive stage enumeration of PA theorems.  Formula strings are
given an explicit arithmetic meaning.  Under that meaning, the three logical
axiom schemes are PA theorems, stage axioms denote the theorem enumerated at
their stage, and the diagonal equality axioms denote the established
first-success/eventual-graph comparisons.

The resulting correspondence is deliberately stated for the structural
`Metamath.Feferman.Proof_T` represented by
`Arith.Feferman.Specialization.specializationProofGraph`.  It does not use the
separately selected `Arith.Feferman.proofTFormula`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalSpecialization

open ProofSearch ConcreteEvaluator

/-! ## A primitive-recursive stage enumeration of PA theorems -/

/-- Every recursively enumerable predicate has a total Boolean stage test whose
binary uncurrying is primitive recursive.  The construction chooses a code for
a partial semidecision procedure; it makes no uniform computability claim in
the proof of enumerability. -/
theorem exists_primrec_stage_witness
    {A : ℕ → Prop}
    (hA : REPred A) :
    ∃ w : ℕ → ℕ → Bool,
      Primrec (fun z : ℕ × ℕ ↦ w z.1 z.2) ∧
      ∀ n : ℕ, A n ↔ ∃ s : ℕ, w n s = true := by
  obtain ⟨f, hf, Hf⟩ := REPred.iff'.mp hA
  have hg : Partrec (fun n : ℕ ↦ (f n).map fun _ ↦ (0 : ℕ)) :=
    Partrec.map hf (Computable.const 0).to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hg)
  refine ⟨fun n s ↦ (Nat.Partrec.Code.evaln s c n).isSome, ?_, ?_⟩
  · exact Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.snd.pair (Primrec.const c)).pair Primrec.fst))
  · intro n
    constructor
    · intro hn
      have hdom : ((f n).map fun _ ↦ (0 : ℕ)).Dom := by
        simpa using (Hf n).mp hn
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
      have hv' : v ∈ Nat.Partrec.Code.eval c n := by
        rw [hc]
        exact hv
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv'
      exact ⟨s, by simpa using Option.isSome_of_mem hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (by simpa using hs)
      have hv' : v ∈ Nat.Partrec.Code.eval c n :=
        Nat.Partrec.Code.evaln_sound hv
      rw [hc] at hv'
      have hdom : ((f n).map fun _ ↦ (0 : ℕ)).Dom :=
        Part.dom_iff_mem.mpr ⟨v, hv'⟩
      exact (Hf n).mpr (by simpa using hdom)

private def PATheoremCode (n : ℕ) : Prop :=
  (Encodable.decode (α := ArithmeticSentence) n).elim False
    (fun σ ↦ 𝗣𝗔 ⊢ σ)

private theorem rePred_PATheoremCode : REPred PATheoremCode :=
  REPred.iff_decoded_pred.mp (sentence_provability_re_of_delta1 𝗣𝗔)

/-- A fixed primitive-recursive finite-stage test enumerating exactly the
codes of PA theorems.  The stage is a certificate, not a proof-code selector. -/
@[no_expose] noncomputable def paStageWitness : ℕ → ℕ → Bool :=
  Classical.choose (exists_primrec_stage_witness rePred_PATheoremCode)

theorem primrec_paStageWitness :
    Primrec (fun z : ℕ × ℕ ↦ paStageWitness z.1 z.2) :=
  (Classical.choose_spec
    (exists_primrec_stage_witness rePred_PATheoremCode)).1

theorem PA_provable_iff_exists_stage (σ : ArithmeticSentence) :
    𝗣𝗔 ⊢ σ ↔ ∃ s : ℕ, paStageWitness (Encodable.encode σ) s = true := by
  have h := (Classical.choose_spec
    (exists_primrec_stage_witness rePred_PATheoremCode)).2
    (Encodable.encode σ)
  simpa [PATheoremCode, paStageWitness] using h

/-! ## Arithmetic meaning of the tagged formula strings -/

/-- Total decoding of a sentence code.  A malformed code denotes truth; all
stage axioms used below carry an actual `Encodable.encode` code. -/
noncomputable def decodedSentence (a : ℕ) : ArithmeticSentence :=
  (Encodable.decode (α := ArithmeticSentence) a).getD ⊤

@[simp] theorem decodedSentence_encode (σ : ArithmeticSentence) :
    decodedSentence (Encodable.encode σ) = σ := by
  simp [decodedSentence]

/-- Meaning of a non-implication tagged string for two fixed graph families. -/
noncomputable def atomicMeaning (F G : ℕ → Graph) :
    FormulaString → ArithmeticSentence
  | [tag, q, r] =>
      if tag = equalityTag then uniformSentence (F q) (G r)
      else if tag = stageTag then decodedSentence q
      else ⊤
  | [tag, q, n, m] =>
      if tag = leftInstanceTag then (F q).val/[n, m]
      else if tag = rightInstanceTag then (G q).val/[n, m]
      else ⊤
  | [tag, q, r, n, m] =>
      if tag = instanceEqualityTag then
        (F q).val/[n, m] 🡘 (G r).val/[n, m]
      else ⊤
  | _ => ⊤

/-- Compositional meaning of every candidate formula string.  The guard is
the exact self-delimiting implication parse; otherwise the tagged atomic
meaning is used. -/
noncomputable def formulaMeaning (F G : ℕ → Graph)
    (s : FormulaString) : ArithmeticSentence :=
  if _h : s = impString (lhsString s) (rhsString s) then
    formulaMeaning F G (lhsString s) 🡒
      formulaMeaning F G (rhsString s)
  else atomicMeaning F G s
termination_by s.length
decreasing_by
  · rw [_h]
    simp only [lhsString_impString]
    simp [impString]
    omega
  · rw [_h]
    simp only [rhsString_impString]
    simp [impString]
    omega

@[simp] theorem formulaMeaning_impString (F G : ℕ → Graph)
    (a b : FormulaString) :
    formulaMeaning F G (impString a b) =
      (formulaMeaning F G a 🡒 formulaMeaning F G b) := by
  rw [formulaMeaning]
  simp

@[simp] theorem formulaMeaning_equalityString (F G : ℕ → Graph) (q r : ℕ) :
    formulaMeaning F G (equalityString q r) =
      uniformSentence (F q) (G r) := by
  rw [formulaMeaning]
  simp [equalityString, atomicMeaning, equalityTag, impTag, impString,
    lhsString, rhsString]

@[simp] theorem formulaMeaning_leftInstanceString
    (F G : ℕ → Graph) (q n m : ℕ) :
    formulaMeaning F G (leftInstanceString q n m) = (F q).val/[n, m] := by
  rw [formulaMeaning]
  simp [leftInstanceString, atomicMeaning, leftInstanceTag,
    impTag, impString, lhsString, rhsString]

@[simp] theorem formulaMeaning_rightInstanceString
    (F G : ℕ → Graph) (r n m : ℕ) :
    formulaMeaning F G (rightInstanceString r n m) = (G r).val/[n, m] := by
  rw [formulaMeaning]
  simp [rightInstanceString, atomicMeaning, leftInstanceTag, rightInstanceTag,
    impTag, impString, lhsString, rhsString]

@[simp] theorem formulaMeaning_instanceEqualityString
    (F G : ℕ → Graph) (q r n m : ℕ) :
    formulaMeaning F G (instanceEqualityString q r n m) =
      ((F q).val/[n, m] 🡘 (G r).val/[n, m]) := by
  rw [formulaMeaning]
  simp [instanceEqualityString, atomicMeaning, instanceEqualityTag,
    impTag, impString, lhsString, rhsString]

@[simp] theorem formulaMeaning_stageString
    (F G : ℕ → Graph) (a s : ℕ) :
    formulaMeaning F G (stageString a s) = decodedSentence a := by
  rw [formulaMeaning]
  simp [stageString, atomicMeaning, equalityTag, stageTag, impTag, impString,
    lhsString, rhsString]

/-! ## Soundness of the three specialization schemas -/

theorem provable_PA_meaning_specializationAxiom
    (F G : ℕ → Graph) (q r n m : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning F G (specializationAxiomString q r n m) := by
  simp only [specializationAxiomString, formulaMeaning_impString,
    formulaMeaning_equalityString, formulaMeaning_instanceEqualityString]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  suffices
      (∀ x y : V,
        (F q).val.Evalb ![x, y] ↔ (G r).val.Evalb ![x, y]) →
      ((F q).val.Evalb ![(n : V), (m : V)] ↔
        (G r).val.Evalb ![(n : V), (m : V)]) by
    simpa [models_iff, uniformSentence_eval, Semiformula.eval_substs,
      numeral_eq_natCast]
  intro h
  exact h _ _

theorem provable_PA_meaning_forwardAxiom
    (F G : ℕ → Graph) (q r n m : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning F G (forwardAxiomString q r n m) := by
  simp only [forwardAxiomString, formulaMeaning_impString,
    formulaMeaning_instanceEqualityString, formulaMeaning_leftInstanceString,
    formulaMeaning_rightInstanceString]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  suffices
      ((F q).val.Evalb ![(n : V), (m : V)] ↔
        (G r).val.Evalb ![(n : V), (m : V)]) →
      (F q).val.Evalb ![(n : V), (m : V)] →
      (G r).val.Evalb ![(n : V), (m : V)] by
    simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast]
  intro hiff hleft
  exact hiff.mp hleft

theorem provable_PA_meaning_reverseAxiom
    (F G : ℕ → Graph) (q r n m : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning F G (reverseAxiomString q r n m) := by
  simp only [reverseAxiomString, formulaMeaning_impString,
    formulaMeaning_instanceEqualityString, formulaMeaning_leftInstanceString,
    formulaMeaning_rightInstanceString]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  suffices
      ((F q).val.Evalb ![(n : V), (m : V)] ↔
        (G r).val.Evalb ![(n : V), (m : V)]) →
      (G r).val.Evalb ![(n : V), (m : V)] →
      (F q).val.Evalb ![(n : V), (m : V)] by
    simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast]
  intro hiff hright
  exact hiff.mpr hright

/-! ## Soundness and exact correspondence for the chosen presentation -/

theorem logicalAxiom_meaning_provable
    (F G : ℕ → Graph) (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (specializationTheoryPresentation w).syn.logicalAxiom.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning F G s := by
  change logicalAxiomTest s = true at h
  rw [logicalAxiomTest_eq_true_iff, logicalAxiomShape_iff] at h
  rcases h with ⟨q, r, n, m, rfl⟩ | ⟨q, r, n, m, rfl⟩ |
      ⟨q, r, n, m, rfl⟩
  · exact provable_PA_meaning_specializationAxiom F G q r n m
  · exact provable_PA_meaning_forwardAxiom F G q r n m
  · exact provable_PA_meaning_reverseAxiom F G q r n m

theorem theoryAxiom_meaning_provable
    (F G : ℕ → Graph) (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    (hdiagonal : ∀ q : ℕ, Uniform 𝗣𝗔 (F q) (G q))
    {s : FormulaString}
    (h : (specializationTheoryPresentation w).ax.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning F G s := by
  change axiomTest w s = true at h
  rw [axiomTest_eq_true_iff, axiomShape_iff] at h
  rcases h with ⟨a, k, hw, rfl⟩ | ⟨q, rfl⟩
  · simpa using hstage a k hw
  · rw [formulaMeaning_equalityString]
    exact hdiagonal q

private theorem getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

/-- Strong induction over the numerical presentation's proof lines.  Every
line denotes a PA theorem under `formulaMeaning`. -/
theorem proofLines_meaning_provable
    (F G : ℕ → Graph) (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    (hdiagonal : ∀ q : ℕ, Uniform 𝗣𝗔 (F q) (G q))
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (specializationTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning F G (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact logicalAxiom_meaning_provable F G w hlog
    · exact theoryAxiom_meaning_provable F G w hstage hdiagonal hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem isProofList_meaning_sound
    (F G : ℕ → Graph) (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    (hdiagonal : ∀ q : ℕ, Uniform 𝗣𝗔 (F q) (G q))
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (specializationTheoryPresentation w) Ψ s) :
    𝗣𝗔 ⊢ formulaMeaning F G s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := proofLines_meaning_provable F G w hstage hdiagonal hj
    (Ψ.length - 1) hidx
  rw [getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem proof_T_meaning_sound
    (F G : ℕ → Graph) (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    (hdiagonal : ∀ q : ℕ, Uniform 𝗣𝗔 (F q) (G q))
    {p a : ℕ}
    (hp : Proof_T (specializationTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning F G (decodeFormula a) :=
  isProofList_meaning_sound F G w hstage hdiagonal hp

/-- The production first-success and eventual graph families used by the
concrete B1(1) consumer. -/
def firstSuccessFamily (q : ℕ) : Graph := firstSuccessGraph q

def eventualFamily (q : ℕ) : Graph := eventualGraph q

theorem firstSuccess_eventual_diagonal (q : ℕ) :
    Uniform 𝗣𝗔 (firstSuccessFamily q) (eventualFamily q) := by
  exact firstSuccessGraph_uniform_eventualGraph q

/-- The chosen Feferman presentation for the numerical B1(1) application. -/
noncomputable def paSpecializationTheoryPresentation : TheoryPresentation :=
  specializationTheoryPresentation paStageWitness

noncomputable def paSpecializationPRTheoryPresentation : PRTheoryPresentation :=
  specializationPRTheoryPresentation paStageWitness primrec_paStageWitness

noncomputable def paSpecializationProofGraph : 𝚺₁.Semisentence 2 :=
  specializationProofGraph paStageWitness primrec_paStageWitness

theorem paSpecializationProofGraph_nat_iff (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a] paSpecializationProofGraph.val ↔
      Proof_T paSpecializationTheoryPresentation p a := by
  exact specializationProofGraph_nat_iff
    paStageWitness primrec_paStageWitness p a

theorem paStageWitness_sound (a k : ℕ)
    (h : paStageWitness a k = true) :
    𝗣𝗔 ⊢ decodedSentence a := by
  have hcode : PATheoremCode a :=
    (Classical.choose_spec
      (exists_primrec_stage_witness rePred_PATheoremCode)).2 a |>.mpr ⟨k, h⟩
  cases hd : Encodable.decode (α := ArithmeticSentence) a with
  | none => simp [PATheoremCode, hd] at hcode
  | some σ => simpa [PATheoremCode, decodedSentence, hd] using hcode

theorem paSpecializationProof_T_meaning_sound {p a : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily (decodeFormula a) := by
  exact proof_T_meaning_sound firstSuccessFamily eventualFamily paStageWitness
    paStageWitness_sound firstSuccess_eventual_diagonal hp

theorem PA_provable_to_exists_stage_proof_T (σ : ArithmeticSentence)
    (hσ : 𝗣𝗔 ⊢ σ) :
    ∃ s p : ℕ,
      Proof_T paSpecializationTheoryPresentation p
        (stageCode (Encodable.encode σ) s) := by
  obtain ⟨s, hs⟩ := (PA_provable_iff_exists_stage σ).mp hσ
  refine ⟨s, oneLineProofCode (stageCode (Encodable.encode σ) s), ?_⟩
  apply proof_T_oneLine_of_axiom
  rw [stageCode, decodeFormula_encodeFormula]
  exact stageAxiom_holds paStageWitness (Encodable.encode σ) s hs

theorem proof_T_stageCode_sound
    (σ : ArithmeticSentence) (s p : ℕ)
    (hp : Proof_T paSpecializationTheoryPresentation p
      (stageCode (Encodable.encode σ) s)) :
    𝗣𝗔 ⊢ σ := by
  have h := paSpecializationProof_T_meaning_sound hp
  simpa [stageCode] using h

/-- Exact external correspondence between PA derivability and stage-tagged
proofs in the chosen numerical presentation. -/
theorem PA_provable_iff_exists_stage_proof_T (σ : ArithmeticSentence) :
    𝗣𝗔 ⊢ σ ↔
      ∃ s p : ℕ,
        Proof_T paSpecializationTheoryPresentation p
          (stageCode (Encodable.encode σ) s) := by
  constructor
  · exact PA_provable_to_exists_stage_proof_T σ
  · rintro ⟨s, p, hp⟩
    exact proof_T_stageCode_sound σ s p hp

/-! ## PA-uniform preservation for the chosen structural proof graph -/

theorem provable_PA_paSpecializationPreservation :
    𝗣𝗔 ⊢ uniformSpecializationPreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformSpecializationPreservation
    paStageWitness primrec_paStageWitness

theorem provable_PA_paForwardTransferPreservation :
    𝗣𝗔 ⊢ uniformForwardTransferPreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformForwardTransferPreservation
    paStageWitness primrec_paStageWitness

theorem provable_PA_paReverseTransferPreservation :
    𝗣𝗔 ⊢ uniformReverseTransferPreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformReverseTransferPreservation
    paStageWitness primrec_paStageWitness

/-! ## Fixed-index first-success/eventual application -/

/-- An explicit proof code for the diagonal equality axiom at `q`.  Its
soundness is not postulated: `firstSuccess_eventual_diagonal` proves its
arithmetic meaning in PA. -/
def firstSuccessEventualEqualityProofCode (q : ℕ) : ProofSequenceCode :=
  oneLineProofCode (equalityCode q q)

theorem primrec_firstSuccessEventualEqualityProofCode :
    Primrec firstSuccessEventualEqualityProofCode :=
  primrec_oneLineProofCode.comp
    (primrec₂_equalityCode.comp Primrec.id Primrec.id)

theorem proof_T_firstSuccessEventualEqualityProofCode (q : ℕ) :
    Proof_T paSpecializationTheoryPresentation
      (firstSuccessEventualEqualityProofCode q) (equalityCode q q) := by
  apply proof_T_oneLine_of_axiom
  rw [equalityCode, decodeFormula_encodeFormula]
  exact diagonalEqualityAxiom_holds paStageWitness q

theorem proof_T_equalityCode_sound {p q r : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p (equalityCode q r)) :
    𝗣𝗔 ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := paSpecializationProof_T_meaning_sound hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

theorem proof_T_leftInstanceCode_sound {p q n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p
      (leftInstanceCode q n m)) :
    𝗣𝗔 ⊢ (firstSuccessGraph q).val/[n, m] := by
  have h := paSpecializationProof_T_meaning_sound hp
  simpa [leftInstanceCode, firstSuccessFamily] using h

theorem proof_T_rightInstanceCode_sound {p r n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p
      (rightInstanceCode r n m)) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[n, m] := by
  have h := paSpecializationProof_T_meaning_sound hp
  simpa [rightInstanceCode, eventualFamily] using h

theorem proof_T_instanceEqualityCode_sound {p q r n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p
      (instanceEqualityCode q r n m)) :
    𝗣𝗔 ⊢ ((firstSuccessGraph q).val/[n, m] 🡘
      (eventualGraph r).val/[n, m]) := by
  have h := paSpecializationProof_T_meaning_sound hp
  simpa [instanceEqualityCode, firstSuccessFamily, eventualFamily] using h

/-- The existing FFL comparison has a numerical proof in the exact chosen
presentation, through the stage-tagged PA correspondence. -/
theorem firstSuccessGraph_uniform_eventualGraph_has_stage_proof_T (q : ℕ) :
    ∃ s p : ℕ,
      Proof_T paSpecializationTheoryPresentation p
        (stageCode
          (Encodable.encode
            (uniformSentence (firstSuccessGraph q) (eventualGraph q))) s) := by
  exact (PA_provable_iff_exists_stage_proof_T
    (uniformSentence (firstSuccessGraph q) (eventualGraph q))).mp
      (firstSuccessGraph_uniform_eventualGraph q)

/-- Specialization with a supplied proof of the fixed-index graph equality. -/
theorem proof_T_specialize_firstSuccess_eventual_of
    {p q n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p (equalityCode q q)) :
    Proof_T paSpecializationTheoryPresentation
      (specialize p q q n m) (instanceEqualityCode q q n m) :=
  proof_T_specialize paStageWitness hp

/-- The fixed-index specialization using the explicit, sound comparison proof
code. -/
theorem proof_T_specialize_firstSuccess_eventual (q n m : ℕ) :
    Proof_T paSpecializationTheoryPresentation
      (specialize (firstSuccessEventualEqualityProofCode q) q q n m)
      (instanceEqualityCode q q n m) :=
  proof_T_specialize_firstSuccess_eventual_of
    (proof_T_firstSuccessEventualEqualityProofCode q)

theorem proof_T_transfer_firstSuccess_to_eventual_of
    {p h q n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p (equalityCode q q))
    (hh : Proof_T paSpecializationTheoryPresentation h
      (leftInstanceCode q n m)) :
    Proof_T paSpecializationTheoryPresentation
      (transferForward p h q q n m) (rightInstanceCode q n m) :=
  proof_T_transferForward paStageWitness hp hh

theorem proof_T_transfer_eventual_to_firstSuccess_of
    {p h q n m : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p (equalityCode q q))
    (hh : Proof_T paSpecializationTheoryPresentation h
      (rightInstanceCode q n m)) :
    Proof_T paSpecializationTheoryPresentation
      (transferReverse p h q q n m) (leftInstanceCode q n m) :=
  proof_T_transferReverse paStageWitness hp hh

theorem proof_T_transfer_firstSuccess_to_eventual
    {h q n m : ℕ}
    (hh : Proof_T paSpecializationTheoryPresentation h
      (leftInstanceCode q n m)) :
    Proof_T paSpecializationTheoryPresentation
      (transferForward (firstSuccessEventualEqualityProofCode q) h q q n m)
      (rightInstanceCode q n m) :=
  proof_T_transfer_firstSuccess_to_eventual_of
    (proof_T_firstSuccessEventualEqualityProofCode q) hh

theorem proof_T_transfer_eventual_to_firstSuccess
    {h q n m : ℕ}
    (hh : Proof_T paSpecializationTheoryPresentation h
      (rightInstanceCode q n m)) :
    Proof_T paSpecializationTheoryPresentation
      (transferReverse (firstSuccessEventualEqualityProofCode q) h q q n m)
      (leftInstanceCode q n m) :=
  proof_T_transfer_eventual_to_firstSuccess_of
    (proof_T_firstSuccessEventualEqualityProofCode q) hh

theorem transfer_firstSuccess_to_eventual_sound
    {h q n m : ℕ}
    (hh : Proof_T paSpecializationTheoryPresentation h
      (leftInstanceCode q n m)) :
    𝗣𝗔 ⊢ (eventualGraph q).val/[n, m] :=
  proof_T_rightInstanceCode_sound
    (proof_T_transfer_firstSuccess_to_eventual hh)

theorem transfer_eventual_to_firstSuccess_sound
    {h q n m : ℕ}
    (hh : Proof_T paSpecializationTheoryPresentation h
      (rightInstanceCode q n m)) :
    𝗣𝗔 ⊢ (firstSuccessGraph q).val/[n, m] :=
  proof_T_leftInstanceCode_sound
    (proof_T_transfer_eventual_to_firstSuccess hh)

end FailureOfComposition.NumericalSpecialization
