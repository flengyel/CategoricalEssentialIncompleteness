/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProofSearchMembership

/-!
# Stage witnesses required by production equality transport

In the production presentation, a nondiagonal equality tag can be obtained
only through its own theorem-stage witness. The witness occurs in the
proof, so its stage is bounded by the numerical proof code. Consequently,
primitive-recursive equality transport is equivalent to a primitive-recursive
bound on the required stages. This concerns the unchanged production checker.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.ProductionStageClosure

open NumericalProofBridge UniformIndexQuotient ProofSearchMembership

private theorem mem_le_listEncode {xs : List ℕ} {n : ℕ} (h : n ∈ xs) :
    n ≤ listEncode xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      have ha : a ≤ codePair a (listEncode xs) := by
        simpa using codeUnpair_left_le (codePair a (listEncode xs))
      have ht : listEncode xs ≤ codePair a (listEncode xs) := by
        simpa using codeUnpair_right_le (codePair a (listEncode xs))
      rcases List.mem_cons.mp h with rfl | h
      · simp only [listEncode]; omega
      · have := ih h
        simp only [listEncode]; omega

private theorem stage_le_proof {p a s : ℕ}
    (h : stageString a s ∈ decodeProof p) : s ≤ p := by
  have hf : encodeFormula (stageString a s) ≤ p := by
    have hm : encodeFormula (stageString a s) ∈ (decodeProof p).map encodeFormula :=
      List.mem_map.mpr ⟨stageString a s, h, rfl⟩
    have := mem_le_listEncode hm
    change encodeFormula (stageString a s) ≤ encodeProof (decodeProof p) at this
    simpa only [encodeProof_decodeProof] using this
  have hs : s ≤ encodeFormula (stageString a s) :=
    mem_le_listEncode (by simp [stageString])
  exact hs.trans hf

private def atom (w : ℕ → ℕ → Bool) (b : ℕ) : FormulaString → Prop
  | [tag, q, r] =>
      if tag = equalityTag then q = r ∨ ∃ s ≤ b, w (eqSentenceCode q r) s = true
      else if tag = stageTag then ∃ s ≤ b, w q s = true
      else True
  | _ => True

private def holds (w : ℕ → ℕ → Bool) (b : ℕ) (s : FormulaString) : Prop :=
  if _h : s = impString (lhsString s) (rhsString s) then
    holds w b (lhsString s) → holds w b (rhsString s)
  else atom w b s
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

@[simp] private theorem holds_imp (w : ℕ → ℕ → Bool) (b : ℕ)
    (a c : FormulaString) :
    holds w b (impString a c) ↔ (holds w b a → holds w b c) := by
  rw [holds]
  simp

@[simp] private theorem holds_equality (w : ℕ → ℕ → Bool) (b q r : ℕ) :
    holds w b (equalityString q r) ↔
      q = r ∨ ∃ s ≤ b, w (eqSentenceCode q r) s = true := by
  rw [holds]
  simp [equalityString, atom, equalityTag, impTag, impString, lhsString, rhsString]

@[simp] private theorem holds_stage (w : ℕ → ℕ → Bool) (b a s : ℕ) :
    holds w b (stageString a s) ↔ ∃ t ≤ b, w a t = true := by
  rw [holds]
  simp [stageString, atom, equalityTag, stageTag, impTag, impString, lhsString, rhsString]

@[simp] private theorem holds_left (w : ℕ → ℕ → Bool) (b q n m : ℕ) :
    holds w b (leftInstanceString q n m) := by
  rw [holds]
  simp [leftInstanceString, atom, leftInstanceTag, impTag, impString, lhsString, rhsString]

@[simp] private theorem holds_right (w : ℕ → ℕ → Bool) (b q n m : ℕ) :
    holds w b (rightInstanceString q n m) := by
  rw [holds]
  simp [rightInstanceString, atom, rightInstanceTag, impTag, impString, lhsString, rhsString]

@[simp] private theorem holds_instance (w : ℕ → ℕ → Bool) (b q r n m : ℕ) :
    holds w b (instanceEqualityString q r n m) := by
  rw [holds]
  simp [instanceEqualityString, atom, instanceEqualityTag, impTag, impString,
    lhsString, rhsString]

private theorem holds_logical (w : ℕ → ℕ → Bool) (b : ℕ) {s : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds s) : holds w b s := by
  change extendedLogicalAxiomTest s = true at h
  rcases (extendedLogicalAxiomTest_eq_true_iff s).mp h with h | h
  · rcases (logicalAxiomShape_iff s).mp h with
      ⟨q, r, n, m, rfl⟩ | ⟨q, r, n, m, rfl⟩ | ⟨q, r, n, m, rfl⟩
    · simp [specializationAxiomString]
    · simp [forwardAxiomString]
    · simp [reverseAxiomString]
  · rcases h with h | h | h
    · rw [h]
      simp only [bridgeEqualityAxiomString, holds_imp, holds_stage, holds_equality]
      exact Or.inr
    · rw [h]
      simp [bridgeLeftAxiomString]
    · rw [h]
      simp [bridgeRightAxiomString]

private theorem holds_lines (w : ℕ → ℕ → Bool) (p : ℕ)
    (hj : ∀ i, i < (decodeProof p).length →
      LineJustified (extendedTheoryPresentation w) (decodeProof p) i)
    (i : ℕ) (hi : i < (decodeProof p).length) :
    holds w p ((decodeProof p).getD i []) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      obtain ⟨_, _, hlog | hax | hmp⟩ := hj i hi
      · exact holds_logical w p hlog
      · change axiomTest w ((decodeProof p).getD i []) = true at hax
        rcases (axiomShape_iff w _).mp ((axiomTest_eq_true_iff w _).mp hax) with
          ⟨a, s, hs, heq⟩ | ⟨q, heq⟩
        · have hm : stageString a s ∈ decodeProof p := by
            rw [← heq]
            simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
              Option.getD_some] using List.getElem_mem hi
          rw [heq, holds_stage]
          exact ⟨s, stage_le_proof hm, hs⟩
        · rw [heq, holds_equality]
          exact Or.inl rfl
      · obtain ⟨j, hji, k, hki, hk⟩ := hmp
        have hk' := ih k hki (by omega)
        rw [hk, holds_imp] at hk'
        exact hk' (ih j hji (by omega))

/-- Every nondiagonal production equality proof contains a stage witness
for that exact equality sentence, with stage at most the proof code. -/
theorem proof_T_equality_stage_bound (w : ℕ → ℕ → Bool) {p q r : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p (equalityCode q r)) :
    q = r ∨ ∃ s ≤ p, w (eqSentenceCode q r) s = true := by
  obtain ⟨hne, hlast, hj⟩ := hp
  have hi : (decodeProof p).length - 1 < (decodeProof p).length := by
    have := List.length_pos_of_ne_nil hne
    omega
  have h := holds_lines w p hj _ hi
  have hget : (decodeProof p).getD ((decodeProof p).length - 1) [] =
      (decodeProof p).getLastD [] := by
    rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  rw [hget, hlast] at h
  simpa only [equalityCode, decodeFormula_encodeFormula, holds_equality] using h

/-- A bound for the new stage, jointly in the two proof codes and the three
indices. The diagonal output requires no stage witness. -/
def StageTransportBoundCorrect (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (bound : PrfEqTransportArgs → ℕ) : Prop :=
  ∀ e p y y' d : ℕ, PrfEq T hRE e y y' → PrfEq T hRE p y d →
    y' = d ∨ ∃ s ≤ bound ((((e, p), y), y'), d),
      reTheoryStageWitness T hRE (eqSentenceCode y' d) s = true

def HasPrimitiveRecursiveStageTransportBound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) : Prop :=
  ∃ bound : PrfEqTransportArgs → ℕ, Primrec bound ∧ StageTransportBoundCorrect T hRE bound

/-- A production transport function itself bounds the required theorem stages. -/
theorem transport_implies_stage_bound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {transport : PrfEqTransportArgs → ℕ} (h : PrfEqTransportCorrect T hRE transport) :
    StageTransportBoundCorrect T hRE transport := by
  intro e p y y' d he hp
  exact proof_T_equality_stage_bound _ (h e p y y' d he hp)

/-- A total bounded search. If no stage succeeds, the result is zero. -/
def findStage (w : ℕ → ℕ → Bool) (a b : ℕ) : ℕ :=
  (List.range (b + 1)).foldr (fun s r => if w a s then s else r) 0

private theorem foldr_stage {w : ℕ → ℕ → Bool} {a : ℕ} (xs : List ℕ)
    (h : ∃ s ∈ xs, w a s = true) :
    w a (xs.foldr (fun s r => if w a s then s else r) 0) = true := by
  induction xs with
  | nil => simp at h
  | cons s xs ih =>
      by_cases hs : w a s = true
      · simp [hs]
      · have ht : ∃ t ∈ xs, w a t = true := by
          obtain ⟨t, ht, hw⟩ := h
          rcases List.mem_cons.mp ht with rfl | ht
          · exact (hs hw).elim
          · exact ⟨t, ht, hw⟩
        simpa [hs] using ih ht

theorem findStage_spec {w : ℕ → ℕ → Bool} {a b : ℕ}
    (h : ∃ s ≤ b, w a s = true) : w a (findStage w a b) = true := by
  apply foldr_stage
  obtain ⟨s, hs, hw⟩ := h
  exact ⟨s, List.mem_range.mpr (by omega), hw⟩

theorem primrec_findStage (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) : Primrec₂ (findStage w) := by
  have hl : Primrec (fun z : ℕ × ℕ => List.range (z.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  have ha : Primrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.list_foldr hl (Primrec.const 0)
    (Primrec.cond (hw.comp (ha.pair hs)) hs hr).to₂).of_eq (fun _ => by
      simp only [findStage, Bool.cond_eq_ite])

/-- Build an equality proof from a supplied stage bound. On inputs without
such a stage the definition remains total, without claiming proof acceptance. -/
def transportWithBound (w : ℕ → ℕ → Bool) (bound : PrfEqTransportArgs → ℕ)
    (z : PrfEqTransportArgs) : ℕ :=
  let y' := z.1.2
  let d := z.2
  if y' = d then oneLineProofCode (equalityCode y' d) else
    let s := findStage w (eqSentenceCode y' d) (bound z)
    bridgeEquality (oneLineProofCode (stageCode (eqSentenceCode y' d) s)) s y' d

theorem primrec_transportWithBound (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (bound : PrfEqTransportArgs → ℕ) (hb : Primrec bound) :
    Primrec (transportWithBound w bound) := by
  have hy : Primrec (fun z : PrfEqTransportArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun z : PrfEqTransportArgs => z.2) := Primrec.snd
  have hc := primrec₂_eqSentenceCode.comp hy hd
  have hs := (primrec_findStage w hw).comp hc hb
  have hp := primrec_oneLineProofCode.comp (primrec₂_stageCode.comp hc hs)
  have ho := primrec_bridgeEquality.comp (((hp.pair hs).pair hy).pair hd)
  exact (Primrec.ite (Primrec.eq.comp hy hd)
    (primrec_oneLineProofCode.comp (primrec₂_equalityCode.comp hy hd)) ho).of_eq
      (fun _ => rfl)

theorem transportWithBound_correct (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {bound : PrfEqTransportArgs → ℕ} (hb : StageTransportBoundCorrect T hRE bound) :
    PrfEqTransportCorrect T hRE (transportWithBound (reTheoryStageWitness T hRE) bound) := by
  intro e p y y' d he hp
  change Proof_T (extendedTheoryPresentation (reTheoryStageWitness T hRE)) _ _
  by_cases hd : y' = d
  · subst d
    simp only [transportWithBound, ite_true]
    apply proof_T_oneLine_of_axiom
    simpa only [equalityCode, decodeFormula_encodeFormula,
      specializationTheoryPresentation, extendedTheoryPresentation] using
      diagonalEqualityAxiom_holds (reTheoryStageWitness T hRE) y'
  · obtain hdiag | hs := hb e p y y' d he hp
    · exact (hd hdiag).elim
    · simp only [transportWithBound, hd, ite_false]
      apply proof_T_bridgeEquality
      apply proof_T_oneLine_of_axiom
      rw [stageCode, decodeFormula_encodeFormula]
      exact stageAxiom_holds (reTheoryStageWitness T hRE) _ _ (findStage_spec hs)

/-- Exact characterization of the numerical production transport target.
Extensional enumeration supplies stages existentially; this equivalence
requires a single primitive-recursive bound in all five varying arguments. -/
theorem has_transport_iff_stage_bound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    HasPrimitiveRecursivePrfEqTransport T hRE ↔
      HasPrimitiveRecursiveStageTransportBound T hRE := by
  constructor
  · rintro ⟨transport, hpr, hcorrect⟩
    exact ⟨transport, hpr, transport_implies_stage_bound T hRE hcorrect⟩
  · rintro ⟨bound, hpr, hcorrect⟩
    exact ⟨transportWithBound (reTheoryStageWitness T hRE) bound,
      primrec_transportWithBound _ (primrec_reTheoryStageWitness T hRE) bound hpr,
      transportWithBound_correct T hRE hcorrect⟩

/-- Failure of a joint primitive-recursive stage bound obstructs production
transport, even when the corresponding equality proof exists for every input. -/
theorem no_transport_of_no_stage_bound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (h : ¬HasPrimitiveRecursiveStageTransportBound T hRE) :
    ¬HasPrimitiveRecursivePrfEqTransport T hRE :=
  fun ht => h ((has_transport_iff_stage_bound T hRE).mp ht)

end FailureOfComposition.ProductionStageClosure
