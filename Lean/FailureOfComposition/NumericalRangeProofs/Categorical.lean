/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalRangeProofs.Structural.Preservation
import FailureOfComposition.TypedRanges

/-!
# The range proof map at typed representatives

For a raw typed index `q : Q -> R`, the proof map uses the supported
representative `normalizeIndex Q R q`.  Its fixed range index is exactly
`typedRangeIndex Q R q`, the representative installed as the categorical
range.  Primitive recursiveness is asserted only after these two external
indices have been fixed.  The effective selector from `q` to a range index
required by the manuscript's uniform B1 statement is not proved here and
remains a separate obligation.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Metamath.Feferman
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalRangeProofs

open CodedObjectMembership ConcreteEvaluator NumericalProofBridge ProofSearch
open TypedProgramCategory TypedRanges

noncomputable section

/-! ## Fixed typed proof maps -/

abbrev TypedRangeProofArgs := ((ℕ × ℕ) × ℕ)

/-- The numerical range proof for the supported representative of `q`.
Inputs are the supplied evaluator stage, source value, and output value. -/
noncomputable def typedRangeProof
    (Q R : STObjectCode) (q s u i : ℕ) : ProofSequenceCode :=
  rangeProof (normalizeIndex Q R q) (typedRangeIndex Q R q) s u i

noncomputable def typedRangeProofPacked
    (Q R : STObjectCode) (q : ℕ)
    (z : TypedRangeProofArgs) : ProofSequenceCode :=
  typedRangeProof Q R q z.1.1 z.1.2 z.2

/-- Once `Q`, `R`, and `q` are fixed externally, the map on supplied
computation data is primitive recursive.  This conclusion treats the selected
range index as a constant and therefore does not compute that index from `q`;
it is not the uniform range-representative constructor required by B1. -/
theorem primrec_typedRangeProof (Q R : STObjectCode) (q : ℕ) :
    Primrec (typedRangeProofPacked Q R q) := by
  have hs : Primrec (fun z : TypedRangeProofArgs => z.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hu : Primrec (fun z : TypedRangeProofArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun z : TypedRangeProofArgs => z.2) := Primrec.snd
  have hargs : Primrec (fun z : TypedRangeProofArgs =>
      ((((normalizeIndex Q R q, typedRangeIndex Q R q), z.1.1), z.1.2),
        z.2)) :=
    ((((Primrec.const (normalizeIndex Q R q)).pair
      (Primrec.const (typedRangeIndex Q R q))).pair hs).pair hu).pair hi
  exact (primrec_rangeProof.comp hargs).of_eq (fun _ => rfl)

/-- The exact selected-checker endpoint produced from a supplied computation
of the supported normalized representative. -/
theorem typedRangeProof_correct
    (Q R : STObjectCode) (q : ℕ) {s u i : ℕ}
    (hs : stageComputation s (normalizeIndex Q R q) u i) :
    Proof_T
      (paRangeTheoryPresentation (normalizeIndex Q R q)
        (typedRangeIndex Q R q))
      (typedRangeProof Q R q s u i)
      (rightInstanceCode (typedRangeIndex Q R q) i i) :=
  paRangeProof_correct hs

/-- The fixed PA graph law for the selected typed range turns the checked
proof into the exact PA range-fixpoint theorem. -/
theorem PA_proves_typedRangeFixpoint_of_stageComputation
    (Q R : STObjectCode) (q : ℕ) {s u i : ℕ}
    (hs : stageComputation s (normalizeIndex Q R q) u i) :
    𝗣𝗔 ⊢ (eventualGraph (typedRangeIndex Q R q)).val/[i, i] :=
  PA_proves_rangeFixpoint_of_stageComputation
    (typedRangeIndex_uniform Q R q) hs

/-- Every arithmetic extension of PA inherits the produced range-fixpoint
theorem.  Recursive enumerability is unnecessary for this semantic
consequence. -/
theorem theory_proves_typedRangeFixpoint_of_stageComputation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) {s u i : ℕ}
    (hs : stageComputation s (normalizeIndex Q R q) u i) :
    T ⊢ (eventualGraph (typedRangeIndex Q R q)).val/[i, i] :=
  WeakerThan.pbl
    (PA_proves_typedRangeFixpoint_of_stageComputation Q R q hs)

/-! ## Normalization and the categorical range -/

/-- A supplied computation of the normalized representative contains the
source and target membership required by typing.  It also gives a computation
of the raw index semantically; no raw computation code is substituted for the
normalized computation code. -/
theorem normalized_stageComputation_support
    (Q R : STObjectCode) (q : ℕ) {s u i : ℕ}
    (hs : stageComputation s (normalizeIndex Q R q) u i) :
    STObjectCode.member Q u = true ∧
      (eventualGraph q).val.Evalb ![u, i] ∧
      STObjectCode.member R i = true := by
  have hgraph :
      (eventualGraph (normalizeIndex Q R q)).val.Evalb ![u, i] := by
    rw [eventualGraph_eval]
    exact ⟨s, by simpa [stageComputation] using hs⟩
  obtain ⟨hQ, hq, hR⟩ :=
    (eventualGraph_normalizeIndex_eval Q R q u i).mp hgraph
  exact ⟨(memberFormula_nat_iff Q u).mp hQ, hq,
    (memberFormula_nat_iff R i).mp hR⟩

/-- The endpoint program used by `typedRangeProof` is the representative of
the actual categorical range; this is not a second range operation. -/
theorem typedRangeProof_endpoint_is_ran
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    HasRanges.ran (arrowOfIndex T Q R q) =
      arrowOfIndex T R R (typedRangeIndex Q R q) :=
  ran_arrowOfIndex T Q R q

end

end FailureOfComposition.NumericalRangeProofs
