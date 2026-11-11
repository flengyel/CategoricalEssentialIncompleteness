/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Structural

/-!
# Stage-to-tag specialization and transfer
-/

@[expose] public section

set_option autoImplicit false
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural
open Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

/-! ## Composition with specialization and transfer -/

theorem proof_T_extended_specialize
    (w : ℕ → ℕ → Bool) {p q r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (equalityCode q r)) :
    Proof_T (extendedTheoryPresentation w)
      (specialize p q r n m) (instanceEqualityCode q r n m) := by
  apply proof_T_mp _ hp
  rw [← specializationAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [specializationAxiomCode, decodeFormula_encodeFormula]
  exact oldLogicalAxiom_holds_extended w
    (specializationAxiom_holds w q r n m)

theorem proof_T_extended_transferForward
    (w : ℕ → ℕ → Bool) {p h q r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (equalityCode q r))
    (hh : Proof_T (extendedTheoryPresentation w) h
      (leftInstanceCode q n m)) :
    Proof_T (extendedTheoryPresentation w)
      (transferForward p h q r n m) (rightInstanceCode r n m) := by
  apply proof_T_mp _ hh
  apply proof_T_mp _ (proof_T_extended_specialize w hp)
  rw [← forwardAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [forwardAxiomCode, decodeFormula_encodeFormula]
  exact oldLogicalAxiom_holds_extended w
    (forwardAxiom_holds w q r n m)

theorem proof_T_extended_transferReverse
    (w : ℕ → ℕ → Bool) {p h q r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (equalityCode q r))
    (hh : Proof_T (extendedTheoryPresentation w) h
      (rightInstanceCode r n m)) :
    Proof_T (extendedTheoryPresentation w)
      (transferReverse p h q r n m) (leftInstanceCode q n m) := by
  apply proof_T_mp _ hh
  apply proof_T_mp _ (proof_T_extended_specialize w hp)
  rw [← reverseAxiomCode_eq_imp]
  apply proof_T_oneLine_of_logicalAxiom
  rw [reverseAxiomCode, decodeFormula_encodeFormula]
  exact oldLogicalAxiom_holds_extended w
    (reverseAxiom_holds w q r n m)

def transferForwardFromStages
    (p h sEq sLeft q r n m : ℕ) : ProofSequenceCode :=
  transferForward
    (bridgeEquality p sEq q r)
    (bridgeLeft h sLeft q n m) q r n m

def transferReverseFromStages
    (p h sEq sRight q r n m : ℕ) : ProofSequenceCode :=
  transferReverse
    (bridgeEquality p sEq q r)
    (bridgeRight h sRight r n m) q r n m

theorem proof_T_transferForwardFromStages
    (w : ℕ → ℕ → Bool) {p h sEq sLeft q r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (extendedTheoryPresentation w) h
      (stageCode (leftSentenceCode q n m) sLeft)) :
    Proof_T (extendedTheoryPresentation w)
      (transferForwardFromStages p h sEq sLeft q r n m)
      (rightInstanceCode r n m) := by
  apply proof_T_extended_transferForward w
  · exact proof_T_bridgeEquality w hp
  · exact proof_T_bridgeLeft w hh

theorem proof_T_transferReverseFromStages
    (w : ℕ → ℕ → Bool) {p h sEq sRight q r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (extendedTheoryPresentation w) h
      (stageCode (rightSentenceCode r n m) sRight)) :
    Proof_T (extendedTheoryPresentation w)
      (transferReverseFromStages p h sEq sRight q r n m)
      (leftInstanceCode q n m) := by
  apply proof_T_extended_transferReverse w
  · exact proof_T_bridgeEquality w hp
  · exact proof_T_bridgeRight w hh

theorem transferForwardFromStages_sound
    {p h sEq sLeft q r n m : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T paExtendedTheoryPresentation h
      (stageCode (leftSentenceCode q n m) sLeft)) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[n, m] := by
  exact paExtendedProof_T_rightInstanceCode_sound
    (proof_T_transferForwardFromStages paStageWitness hp hh)

theorem transferReverseFromStages_sound
    {p h sEq sRight q r n m : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T paExtendedTheoryPresentation h
      (stageCode (rightSentenceCode r n m) sRight)) :
    𝗣𝗔 ⊢ (firstSuccessGraph q).val/[n, m] := by
  exact paExtendedProof_T_leftInstanceCode_sound
    (proof_T_transferReverseFromStages paStageWitness hp hh)

/-- Packed convention ((p,sEq),(h,sInst),((q,r),(n,m))), arranged as a
product tree. -/
abbrev StageTransferArgs :=
  (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

def transferForwardFromStagesPacked
    (z : StageTransferArgs) : ProofSequenceCode :=
  transferForwardFromStages z.1.1 z.2.1.1 z.1.2 z.2.1.2
    z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2

def transferReverseFromStagesPacked
    (z : StageTransferArgs) : ProofSequenceCode :=
  transferReverseFromStages z.1.1 z.2.1.1 z.1.2 z.2.1.2
    z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2

private theorem primrec_stageTransferComponents :
    let hp : StageTransferArgs → ℕ := fun z => z.1.1
    let hsEq : StageTransferArgs → ℕ := fun z => z.1.2
    let hh : StageTransferArgs → ℕ := fun z => z.2.1.1
    let hsInst : StageTransferArgs → ℕ := fun z => z.2.1.2
    let hq : StageTransferArgs → ℕ := fun z => z.2.2.1.1
    let hr : StageTransferArgs → ℕ := fun z => z.2.2.1.2
    let hn : StageTransferArgs → ℕ := fun z => z.2.2.2.1
    let hm : StageTransferArgs → ℕ := fun z => z.2.2.2.2
    Primrec hp ∧ Primrec hsEq ∧ Primrec hh ∧ Primrec hsInst ∧
      Primrec hq ∧ Primrec hr ∧ Primrec hn ∧ Primrec hm := by
  dsimp
  exact ⟨Primrec.fst.comp Primrec.fst,
    Primrec.snd.comp Primrec.fst,
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd),
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd),
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)),
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)),
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))⟩

theorem primrec_transferForwardFromStages :
    Primrec transferForwardFromStagesPacked := by
  obtain ⟨hp, hsEq, hh, hsInst, hq, hr, hn, hm⟩ :=
    primrec_stageTransferComponents
  have heqArgs : Primrec (fun z : StageTransferArgs =>
      (((z.1.1, z.1.2), z.2.2.1.1), z.2.2.1.2)) :=
    ((hp.pair hsEq).pair hq).pair hr
  have hleftArgs : Primrec (fun z : StageTransferArgs =>
      ((((z.2.1.1, z.2.1.2), z.2.2.1.1), z.2.2.2.1),
        z.2.2.2.2)) :=
    (((hh.pair hsInst).pair hq).pair hn).pair hm
  have heq := primrec_bridgeEquality.comp heqArgs
  have hleft := primrec_bridgeLeft.comp hleftArgs
  have htransferArgs : Primrec (fun z : StageTransferArgs =>
      (((((bridgeEquality z.1.1 z.1.2 z.2.2.1.1 z.2.2.1.2,
        bridgeLeft z.2.1.1 z.2.1.2 z.2.2.1.1
          z.2.2.2.1 z.2.2.2.2), z.2.2.1.1), z.2.2.1.2),
            z.2.2.2.1), z.2.2.2.2)) :=
    ((((heq.pair hleft).pair hq).pair hr).pair hn).pair hm
  exact (primrec_transferForward.comp htransferArgs).of_eq (fun _ => rfl)

theorem primrec_transferReverseFromStages :
    Primrec transferReverseFromStagesPacked := by
  obtain ⟨hp, hsEq, hh, hsInst, hq, hr, hn, hm⟩ :=
    primrec_stageTransferComponents
  have heqArgs : Primrec (fun z : StageTransferArgs =>
      (((z.1.1, z.1.2), z.2.2.1.1), z.2.2.1.2)) :=
    ((hp.pair hsEq).pair hq).pair hr
  have hrightArgs : Primrec (fun z : StageTransferArgs =>
      ((((z.2.1.1, z.2.1.2), z.2.2.1.2), z.2.2.2.1),
        z.2.2.2.2)) :=
    (((hh.pair hsInst).pair hr).pair hn).pair hm
  have heq := primrec_bridgeEquality.comp heqArgs
  have hright := primrec_bridgeRight.comp hrightArgs
  have htransferArgs : Primrec (fun z : StageTransferArgs =>
      (((((bridgeEquality z.1.1 z.1.2 z.2.2.1.1 z.2.2.1.2,
        bridgeRight z.2.1.1 z.2.1.2 z.2.2.1.2
          z.2.2.2.1 z.2.2.2.2), z.2.2.1.1), z.2.2.1.2),
            z.2.2.2.1), z.2.2.2.2)) :=
    ((((heq.pair hright).pair hq).pair hr).pair hn).pair hm
  exact (primrec_transferReverse.comp htransferArgs).of_eq (fun _ => rfl)

theorem extendedLogicalAxiomLeaf_specialization
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V)
      ![specializationAxiomCodeValue q r n m]
      extendedLogicalAxiomLeaf.val :=
  extendedLogicalAxiomLeaf_old _
    (specializationLogicalAxiomLeaf_specialization q r n m)

theorem extendedLogicalAxiomLeaf_forward
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V)
      ![forwardAxiomCodeValue q r n m]
      extendedLogicalAxiomLeaf.val :=
  extendedLogicalAxiomLeaf_old _
    (specializationLogicalAxiomLeaf_forward q r n m)

theorem extendedLogicalAxiomLeaf_reverse
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n m : V) :
    Semiformula.Evalb (M := V)
      ![reverseAxiomCodeValue q r n m]
      extendedLogicalAxiomLeaf.val :=
  extendedLogicalAxiomLeaf_old _
    (specializationLogicalAxiomLeaf_reverse q r n m)

theorem extendedProofGraph_of_specializeGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r n m e i s : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hi : Semiformula.Evalb (M := V) ![i, q, r, n, m]
      instanceEqualityCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (extendedProofGraph w hw).val)
    (hs : Semiformula.Evalb (M := V) ![s, p, q, r, n, m]
      specializeGraph.val) :
    Semiformula.Evalb (M := V) ![s, i]
      (extendedProofGraph w hw).val := by
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hiq := (instanceEqualityCodeGraph_iff i q r n m).mp hi
  have hsq := (specializeGraph_iff s p q r n m).mp hs
  subst e
  subst i
  subst s
  let Th := extendedPRTheoryPresentation w hw
  let c := specializationAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V)
      ![c, equalityCodeValue q r, instanceEqualityCodeValue q r n m]
      impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf).val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_specialization q r n m)
  have hmp : Semiformula.Evalb (M := V)
      ![specializeValue p q r n m, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    p (equalityCodeValue q r) c (instanceEqualityCodeValue q r n m)
    u (specializeValue p q r n m) hp hc hu hmp

theorem extendedProofGraph_of_transferForwardGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p h q r n m e f g t : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (extendedProofGraph w hw).val)
    (hh : Semiformula.Evalb (M := V) ![h, f]
      (extendedProofGraph w hw).val)
    (ht : Semiformula.Evalb (M := V) ![t, p, h, q, r, n, m]
      transferForwardGraph.val) :
    Semiformula.Evalb (M := V) ![t, g]
      (extendedProofGraph w hw).val := by
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hfq := (leftInstanceCodeGraph_iff f q n m).mp hf
  have hgq := (rightInstanceCodeGraph_iff g r n m).mp hg
  have htq := (transferForwardGraph_iff t p h q r n m).mp ht
  subst e
  subst f
  subst g
  subst t
  let Th := extendedPRTheoryPresentation w hw
  let prf := proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf
  let i := instanceEqualityCodeValue (V := V) q r n m
  let f := leftInstanceCodeValue (V := V) q n m
  let g := rightInstanceCodeValue (V := V) r n m
  let c := forwardAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  let s := specializeValue (V := V) p q r n m
  let d := mpValue u s
  have hs : Semiformula.Evalb (M := V) ![s, i] prf.val := by
    exact extendedProofGraph_of_specializeGraph w hw p q r n m
      (equalityCodeValue q r) i s
      ((equalityCodeGraph_iff _ _ _).mpr rfl)
      ((instanceEqualityCodeGraph_iff _ _ _ _ _).mpr rfl) hp
      ((specializeGraph_iff _ _ _ _ _ _).mpr rfl)
  have hu : Semiformula.Evalb (M := V) ![u, c] prf.val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_forward q r n m)
  have hc : Semiformula.Evalb (M := V)
      ![c, i, impValue f g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hdmp : Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hd : Semiformula.Evalb (M := V) ![d, impValue f g] prf.val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
      s i c (impValue f g) u d hs hc hu hdmp
  have hfg : Semiformula.Evalb (M := V)
      ![impValue f g, f, g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hout : Semiformula.Evalb (M := V)
      ![transferForwardValue p h q r n m, d, h] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    h f (impValue f g) g d (transferForwardValue p h q r n m)
    hh hfg hd hout

theorem extendedProofGraph_of_transferReverseGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p h q r n m e f g t : V)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, e]
      (extendedProofGraph w hw).val)
    (hh : Semiformula.Evalb (M := V) ![h, g]
      (extendedProofGraph w hw).val)
    (ht : Semiformula.Evalb (M := V) ![t, p, h, q, r, n, m]
      transferReverseGraph.val) :
    Semiformula.Evalb (M := V) ![t, f]
      (extendedProofGraph w hw).val := by
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hfq := (leftInstanceCodeGraph_iff f q n m).mp hf
  have hgq := (rightInstanceCodeGraph_iff g r n m).mp hg
  have htq := (transferReverseGraph_iff t p h q r n m).mp ht
  subst e
  subst f
  subst g
  subst t
  let Th := extendedPRTheoryPresentation w hw
  let prf := proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf
  let i := instanceEqualityCodeValue (V := V) q r n m
  let f := leftInstanceCodeValue (V := V) q n m
  let g := rightInstanceCodeValue (V := V) r n m
  let c := reverseAxiomCodeValue (V := V) q r n m
  let u := oneLineProofValue c
  let s := specializeValue (V := V) p q r n m
  let d := mpValue u s
  have hs : Semiformula.Evalb (M := V) ![s, i] prf.val := by
    exact extendedProofGraph_of_specializeGraph w hw p q r n m
      (equalityCodeValue q r) i s
      ((equalityCodeGraph_iff _ _ _).mpr rfl)
      ((instanceEqualityCodeGraph_iff _ _ _ _ _).mpr rfl) hp
      ((specializeGraph_iff _ _ _ _ _ _).mpr rfl)
  have hu : Semiformula.Evalb (M := V) ![u, c] prf.val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_reverse q r n m)
  have hc : Semiformula.Evalb (M := V)
      ![c, i, impValue g f] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hdmp : Semiformula.Evalb (M := V) ![d, u, s] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hd : Semiformula.Evalb (M := V) ![d, impValue g f] prf.val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
      s i c (impValue g f) u d hs hc hu hdmp
  have hgf : Semiformula.Evalb (M := V)
      ![impValue g f, g, f] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hout : Semiformula.Evalb (M := V)
      ![transferReverseValue p h q r n m, d, h] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    h g (impValue g f) f d (transferReverseValue p h q r n m)
    hh hgf hd hout

noncomputable def transferForwardFromStagesValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p h sEq sLeft q r n m : V) : V :=
  transferForwardValue
    (bridgeEqualityValue p sEq q r)
    (bridgeLeftValue h sLeft q n m) q r n m

noncomputable def transferReverseFromStagesValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p h sEq sRight q r n m : V) : V :=
  transferReverseValue
    (bridgeEqualityValue p sEq q r)
    (bridgeRightValue h sRight r n m) q r n m

private theorem eval_stage_transfer_equality_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (x y p h sEq sInst q r n m : V) :
    Semiformula.Eval
        (Semiterm.val ![x, y, p, h, sEq, sInst, q, r, n, m]
          Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 10), #2, #4, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![x, p, sEq, q, r] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_stage_transfer_left_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 6)
    (z x y p h sEq sLeft q r n m : V) :
    Semiformula.Eval
        (Semiterm.val ![z, x, y, p, h, sEq, sLeft, q, r, n, m]
          Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 11), #4, #6, #7, #9, #10])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![z, h, sLeft, q, n, m] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_stage_transfer_right_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 6)
    (z x y p h sEq sRight q r n m : V) :
    Semiformula.Eval
        (Semiterm.val ![z, x, y, p, h, sEq, sRight, q, r, n, m]
          Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 11), #4, #6, #8, #9, #10])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![z, h, sRight, r, n, m] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_stage_transfer_result_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 7)
    (z x y p h sEq sInst q r n m : V) :
    Semiformula.Eval
        (Semiterm.val ![z, x, y, p, h, sEq, sInst, q, r, n, m]
          Empty.elim ∘
          ![(#2 : ArithmeticSemiterm Empty 11), #1, #0, #7, #8, #9, #10])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![y, x, z, q, r, n, m] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

noncomputable def transferForwardFromStagesGraph :
    𝚺₁.Semisentence 9 := .mkSigma
  “y p h sEq sLeft q r n m.
    ∃ pe, !bridgeEqualityGraph pe p sEq q r ∧
    ∃ ph, !bridgeLeftGraph ph h sLeft q n m ∧
      !transferForwardGraph y pe ph q r n m”

noncomputable def transferReverseFromStagesGraph :
    𝚺₁.Semisentence 9 := .mkSigma
  “y p h sEq sRight q r n m.
    ∃ pe, !bridgeEqualityGraph pe p sEq q r ∧
    ∃ ph, !bridgeRightGraph ph h sRight r n m ∧
      !transferReverseGraph y pe ph q r n m”

theorem transferForwardFromStagesGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h sEq sLeft q r n m : V) :
    Semiformula.Evalb (M := V)
        ![y, p, h, sEq, sLeft, q, r, n, m]
        transferForwardFromStagesGraph.val ↔
      y = transferForwardFromStagesValue p h sEq sLeft q r n m := by
  simp [transferForwardFromStagesGraph, transferForwardFromStagesValue,
    eval_stage_transfer_equality_iff, eval_stage_transfer_left_iff,
    eval_stage_transfer_result_iff,
    bridgeEqualityGraph_iff, bridgeLeftGraph_iff,
    transferForwardGraph_iff]

theorem transferReverseFromStagesGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p h sEq sRight q r n m : V) :
    Semiformula.Evalb (M := V)
        ![y, p, h, sEq, sRight, q, r, n, m]
        transferReverseFromStagesGraph.val ↔
      y = transferReverseFromStagesValue p h sEq sRight q r n m := by
  simp [transferReverseFromStagesGraph, transferReverseFromStagesValue,
    eval_stage_transfer_equality_iff, eval_stage_transfer_right_iff,
    eval_stage_transfer_result_iff,
    bridgeEqualityGraph_iff, bridgeRightGraph_iff,
    transferReverseGraph_iff]

theorem transferForwardFromStagesValue_nat
    (p h sEq sLeft q r n m : ℕ) :
    transferForwardFromStagesValue p h sEq sLeft q r n m =
      transferForwardFromStages p h sEq sLeft q r n m := by
  simp [transferForwardFromStagesValue, transferForwardFromStages,
    bridgeEqualityValue_nat, bridgeLeftValue_nat,
    transferForwardValue_nat]

theorem transferReverseFromStagesValue_nat
    (p h sEq sRight q r n m : ℕ) :
    transferReverseFromStagesValue p h sEq sRight q r n m =
      transferReverseFromStages p h sEq sRight q r n m := by
  simp [transferReverseFromStagesValue, transferReverseFromStages,
    bridgeEqualityValue_nat, bridgeRightValue_nat,
    transferReverseValue_nat]

theorem extendedProofGraph_of_transferForwardFromStagesGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p h sEq sLeft q r n m aEq uEq aLeft uLeft g t : V)
    (haEq : Semiformula.Evalb (M := V) ![aEq, q, r]
      eqSentenceCodeGraph.val)
    (huEq : Semiformula.Evalb (M := V) ![uEq, aEq, sEq]
      stageCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, uEq]
      (extendedProofGraph w hw).val)
    (haLeft : Semiformula.Evalb (M := V) ![aLeft, q, n, m]
      leftSentenceCodeGraph.val)
    (huLeft : Semiformula.Evalb (M := V) ![uLeft, aLeft, sLeft]
      stageCodeGraph.val)
    (hh : Semiformula.Evalb (M := V) ![h, uLeft]
      (extendedProofGraph w hw).val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (ht : Semiformula.Evalb (M := V)
      ![t, p, h, sEq, sLeft, q, r, n, m]
      transferForwardFromStagesGraph.val) :
    Semiformula.Evalb (M := V) ![t, g]
      (extendedProofGraph w hw).val := by
  have htq :=
    (transferForwardFromStagesGraph_iff
      t p h sEq sLeft q r n m).mp ht
  subst t
  let e := equalityCodeValue (V := V) q r
  let f := leftInstanceCodeValue (V := V) q n m
  let pe := bridgeEqualityValue (V := V) p sEq q r
  let ph := bridgeLeftValue (V := V) h sLeft q n m
  have hpe : Semiformula.Evalb (M := V) ![pe, e]
      (extendedProofGraph w hw).val := by
    exact extendedProofGraph_of_bridgeEqualityGraph w hw
      p sEq q r aEq uEq e pe haEq huEq
      ((equalityCodeGraph_iff _ _ _).mpr rfl) hp
      ((bridgeEqualityGraph_iff _ _ _ _ _).mpr rfl)
  have hph : Semiformula.Evalb (M := V) ![ph, f]
      (extendedProofGraph w hw).val := by
    exact extendedProofGraph_of_bridgeLeftGraph w hw
      h sLeft q n m aLeft uLeft f ph haLeft huLeft
      ((leftInstanceCodeGraph_iff _ _ _ _).mpr rfl) hh
      ((bridgeLeftGraph_iff _ _ _ _ _ _).mpr rfl)
  exact extendedProofGraph_of_transferForwardGraph w hw
    pe ph q r n m e f g
      (transferForwardFromStagesValue p h sEq sLeft q r n m)
    ((equalityCodeGraph_iff _ _ _).mpr rfl)
    ((leftInstanceCodeGraph_iff _ _ _ _).mpr rfl) hg hpe hph
    ((transferForwardGraph_iff _ _ _ _ _ _ _).mpr rfl)

theorem extendedProofGraph_of_transferReverseFromStagesGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p h sEq sRight q r n m aEq uEq aRight uRight f t : V)
    (haEq : Semiformula.Evalb (M := V) ![aEq, q, r]
      eqSentenceCodeGraph.val)
    (huEq : Semiformula.Evalb (M := V) ![uEq, aEq, sEq]
      stageCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, uEq]
      (extendedProofGraph w hw).val)
    (haRight : Semiformula.Evalb (M := V) ![aRight, r, n, m]
      rightSentenceCodeGraph.val)
    (huRight : Semiformula.Evalb (M := V) ![uRight, aRight, sRight]
      stageCodeGraph.val)
    (hh : Semiformula.Evalb (M := V) ![h, uRight]
      (extendedProofGraph w hw).val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (ht : Semiformula.Evalb (M := V)
      ![t, p, h, sEq, sRight, q, r, n, m]
      transferReverseFromStagesGraph.val) :
    Semiformula.Evalb (M := V) ![t, f]
      (extendedProofGraph w hw).val := by
  have htq :=
    (transferReverseFromStagesGraph_iff
      t p h sEq sRight q r n m).mp ht
  subst t
  let e := equalityCodeValue (V := V) q r
  let g := rightInstanceCodeValue (V := V) r n m
  let pe := bridgeEqualityValue (V := V) p sEq q r
  let ph := bridgeRightValue (V := V) h sRight r n m
  have hpe : Semiformula.Evalb (M := V) ![pe, e]
      (extendedProofGraph w hw).val := by
    exact extendedProofGraph_of_bridgeEqualityGraph w hw
      p sEq q r aEq uEq e pe haEq huEq
      ((equalityCodeGraph_iff _ _ _).mpr rfl) hp
      ((bridgeEqualityGraph_iff _ _ _ _ _).mpr rfl)
  have hph : Semiformula.Evalb (M := V) ![ph, g]
      (extendedProofGraph w hw).val := by
    exact extendedProofGraph_of_bridgeRightGraph w hw
      h sRight r n m aRight uRight g ph haRight huRight
      ((rightInstanceCodeGraph_iff _ _ _ _).mpr rfl) hh
      ((bridgeRightGraph_iff _ _ _ _ _ _).mpr rfl)
  exact extendedProofGraph_of_transferReverseGraph w hw
    pe ph q r n m e f g
      (transferReverseFromStagesValue p h sEq sRight q r n m)
    ((equalityCodeGraph_iff _ _ _).mpr rfl) hf
    ((rightInstanceCodeGraph_iff _ _ _ _).mpr rfl) hpe hph
    ((transferReverseGraph_iff _ _ _ _ _ _ _).mpr rfl)

noncomputable def forwardFromStagesPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := extendedProofGraph w hw
  “p h sEq sLeft q r n m g t.
    !rightInstanceCodeGraph g r n m ∧
    (∃ aEq uEq,
      !eqSentenceCodeGraph aEq q r ∧
      !stageCodeGraph uEq aEq sEq ∧
      !prf p uEq) ∧
    (∃ aLeft uLeft,
      !leftSentenceCodeGraph aLeft q n m ∧
      !stageCodeGraph uLeft aLeft sLeft ∧
      !prf h uLeft) ∧
    !transferForwardFromStagesGraph t p h sEq sLeft q r n m →
    !prf t g”

noncomputable def reverseFromStagesPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := extendedProofGraph w hw
  “p h sEq sRight q r n m f t.
    !leftInstanceCodeGraph f q n m ∧
    (∃ aEq uEq,
      !eqSentenceCodeGraph aEq q r ∧
      !stageCodeGraph uEq aEq sEq ∧
      !prf p uEq) ∧
    (∃ aRight uRight,
      !rightSentenceCodeGraph aRight r n m ∧
      !stageCodeGraph uRight aRight sRight ∧
      !prf h uRight) ∧
    !transferReverseFromStagesGraph t p h sEq sRight q r n m →
    !prf t f”

noncomputable def uniformForwardFromStagesPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* forwardFromStagesPreservationMatrix w hw

noncomputable def uniformReverseFromStagesPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* reverseFromStagesPreservationMatrix w hw

theorem models_uniformForwardFromStagesPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformForwardFromStagesPreservation w hw := by
  rw [models_iff, uniformForwardFromStagesPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [forwardFromStagesPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_ex, Semiformula.eval_substs, Matrix.comp_vecCons'',
    Matrix.comp₀, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  intro hpre
  rcases hpre.2.1 with ⟨aEq, uEq, haEq, huEq, hp⟩
  rcases hpre.2.2.1 with ⟨aLeft, uLeft, haLeft, huLeft, hh⟩
  exact extendedProofGraph_of_transferForwardFromStagesGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    aEq uEq aLeft uLeft (v 8) (v 9)
    haEq huEq hp haLeft huLeft hh hpre.1 hpre.2.2.2

theorem models_uniformReverseFromStagesPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformReverseFromStagesPreservation w hw := by
  rw [models_iff, uniformReverseFromStagesPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [reverseFromStagesPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_ex, Semiformula.eval_substs, Matrix.comp_vecCons'',
    Matrix.comp₀, Semiterm.val_bvar, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  intro hpre
  rcases hpre.2.1 with ⟨aEq, uEq, haEq, huEq, hp⟩
  rcases hpre.2.2.1 with ⟨aRight, uRight, haRight, huRight, hh⟩
  exact extendedProofGraph_of_transferReverseFromStagesGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    aEq uEq aRight uRight (v 8) (v 9)
    haEq huEq hp haRight huRight hh hpre.1 hpre.2.2.2

theorem provable_PA_uniformForwardFromStagesPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformForwardFromStagesPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformForwardFromStagesPreservation (V := V) w hw

theorem provable_PA_uniformReverseFromStagesPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformReverseFromStagesPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformReverseFromStagesPreservation (V := V) w hw

theorem provable_PA_paForwardFromStagesPreservation :
    𝗣𝗔 ⊢ uniformForwardFromStagesPreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformForwardFromStagesPreservation
    paStageWitness primrec_paStageWitness

theorem provable_PA_paReverseFromStagesPreservation :
    𝗣𝗔 ⊢ uniformReverseFromStagesPreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformReverseFromStagesPreservation
    paStageWitness primrec_paStageWitness

/-! ## Concrete identity-program regression -/

theorem provable_PA_firstSuccess_identity_zero :
    𝗣𝗔 ⊢
      (firstSuccessGraph FailureOfComposition.Kleene.identityIndex).val/[
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0),
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0)] := by
  apply Arithmetic.complete.{0} 𝗣𝗔
  intro V _ _
  rw [models_iff]
  simp only [Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀]
  rw [firstSuccessGraph_eval,
    canonicalPartrecGraphFormula_eval_iff_eventualGraph]
  apply (eventualGraph_eval _ _).mpr
  refine ⟨1, ?_⟩
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Semiterm.val_operator, Matrix.comp₀,
    Tarski.Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero,
    numeral_eq_natCast] using
      (ConcreteWitnessGraphs.identity_computation
        (M := V) (1 : V) (0 : V) (by simp))

theorem identity_zero_leftInstanceCode_exists :
    ∃ p : ℕ, Proof_T paExtendedTheoryPresentation p
      (leftInstanceCode FailureOfComposition.Kleene.identityIndex 0 0) :=
  (PA_provable_left_iff_exists_leftInstanceCode_proof_T
    FailureOfComposition.Kleene.identityIndex 0 0).mp
      provable_PA_firstSuccess_identity_zero

theorem identity_zero_bridge_witness :
    ∃ s p : ℕ,
      Proof_T paExtendedTheoryPresentation p
        (stageCode
          (leftSentenceCode FailureOfComposition.Kleene.identityIndex 0 0) s) ∧
      Proof_T paExtendedTheoryPresentation
        (bridgeLeft p s FailureOfComposition.Kleene.identityIndex 0 0)
        (leftInstanceCode FailureOfComposition.Kleene.identityIndex 0 0) := by
  obtain ⟨s, p, hp⟩ :=
    (PA_provable_iff_exists_stage_proof_T
      ((firstSuccessGraph FailureOfComposition.Kleene.identityIndex).val/[
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0),
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0)])).mp
        provable_PA_firstSuccess_identity_zero
  have hp' : Proof_T paExtendedTheoryPresentation p
      (stageCode
        (leftSentenceCode FailureOfComposition.Kleene.identityIndex 0 0) s) := by
    apply paProof_T_old_to_extended
    simpa [leftSentenceCode] using hp
  exact ⟨s, p, hp',
    proof_T_bridgeLeft paStageWitness hp'⟩

theorem identity_zero_bridge_transfer_application :
    ∃ hLeft : ℕ,
      Proof_T paExtendedTheoryPresentation hLeft
        (leftInstanceCode FailureOfComposition.Kleene.identityIndex 0 0) ∧
      Proof_T paExtendedTheoryPresentation
        (transferForward
          (firstSuccessEventualEqualityProofCode
            FailureOfComposition.Kleene.identityIndex)
          hLeft FailureOfComposition.Kleene.identityIndex
          FailureOfComposition.Kleene.identityIndex 0 0)
        (rightInstanceCode FailureOfComposition.Kleene.identityIndex 0 0) ∧
      Proof_T paExtendedTheoryPresentation
        (transferReverse
          (firstSuccessEventualEqualityProofCode
            FailureOfComposition.Kleene.identityIndex)
          (transferForward
            (firstSuccessEventualEqualityProofCode
              FailureOfComposition.Kleene.identityIndex)
            hLeft FailureOfComposition.Kleene.identityIndex
            FailureOfComposition.Kleene.identityIndex 0 0)
          FailureOfComposition.Kleene.identityIndex
          FailureOfComposition.Kleene.identityIndex 0 0)
        (leftInstanceCode FailureOfComposition.Kleene.identityIndex 0 0) := by
  obtain ⟨s, p, -, hLeft⟩ := identity_zero_bridge_witness
  let e := FailureOfComposition.Kleene.identityIndex
  let hEqCode := firstSuccessEventualEqualityProofCode e
  have hEq : Proof_T paExtendedTheoryPresentation hEqCode
      (equalityCode e e) :=
    paProof_T_old_to_extended
      (proof_T_firstSuccessEventualEqualityProofCode e)
  let hLeftCode := bridgeLeft p s e 0 0
  have hForward : Proof_T paExtendedTheoryPresentation
      (transferForward hEqCode hLeftCode e e 0 0)
      (rightInstanceCode e 0 0) :=
    proof_T_extended_transferForward paStageWitness hEq hLeft
  have hReverse : Proof_T paExtendedTheoryPresentation
      (transferReverse hEqCode
        (transferForward hEqCode hLeftCode e e 0 0) e e 0 0)
      (leftInstanceCode e 0 0) :=
    proof_T_extended_transferReverse paStageWitness hEq hForward
  exact ⟨hLeftCode, hLeft, hForward, hReverse⟩

theorem identity_zero_bridge_transfer_sound :
    (𝗣𝗔 ⊢
      (eventualGraph FailureOfComposition.Kleene.identityIndex).val/[
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0),
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0)]) ∧
    (𝗣𝗔 ⊢
      (firstSuccessGraph FailureOfComposition.Kleene.identityIndex).val/[
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0),
        (↑(0 : ℕ) : ArithmeticSemiterm Empty 0)]) := by
  obtain ⟨hLeft, -, hForward, hReverse⟩ :=
    identity_zero_bridge_transfer_application
  exact ⟨paExtendedProof_T_rightInstanceCode_sound hForward,
    paExtendedProof_T_leftInstanceCode_sound hReverse⟩

end FailureOfComposition.NumericalProofBridge
