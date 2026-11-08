/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxEvaluation
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTrace

/-! # Constructor framing and concatenation for the actual uniform evaluator

The trace stores the original ordered input records. Its transitions
are the actual arbitrary algebra operations; only finite computation
witnesses are existential. Framing applies to successful computations,
so an ambient tail cannot supply a missing child of the original word.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

theorem outcome_frame {a : SyntaxPolynomial (Total.TotalCategory P)} {Z : Over R}
    (h : object R X Y a ⟶ Z) (formula : Bool) (r s stack new tail : ℕ)
    (hn : new ∈ outcome h formula (r,(s,stack))) (hnew : new≠0) :
    frameStatus new tail ∈ outcome h formula (r,(s,Words.append stack tail)) := by
  rcases (outcome_graph h formula r s stack new).mp hn with ⟨_,hz⟩ | ⟨u,rest,value,hu,hv,hnewv⟩
  · exact False.elim (hnew hz)
  · subst new
    apply (outcome_graph h formula r s (Words.append stack tail) _).mpr
    refine Or.inr ⟨u,Words.append rest tail,value,?_,hv,?_⟩
    · exact Coding.refill_frame (skeleton a) s stack u rest tail hu
    · simp only [frameStatus_succ,Words.append_adjoin]

theorem valueStep_zero (r record : ℕ) : valueStep hT hF (r,(record,0)) = Part.some 0 := by
  simp [valueStep]

theorem valueStep_frame (r record old new tail : ℕ)
    (hn : new ∈ valueStep hT hF (r,(record,old))) (hnew : new≠0) :
    frameStatus new tail ∈ valueStep hT hF (r,(record,frameStatus old tail)) := by
  rcases Nat.eq_zero_or_pos old with hz | hpos
  · rw [hz,valueStep_zero] at hn
    exact False.elim (hnew (Part.mem_some_iff.mp hn))
  · obtain ⟨stack,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    by_cases hk0 : (Nat.unpair record).2=0
    · have ho : new ∈ outcome hT false (r,((Nat.unpair record).1,stack)) := by
        simpa [valueStep,hk0] using hn
      simpa [valueStep,hk0,frameStatus_succ] using
        outcome_frame hT false r (Nat.unpair record).1 stack new tail ho hnew
    · by_cases hk1 : (Nat.unpair record).2=1
      · have ho : new ∈ outcome hF true (r,((Nat.unpair record).1,stack)) := by
          simpa [valueStep,hk0,hk1] using hn
        simpa [valueStep,hk0,hk1,frameStatus_succ] using
          outcome_frame hF true r (Nat.unpair record).1 stack new tail ho hnew
      · have hz : new=0 := by simpa [valueStep,hk0,hk1] using hn
        exact False.elim (hnew hz)

inductive Trace (r : ℕ) : List ℕ → ℕ → ℕ → Prop
  | nil (s : ℕ) : Trace r [] s s
  | cons {record : ℕ} {records : List ℕ} {s t u : ℕ}
      (step : t ∈ valueStep hT hF (r,(record,s)))
      (rest : Trace r records t u) : Trace r (record::records) s u

namespace Trace

theorem append {r : ℕ} {left right : List ℕ} {s t u : ℕ}
    (hl : Trace hT hF r left s t) (hr : Trace hT hF r right t u) :
    Trace hT hF r (left++right) s u := by
  induction hl with
  | nil _ => exact hr
  | cons hs _ ih => exact .cons hs (ih hr)

theorem functional {r : ℕ} {records : List ℕ} {s t u : ℕ}
    (ht : Trace hT hF r records s t) (hu : Trace hT hF r records s u) : t=u := by
  induction ht generalizing u with
  | nil _ => cases hu;rfl
  | cons ht _ ih =>
      cases hu with
      | cons hu hrest =>
          have he := Part.mem_unique ht hu
          cases he
          exact ih hrest

theorem error_of_start {r : ℕ} {records : List ℕ} {s t : ℕ}
    (h : Trace hT hF r records s t) (hs : s=0) : t=0 := by
  revert hs
  induction h with
  | nil _ => exact fun hs => hs
  | cons hstep _ ih =>
      intro hs
      apply ih
      rw [hs,valueStep_zero] at hstep
      exact Part.mem_some_iff.mp hstep

theorem error {r : ℕ} {records : List ℕ} {t : ℕ}
    (h : Trace hT hF r records 0 t) : t=0 := error_of_start hT hF h rfl

theorem frame {r : ℕ} {records : List ℕ} {s t : ℕ}
    (h : Trace hT hF r records s t) (ht : t≠0) (tail : ℕ) :
    Trace hT hF r records (frameStatus s tail) (frameStatus t tail) := by
  induction h with
  | nil _ => exact .nil _
  | @cons record records s v t hs hrest ih =>
      have hv : v≠0 := by
        intro hz
        subst v
        exact ht (error hT hF hrest)
      exact .cons (valueStep_frame hT hF r record s v tail hs hv) (ih ht)

end Trace

def FiniteRecord (r : ℕ) (records : List ℕ) (initial : ℕ) (states : List ℕ) : Prop :=
  states.length=records.length+1 ∧ states.getD 0 0=initial ∧
    ∀ i<records.length,states.getD (i+1) 0 ∈ valueStep hT hF (r,(records.getD i 0,states.getD i 0))

theorem trace_iff_record (r : ℕ) (records : List ℕ) (initial final : ℕ) :
    Trace hT hF r records initial final ↔
      ∃ states,FiniteRecord hT hF r records initial states ∧ states.getD records.length 0=final := by
  constructor
  · intro h
    induction h with
    | nil s => exact ⟨[s],⟨rfl,by simp,by simp⟩,by simp⟩
    | @cons record records s t u hstep hrest ih =>
        obtain ⟨states,hs,hfinal⟩ := ih
        refine ⟨s::states,⟨by simp [hs.1],by simp,?_⟩,?_⟩
        · intro i hi
          cases i with
          | zero =>
              change states.getD 0 0 ∈ valueStep hT hF (r,(record,s))
              rw [hs.2.1]
              exact hstep
          | succ i =>
              simpa only [List.getD_cons_succ] using hs.2.2 i (by simpa using hi)
        · simpa only [List.length_cons,List.getD_cons_succ] using hfinal
  · rintro ⟨states,hs,hfinal⟩
    induction records generalizing initial states with
    | nil =>
        have he : initial=final := by simpa using hs.2.1.symm.trans hfinal
        rw [← he]
        exact .nil _
    | cons record records ih =>
        cases states with
        | nil =>
            have hlen := hs.1
            simp at hlen
        | cons s states =>
            have hs0 : s=initial := by simpa using hs.2.1
            subst s
            have hslen : states.length=records.length+1 := by simpa using hs.1
            have hstep : states.getD 0 0 ∈ valueStep hT hF (r,(record,initial)) := by
              simpa using hs.2.2 0 (by simp)
            apply Trace.cons hstep
            apply ih (states.getD 0 0) states
            · exact ⟨hslen,rfl,fun i hi => by simpa using hs.2.2 (i+1) (by simpa using hi)⟩
            · simpa only [List.length_cons,List.getD_cons_succ] using hfinal

theorem evaluation_trace (r word final : ℕ) :
    final ∈ evaluation hT hF (Nat.pair r word) ↔ Trace hT hF r (Nat.natToList word) 1 final := by
  rw [evaluation_graph,trace_iff_record]
  simp only [loopLength,Nat.unpair_pair,NatVectors.len_eq_decode]
  apply exists_congr
  intro states
  change (_ ∧ _ ∧ _) ∧ _ ↔ (_ ∧ _ ∧ _) ∧ _
  simp only [loopStep,Nat.unpair_pair,NatVectors.nth_eq_decode]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
