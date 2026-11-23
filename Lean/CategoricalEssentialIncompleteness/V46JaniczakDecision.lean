/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakFiniteEvaluator
public import CategoricalEssentialIncompleteness.V46JaniczakClosure
public import CategoricalEssentialIncompleteness.V46JaniczakFrame
public import CategoricalEssentialIncompleteness.V46JaniczakReduction

/-!
# A decision procedure from a recursive class spectrum

Murwanashyaka, Pakhomov and Visser's Janiczak theory has a decidable same-language extension whenever the signed pair has a recursive separator. The procedure evaluates a finite sample determined by the formula.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

namespace FiniteEvaluator

theorem correct {X : Type*} (enc : X → ℕ) (inj : Function.Injective enc)
    (D : X → Prop) (L : List ℕ) (mem : ∀ z, z ∈ L ↔ ∃ a, D a ∧ enc a = z)
    (p : Formula) (k : ℕ) (hk : p.depth ≤ k) (env : Env) (v : ℕ → X)
    (hv : ∀ i, value env i = enc (v i)) :
    run k p.code L env = true ↔
      p.Restricted (fun a b ↦ (enc a).unpair.1 = (enc b).unpair.1) D v := by
  induction p generalizing k env v with
  | equal x y =>
    cases k with
    | zero => exact (Nat.not_le_of_lt ((Formula.equal x y).depth_pos) hk).elim
    | succ k => simp [run, Formula.code, Formula.Restricted, hv, inj.eq_iff]
  | related x y =>
    cases k with
    | zero => exact (Nat.not_le_of_lt ((Formula.related x y).depth_pos) hk).elim
    | succ k => simp [run, Formula.code, Formula.Restricted, hv]
  | top =>
    cases k with
    | zero => exact (Nat.not_le_of_lt Formula.top.depth_pos hk).elim
    | succ k => simp [run, Formula.code, Formula.Restricted]
  | neg p ih =>
    cases k with
    | zero => exact (Nat.not_le_of_lt p.neg.depth_pos hk).elim
    | succ k =>
      have hp := ih k (Nat.le_of_succ_le_succ hk) env v hv
      simpa [run, Formula.code, Formula.Restricted, Bool.not_eq_true'] using not_congr hp
  | conj p q ih jh =>
    cases k with
    | zero => exact (Nat.not_le_of_lt (p.conj q).depth_pos hk).elim
    | succ k =>
      have hh : max p.depth q.depth ≤ k := Nat.le_of_succ_le_succ hk
      simpa [run, Formula.code, Formula.Restricted] using
        and_congr (ih k ((le_max_left ..).trans hh) env v hv)
          (jh k ((le_max_right ..).trans hh) env v hv)
  | ex x p ih =>
    cases k with
    | zero => exact (Nat.not_le_of_lt (Formula.ex x p).depth_pos hk).elim
    | succ k =>
      have hval (a : X) (i : ℕ) :
          value ((x,enc a)::env) i = enc (Function.update v x a i) := by
        rw [value_cons]
        by_cases h : i=x
        · simp [h]
        · simpa [Function.update_of_ne h] using hv i
      simp only [run, Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true,
        List.any_eq_true, Formula.Restricted]
      constructor
      · rintro ⟨z,hz,hs⟩
        obtain ⟨a,ha,rfl⟩ := (mem z).mp hz
        exact ⟨a,ha,(ih k (Nat.le_of_succ_le_succ hk) _ _ (hval a)).mp hs⟩
      · rintro ⟨a,ha,hp⟩
        exact ⟨enc a,(mem _).mpr ⟨a,ha,rfl⟩,
          (ih k (Nat.le_of_succ_le_succ hk) _ _ (hval a)).mpr hp⟩

end FiniteEvaluator

private def closureWord (e : ℕ) := Formula.closeCode (e+1) e

private def wordSample (d : ℕ → Bool) (e : ℕ) := Frame.sampleCodes d (e+1)

private def decisionState (d : ℕ → Bool) (e : ℕ) : FiniteEvaluator.State :=
  (closureWord e+1,closureWord e,wordSample d e,[])

private theorem computable_closureWord : Computable closureWord :=
  (Formula.primrec_closeCode.comp Primrec.succ Primrec.id).to_comp

private theorem computable_wordSample {d : ℕ → Bool} (hd : Computable d) : Computable (wordSample d) :=
  (Frame.computable_sampleCodes hd).comp Primrec.succ.to_comp

private theorem computable_decisionState {d : ℕ → Bool} (hd : Computable d) : Computable (decisionState d) :=
  (Primrec.succ.to_comp.comp computable_closureWord).pair
    (computable_closureWord.pair ((computable_wordSample hd).pair (Computable.const ([] : FiniteEvaluator.Env))))

/-- The finite sample determined by the variable bound decides the universal
closure of a formula in the model with the prescribed finite spectrum. -/
def decideSpectrum (d : ℕ → Bool) (e : ℕ) :=
  let b := e+1
  let q := Formula.closeCode b e
  FiniteEvaluator.run (q+1) q (Frame.sampleCodes d b) []

theorem computable_decideSpectrum {d : ℕ → Bool} (hd : Computable d) :
    Computable (decideSpectrum d) :=
  (FiniteEvaluator.primrec_run.to_comp.comp (computable_decisionState hd)).of_eq (fun _ ↦ rfl)

theorem decideSpectrum_correct {C : Set ℕ} {d : ℕ → Bool} (hd : ∀ i, d i = true ↔ i ∈ C)
    (p : Formula) : decideSpectrum d p.code = true ↔ (canonical C).Valid p := by
  let b := p.code+1
  let q := Formula.close b p
  let v : ℕ → Frame.Point C := fun _ ↦ Frame.center
  have hb : p.Below b := p.below_of_code_lt b (Nat.lt_succ_self _)
  have hq : q.Below b := Formula.below_close hb
  have hs (i : Fin b) : Frame.sample b (v i) := ⟨Nat.succ_pos _,Nat.succ_pos _⟩
  have eval := FiniteEvaluator.correct Frame.code Frame.code_injective (Frame.sample b)
    (Frame.sampleCodes d b) (Frame.mem_sampleCodes hd b) q (q.code+1) q.depth_le_code [] v
    (fun _ ↦ rfl)
  have key : (fun a c : Frame.Point C ↦ (Frame.code a).unpair.1 = (Frame.code c).unpair.1) =
      (fun a c ↦ a.1 = c.1) := by
    funext a c
    exact propext (by simp only [Frame.code_key, Frame.keyCode_injective.eq_iff])
  rw [key] at eval
  have transfer := Formula.restricted_transfer (Frame.sampleReservoir (C := C) b)
    (Frame.fullReservoir b) q hq (Transfer.Matches.ident v) hs (fun _ ↦ trivial)
  unfold Structure.Valid
  rw [← Formula.holds_close (canonical C).rel v p hb]
  change FiniteEvaluator.run (Formula.closeCode b p.code+1) (Formula.closeCode b p.code) (Frame.sampleCodes d b) [] = true ↔ _
  rw [← Formula.code_close]
  exact eval.trans (transfer.trans (Formula.restricted_univ (canonical C).rel v q))

theorem decidable_extension_of_separator {P N C : Set ℕ} (hp : P ⊆ C) (hn : Disjoint C N)
    (hc : ComputablePred (· ∈ C)) :
    ∃ U : Set Formula, Signed P N ⊆ U ∧ Consistent U ∧ DecidableTheorems U := by
  obtain ⟨d,hd,h⟩ := ComputablePred.computable_iff.mp hc
  have dec (i : ℕ) : d i = true ↔ i ∈ C := by
    exact Iff.of_eq (congrFun h i).symm
  let M := canonical C
  refine ⟨Set.ofPred M.Valid, Canonical.models_signed hp hn, ⟨M, fun _ ha ↦ ha⟩,
    decideSpectrum d,computable_decideSpectrum hd,fun p ↦ ?_⟩
  exact (decideSpectrum_correct dec p).trans (consequence_fullTheory M p).symm

/-- For a disjoint pair, the fixed Janiczak extension is essentially undecidable
if and only if the numerical pair is recursively inseparable. -/
theorem essentiallyUndecidable_iff {P N : Set ℕ} (hdis : Disjoint P N) :
    EssentiallyUndecidable (Signed P N) ↔
      CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N := by
  refine ⟨fun hu ↦ ⟨hdis, ?_⟩, essentiallyUndecidable_of_inseparable⟩
  rintro ⟨C,hc,hp,hn⟩
  obtain ⟨U,he,hu',hd⟩ := decidable_extension_of_separator hp hn hc
  exact hu U he hu' hd

end Janiczak
