/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOracleProgramEffective

/-! # Compiling an ordinary coherent table search into one oracle program

Fuel and oracle-prefix length are independent: at stage `t` the search tries
all prefixes of length at most `t`, with ordinary evaluator fuel `t`. A fixed
successful short prefix is therefore revisited with arbitrarily large fuel.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
namespace CategoricalEssentialIncompleteness.V46.Miller.OracleProgram

private def scan (e : Code) (l : List ℕ) (n fuel : ℕ) : ℕ → Option ℕ
  | 0 => none
  | k+1 => (scan e l n fuel k).orElse
      (fun _ => e.evaln fuel (encode (l.take k,n)))

private theorem scan_sound (e : Code) (l : List ℕ) (n fuel count y : ℕ)
    (hy : scan e l n fuel count = some y) :
    ∃ k < count, e.evaln fuel (encode (l.take k,n)) = some y := by
  induction count with
  | zero => simp [scan] at hy
  | succ c ih =>
    cases h : scan e l n fuel c with
    | none => exact ⟨c,by omega,by simpa [scan,h] using hy⟩
    | some z =>
      have he : z=y := Option.some.inj (by simpa [scan,h] using hy)
      subst z
      obtain ⟨k,hk,hv⟩ := ih h
      exact ⟨k,by omega,hv⟩

private theorem scan_has (e : Code) (l : List ℕ) (n fuel count : ℕ)
    (h : ∃ k < count, ∃ y, e.evaln fuel (encode (l.take k,n)) = some y) :
    ∃ y, scan e l n fuel count = some y := by
  induction count with
  | zero => obtain ⟨k,hk,_⟩ := h; omega
  | succ c ih =>
    cases he : scan e l n fuel c with
    | some y => exact ⟨y,by simp [scan,he]⟩
    | none =>
      obtain ⟨k,hk,y,hy⟩ := h
      by_cases hkc : k<c
      · obtain ⟨z,hz⟩ := ih ⟨k,hkc,y,hy⟩
        rw [he] at hz
        cases hz
      · have hek : k=c := by omega
        subst k
        refine ⟨y,?_⟩
        rw [scan,he]
        exact hy

private theorem scan_primrec :
    Primrec (fun a : ((Code × List ℕ) × ℕ) × (ℕ × ℕ) =>
      scan a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2) := by
  let A := ((Code × List ℕ) × ℕ) × ℕ
  have hstep : Primrec₂ (fun a : A => fun q : ℕ × Option ℕ =>
      q.2.orElse (fun _ => a.1.1.1.evaln a.2
        (encode (a.1.1.2.take q.1,a.1.2)))) :=
    (Primrec.option_orElse.comp (Primrec.snd.comp Primrec.snd)
      (Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.encode.comp (Primrec.pair
          (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))).to₂
  have hrec := Primrec.nat_rec (Primrec.const (α := A) (none : Option ℕ)) hstep
  apply (hrec.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).of_eq
  intro a
  induction a.2.2 with
  | zero => rfl
  | succ k ih =>
      exact congrArg (fun o : Option ℕ => o.orElse (fun _ => a.1.1.1.evaln a.2.1
        (encode (a.1.1.2.take k,a.1.2)))) ih

private def stage (e : Code) (l : List ℕ) (n : ℕ) : Option ℕ :=
  scan e l n l.length (l.length+1)

private theorem stage_computable :
    Computable (fun a : (Code × List ℕ) × ℕ => stage a.1.1 a.1.2 a.2) := by
  let A := (Code × List ℕ) × ℕ
  have hlen : Computable (fun a : A => a.1.2.length) :=
    Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst)
  have hinput : Computable (fun a : A => (a,(a.1.2.length,a.1.2.length+1))) :=
    Computable.pair Computable.id (Computable.pair hlen (Computable.succ.comp hlen))
  exact (scan_primrec.to_comp.comp hinput).of_eq (fun _ => rfl)

private def buffer (s : ℕ) : List ℕ :=
  if s=0 then [] else
    (decode (α := List ℕ) ((Nat.unpair s).1-1)).getD [] ++ [(Nat.unpair s).2]

private theorem buffer_computable : Computable buffer := by
  have hc : Computable (fun s : ℕ => decide (s=0)) :=
    (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.decide
  have hd : Computable (fun s : ℕ =>
      (decode (α := List ℕ) ((Nat.unpair s).1-1)).getD []) :=
    Computable.option_getD (Computable.decode.comp
      (Primrec.nat_sub.to_comp.comp (Computable.fst.comp Computable.unpair) (Computable.const 1)))
      (Computable.const [])
  apply (Computable.cond hc (Computable.const [])
    (Computable.list_append.comp hd
      (Primrec.list_cons.to_comp.comp (Computable.snd.comp Computable.unpair)
        (Computable.const [])))).of_eq
  intro s
  simp only [buffer,Bool.cond_decide]

private theorem buffer_next (l : List ℕ) (b : ℕ) :
    buffer (Nat.pair (encode l+1) b) = l ++ [b] := by
  have hn : Nat.pair (encode l+1) b ≠ 0 := by
    have h := Nat.left_le_pair (encode l+1) b
    omega
  simp [buffer,hn,Nat.unpair_pair]

private def streamTransition (e : Code) (n s : ℕ) : ℕ :=
  let l := buffer s
  match stage e l n with
  | some y => Nat.pair 0 y
  | none => Nat.pair (l.length+1) (encode l+1)

private def directive (a : List ℕ × Option ℕ) : ℕ :=
  match a.2 with
  | some y => Nat.pair 0 y
  | none => Nat.pair (a.1.length+1) (encode a.1+1)

private theorem directive_computable : Computable directive := by
  have hquery : Computable (fun a : List ℕ × Option ℕ =>
      Nat.pair (a.1.length+1) (encode a.1+1)) :=
    Primrec₂.natPair.to_comp.comp
      (Computable.succ.comp (Primrec.list_length.to_comp.comp Computable.fst))
      (Computable.succ.comp (Computable.encode.comp Computable.fst))
  have hhalt : Computable₂ (fun (_ : List ℕ × Option ℕ) (y : ℕ) => Nat.pair 0 y) :=
    (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.snd).to₂
  exact (Computable.option_casesOn Computable.snd hquery hhalt).of_eq (fun a => by
    rcases a with ⟨l,o⟩
    cases o <;> rfl)

private theorem streamTransition_computable :
    Computable (fun a : Code × (ℕ × ℕ) => streamTransition a.1 a.2.1 a.2.2) := by
  have hl : Computable (fun a : Code × (ℕ × ℕ) => buffer a.2.2) :=
    buffer_computable.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : Code × (ℕ × ℕ) => stage a.1 (buffer a.2.2) a.2.1) :=
    (stage_computable.comp (Computable.pair (Computable.pair Computable.fst hl)
      (Computable.fst.comp Computable.snd))).of_eq (fun _ => rfl)
  exact (directive_computable.comp (Computable.pair hl hs)).of_eq (fun _ => by
    dsimp only [directive,streamTransition])

private def universalTransition (v : ℕ) : ℕ :=
  streamTransition (Denumerable.ofNat Code (Nat.unpair v).1)
    (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2

private theorem universalTransition_computable : Computable universalTransition := by
  exact (streamTransition_computable.comp (Computable.pair
    ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
    (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))).of_eq (fun _ => rfl)

private def transitionCode : Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp universalTransition_computable.partrec))

private theorem transitionCode_eval (v : ℕ) :
    transitionCode.eval v = Part.some (universalTransition v) :=
  congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp universalTransition_computable.partrec))) v

/-- A compiler on ordinary program indices, chosen before the oracle. -/
@[no_expose] def ofTableCode (e : Code) : Code := transitionCode.curry (encode e)

theorem ofTableCode_computable : Computable ofTableCode :=
  Nat.Partrec.Code.primrec₂_curry.to_comp.comp (Computable.const transitionCode) Computable.encode

private theorem ofTableCode_transition (e : Code) (n s : ℕ) :
    (ofTableCode e).eval (Nat.pair n s) = Part.some (streamTransition e n s) := by
  simp only [ofTableCode,Nat.Partrec.Code.eval_curry,transitionCode_eval,
    universalTransition,Nat.unpair_pair,Denumerable.ofNat_encode]

private theorem numericalPrefix_succ (p : Bits) (k : ℕ) :
    numericalPrefix p (k+1) = numericalPrefix p k ++ [(p k).val] := by
  simp only [numericalPrefix,bitPrefix]
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append,List.map_append,List.map_cons,List.map_nil]
  rfl

private def streamState (p : Bits) : ℕ → ℕ
  | 0 => 0
  | k+1 => Nat.pair (encode (numericalPrefix p k)+1) (p k).val

private theorem buffer_streamState (p : Bits) (k : ℕ) :
    buffer (streamState p k) = numericalPrefix p k := by
  cases k with
  | zero => simp [streamState,buffer,numericalPrefix,bitPrefix]
  | succ k => rw [streamState,buffer_next,numericalPrefix_succ]

private theorem stream_step (e : Code) (p : Bits) (n k : ℕ) :
    step (ofTableCode e) (oracle p) n (streamState p k) =
      match stage e (numericalPrefix p k) n with
      | some y => Part.some (Sum.inl y)
      | none => Part.some (Sum.inr (streamState p (k+1))) := by
  rw [step,ofTableCode_transition]
  simp only [Part.bind_some,streamTransition,buffer_streamState]
  cases h : stage e (numericalPrefix p k) n with
  | some y => simp [execute,Nat.unpair_pair]
  | none => simp [execute,Nat.unpair_pair,oracle,streamState,numericalPrefix_length]

private theorem stage_sound (e : Code) (p : Bits) (n k y : ℕ)
    (hy : stage e (numericalPrefix p k) n = some y) :
    ∃ i, y ∈ e.eval (encode (numericalPrefix p i,n)) := by
  obtain ⟨i,hi,hv⟩ := scan_sound e (numericalPrefix p k) n k (k+1) y (by
    simpa only [stage,numericalPrefix_length] using hy)
  have hs := Nat.Partrec.Code.evaln_sound hv
  refine ⟨i,?_⟩
  simpa only [numericalPrefix_take,Nat.min_eq_left (by omega : i≤k)] using hs

private theorem stage_eventually (e : Code) (p : Bits) (n i y : ℕ)
    (hy : y ∈ e.eval (encode (numericalPrefix p i,n))) :
    ∃ k, ∃ z, stage e (numericalPrefix p k) n = some z := by
  obtain ⟨fuel,hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  let k := max fuel i
  apply Exists.intro k
  have hscan : ∃ z, scan e (numericalPrefix p k) n k (k+1) = some z := by
    apply scan_has e (numericalPrefix p k) n k (k+1)
    refine ⟨i,by omega,y,?_⟩
    have hik : i ≤ k := le_max_right fuel i
    have ht : (numericalPrefix p k).take i = numericalPrefix p i := by
      rw [numericalPrefix_take,Nat.min_eq_left hik]
    rw [ht]
    exact Nat.Partrec.Code.evaln_mono (show fuel ≤ k from le_max_left fuel i) hfuel
  simpa only [stage,numericalPrefix_length] using hscan

private theorem stream_run_sound (e : Code) (p : Bits) (n k y : ℕ)
    (hy : y ∈ run (ofTableCode e) (oracle p) n (streamState p k)) :
    ∃ i, y ∈ e.eval (encode (numericalPrefix p i,n)) := by
  let C (s : ℕ) := ∀ k, s=streamState p k →
    ∃ i, y ∈ e.eval (encode (numericalPrefix p i,n))
  have hh : C (streamState p k) := by
    refine PFun.fixInduction' (C := C) hy ?_ ?_
    · intro s hs k hk
      subst s
      rw [stream_step] at hs
      cases he : stage e (numericalPrefix p k) n with
      | none => simp [he] at hs
      | some z =>
        have hz : y=z := by simpa [he] using hs
        subst z
        exact stage_sound e p n k y he
    · intro s s' _ hs ih k hk
      subst s
      rw [stream_step] at hs
      cases he : stage e (numericalPrefix p k) n with
      | some z => simp [he] at hs
      | none =>
        have hs' : s'=streamState p (k+1) := by simpa [he] using hs
        exact ih (k+1) hs'
  exact hh k rfl

private theorem stream_run_complete (e : Code) (p : Bits) (n y : ℕ)
    (hcoh : ∀ i j a b, a ∈ e.eval (encode (numericalPrefix p i,n)) →
      b ∈ e.eval (encode (numericalPrefix p j,n)) → a=b)
    (hy : ∃ i, y ∈ e.eval (encode (numericalPrefix p i,n))) :
    y ∈ run (ofTableCode e) (oracle p) n 0 := by
  obtain ⟨i,hi⟩ := hy
  obtain ⟨k,z,hz⟩ := stage_eventually e p n i y hi
  have hstage : ∀ j v, stage e (numericalPrefix p j) n = some v → v=y := by
    intro j v hv
    obtain ⟨q,hq⟩ := stage_sound e p n j v hv
    exact hcoh q i v y hq hi
  have hback : ∀ d j, j+d=k →
      y ∈ run (ofTableCode e) (oracle p) n (streamState p j) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hj' : j=k := by omega
      subst j
      apply PFun.fix_stop
      rw [stream_step,hz]
      exact Part.mem_some_iff.mpr (congrArg Sum.inl (hstage k z hz)).symm
    | succ d ih =>
      intro j hj
      cases he : stage e (numericalPrefix p j) n with
      | some v =>
        apply PFun.fix_stop
        rw [stream_step,he]
        exact Part.mem_some_iff.mpr (congrArg Sum.inl (hstage j v he)).symm
      | none =>
        apply PFun.mem_fix_iff.mpr
        refine .inr ⟨streamState p (j+1),?_,ih (j+1) (by omega)⟩
        rw [stream_step,he]
        exact Part.mem_some_iff.mpr rfl
  exact hback k 0 (by omega)


/-- Every result of the concrete compiler is certified by a finite table,
without any coherence hypothesis on that table algorithm. -/
theorem ofTableCode_sound (e : Code) (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTableCode e) p n → ∃ k, y ∈ e.eval (encode (numericalPrefix p k,n)) :=
  stream_run_sound e p n 0 y

/-- Completeness needs output uniqueness only along the specified oracle's
prefixes and at the specified input. -/
theorem ofTableCode_graph_at (e : Code) (p : Bits) (n : ℕ)
    (hcoh : ∀ i j a b, a ∈ e.eval (encode (numericalPrefix p i,n)) →
      b ∈ e.eval (encode (numericalPrefix p j,n)) → a=b) (y : ℕ) :
    y ∈ eval (ofTableCode e) p n ↔ ∃ k, y ∈ e.eval (encode (numericalPrefix p k,n)) :=
  ⟨ofTableCode_sound e p n y,stream_run_complete e p n y hcoh⟩

/-- Exact graph of the compiled program. The index is `ofTableCode e`,
independent of the oracle; coherence is a property of the given table
algorithm and is not a program-realizability assumption. -/
theorem ofTableCode_graph (e : Code)
    (hM : LocalConnectedness.OracleComputation.MonotoneValues
      (fun a : List ℕ × ℕ => e.eval (encode a))) (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTableCode e) p n ↔ ∃ k, y ∈ e.eval (encode (numericalPrefix p k,n)) := by
  constructor
  · exact stream_run_sound e p n 0 y
  · intro hy
    apply stream_run_complete e p n y ?_ hy
    intro i j a b ha hb
    exact Part.mem_unique
      (hM _ _ (numericalPrefix_le p (le_max_left i j)) n a ha)
      (hM _ _ (numericalPrefix_le p (le_max_right i j)) n b hb)

def tableCode (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) : Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp hF)

theorem tableCode_eval (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (a : List ℕ × ℕ) :
    (tableCode F hF).eval (encode a) = F a := by
  rw [tableCode,Classical.choose_spec (Nat.Partrec.Code.exists_code.mp hF)]
  rcases a with ⟨l,n⟩
  simp [Encodable.encode_prod_val,Nat.unpair_pair,Denumerable.ofNat_encode,Part.map_id']

/-- A single ordinary oracle-program index for a given ordinary table
algorithm. It is selected BEFORE any binary representation. -/
def ofTable (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) : Code :=
  ofTableCode (tableCode F hF)


/-- Unconditional finite-prefix soundness for any ordinary table program. -/
theorem ofTable_sound (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTable F hF) p n → ∃ k, y ∈ F (numericalPrefix p k,n) := by
  simpa only [ofTable,tableCode_eval] using ofTableCode_sound (tableCode F hF) p n y

/-- Local uniqueness suffices, even if other oracle fibers have conflicting
outputs. The compiler index is unchanged. -/
theorem ofTable_graph_at (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (p : Bits) (n : ℕ)
    (hcoh : ∀ i j a b, a ∈ F (numericalPrefix p i,n) →
      b ∈ F (numericalPrefix p j,n) → a=b) (y : ℕ) :
    y ∈ eval (ofTable F hF) p n ↔ ∃ k, y ∈ F (numericalPrefix p k,n) := by
  have hc : ∀ i j a b, a ∈ (tableCode F hF).eval (encode (numericalPrefix p i,n)) →
      b ∈ (tableCode F hF).eval (encode (numericalPrefix p j,n)) → a=b := by
    intro i j a b ha hb
    exact hcoh i j a b
      (Eq.mp (congrArg (fun v : Part ℕ => a ∈ v) (tableCode_eval F hF (numericalPrefix p i,n))) ha)
      (Eq.mp (congrArg (fun v : Part ℕ => b ∈ v) (tableCode_eval F hF (numericalPrefix p j,n))) hb)
  simpa only [ofTable,tableCode_eval] using ofTableCode_graph_at (tableCode F hF) p n hc y

theorem ofTable_graph (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (hM : LocalConnectedness.OracleComputation.MonotoneValues F)
    (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTable F hF) p n ↔ ∃ k, y ∈ F (numericalPrefix p k,n) := by
  have hm : LocalConnectedness.OracleComputation.MonotoneValues
      (fun a : List ℕ × ℕ => (tableCode F hF).eval (encode a)) := by
    intro l l' hl n y hy
    have hyl : y ∈ F (l,n) :=
      Eq.mp (congrArg (fun v : Part ℕ => y ∈ v) (tableCode_eval F hF (l,n))) hy
    exact Eq.mpr (congrArg (fun v : Part ℕ => y ∈ v) (tableCode_eval F hF (l',n)))
      (hM l l' hl n y hyl)
  simpa only [ofTable,tableCode_eval] using ofTableCode_graph (tableCode F hF) hm p n y

theorem ofTable_domain (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (hM : LocalConnectedness.OracleComputation.MonotoneValues F) (p : Bits) (n : ℕ) :
    (eval (ofTable F hF) p n).Dom ↔ ∃ k, (F (numericalPrefix p k,n)).Dom := by
  simp only [Part.dom_iff_mem,ofTable_graph F hF hM]
  exact exists_comm


/-- ONE numerical index works for every oracle; it includes simultaneous
undefinedness through the exact graph equation. -/
theorem exists_uniform_index (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F)
    (hM : LocalConnectedness.OracleComputation.MonotoneValues F) :
    ∃ d : ℕ, ∀ p : Bits, ∀ n y : ℕ,
      y ∈ numberedEval d p n ↔ ∃ k, y ∈ F (numericalPrefix p k,n) := by
  refine ⟨encode (ofTable F hF), ?_⟩
  intro p n y
  simpa only [numberedEval_encode] using ofTable_graph F hF hM p n y

end CategoricalEssentialIncompleteness.V46.Miller.OracleProgram
