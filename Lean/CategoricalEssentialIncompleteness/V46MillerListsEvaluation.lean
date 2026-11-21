/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsCarrier

/-! # Positive value records for arbitrary uniform list algebras

The last record entry is obtained by invoking the nullary operation. Every preceding
entry is obtained by the cons operation on the given label and the next recorded
value. No algebra result is an ordinary computable initial value.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax.NatVectors
open Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)

inductive Evaluates (r : ℕ) : List ℕ → ℕ → Prop
  | nil {v : ℕ} (value : v ∈ operation h0 (r,0)) : Evaluates r [] v
  | cons {a v w : ℕ} {L : List ℕ} (tail : Evaluates r L w)
      (value : v ∈ operation hc (r,Nat.pair a w)) : Evaluates r (a::L) v

theorem evaluates_fiber {r v : ℕ} {L : List ℕ} (h : Evaluates V h0 hc r L v) :
    r ∈ Total.val X.hom.hom v := by
  cases h with
  | nil hv => exact operation_parameter h0 hv
  | cons _ hv => exact operation_parameter hc hv

theorem evaluates_source {r v : ℕ} {L : List ℕ} (h : Evaluates V h0 hc r L v) :
    r ∈ R.obj.support ∧ ∀ a ∈ L,a ∈ V.support := by
  induction h with
  | nil hv =>
      have hf := operation_source h0 hv
      exact ⟨hf.1,by simp⟩
  | @cons a v w L htail hv ih =>
      have hf := operation_source hc hv
      have ha : a ∈ V.support := by simpa only [fiber,Nat.unpair_pair] using hf.1.2
      exact ⟨ih.1,by simpa only [List.forall_mem_cons] using And.intro ha ih.2⟩

theorem evaluates_exists (r : ℕ) (L : List ℕ) (hr : r ∈ R.obj.support)
    (hL : ∀ a ∈ L,a ∈ V.support) : ∃ v,Evaluates V h0 hc r L v := by
  induction L with
  | nil =>
      obtain ⟨v,hv⟩ := operation_exists h0 (by exact ⟨hr,rfl⟩)
      exact ⟨v,.nil hv⟩
  | cons a L ih =>
      have hL' := List.forall_mem_cons.mp hL
      obtain ⟨w,hw⟩ := ih hL'.2
      have hf : fiber R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) (r,Nat.pair a w) := by
        simpa only [fiber,Nat.unpair_pair] using And.intro ⟨hr,hL'.1⟩ (evaluates_fiber V h0 hc hw)
      obtain ⟨v,hv⟩ := operation_exists hc hf
      exact ⟨v,.cons hw hv⟩

theorem evaluates_functional {r v w : ℕ} {L : List ℕ}
    (hv : Evaluates V h0 hc r L v) (hw : Evaluates V h0 hc r L w) : v=w := by
  induction hv generalizing w with
  | nil hv => cases hw with | nil hw => exact Part.mem_unique hv hw
  | cons htail hv ih =>
      cases hw with
      | cons htail' hw =>
          have he := ih htail'
          cases he
          exact Part.mem_unique hv hw

abbrev Input := ℕ × List ℕ
abbrev RecordInput := Input × List ℕ

def Record (r : ℕ) (L states : List ℕ) : Prop :=
  states.length=L.length+1 ∧ states.getD L.length 0 ∈ operation h0 (r,0) ∧
    ∀ i<L.length,states.getD i 0 ∈ operation hc (r,Nat.pair (L.getD i 0) (states.getD (i+1) 0))

def consCall (a : RecordInput) (i : ℕ) : (ℕ × ℕ) × ℕ :=
  ((a.1.1,Nat.pair (a.1.2.getD i 0) (a.2.getD (i+1) 0)),a.2.getD i 0)

def consCalls (a : RecordInput) : List ((ℕ × ℕ) × ℕ) :=
  (List.range a.1.2.length).map (consCall a)

theorem consCall_primrec : Primrec₂ consCall := by
  have hr : Primrec (fun a : RecordInput × ℕ => a.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hL : Primrec (fun a : RecordInput × ℕ => a.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec (fun a : RecordInput × ℕ => a.1.2) := Primrec.snd.comp Primrec.fst
  have ha := (Primrec.list_getD 0).comp hL Primrec.snd
  have hw := (Primrec.list_getD 0).comp hs (Primrec.succ.comp Primrec.snd)
  have hv := (Primrec.list_getD 0).comp hs Primrec.snd
  exact Primrec.pair (Primrec.pair hr (Primrec₂.natPair.comp ha hw)) hv

theorem consCalls_primrec : Primrec consCalls :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))) consCall_primrec

theorem record_enumerable :
    Uniform.Enumerable P (fun a : RecordInput => Record V h0 hc a.1.1 a.1.2 a.2) := by
  have hlen : REPred (fun a : RecordInput => a.2.length=a.1.2.length+1) :=
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))).computablePred.to_re
  have hz : Computable (fun a : RecordInput =>
      ((a.1.1,0),a.2.getD a.1.2.length 0)) :=
    (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) (.const 0))
      ((Primrec.list_getD 0).comp Primrec.snd (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))).to_comp
  have hzero := Uniform.Enumerable.comp hz (operation_enumerable h0)
  have hcons := Uniform.Enumerable.finiteRecord (operation_enumerable hc) consCalls consCalls_primrec.to_comp
  exact ((Uniform.Enumerable.of_re hlen).and (hzero.and hcons)).of_eq (fun a => by
    simp only [Record,consCalls,List.forall_mem_map,List.mem_range,consCall])

theorem evaluates_iff_record (r : ℕ) (L : List ℕ) (v : ℕ) :
    Evaluates V h0 hc r L v ↔ ∃ states,Record V h0 hc r L states ∧ states.getD 0 0=v := by
  constructor
  · intro h
    induction h with
    | nil hv => exact ⟨[_],⟨rfl,by simpa using hv,by simp⟩,by simp⟩
    | @cons a v w L htail hv ih =>
        obtain ⟨states,hs,hw⟩ := ih
        refine ⟨v::states,⟨by simp [hs.1],?_,?_⟩,by simp⟩
        · simpa only [List.length_cons,List.getD_cons_succ] using hs.2.1
        · intro i hi
          cases i with
          | zero =>
              change v ∈ operation hc (r,Nat.pair a (states.getD 0 0))
              rw [hw]
              exact hv
          | succ i => simpa only [List.getD_cons_succ] using hs.2.2 i (by simpa using hi)
  · rintro ⟨states,hs,hv⟩
    induction L generalizing v states with
    | nil => exact .nil (by simpa [← hv] using hs.2.1)
    | cons a L ih =>
        cases states with
        | nil =>
            have hlen := hs.1
            simp at hlen
        | cons s states =>
            have hsv : s=v := by simpa using hv
            subst s
            apply Evaluates.cons (w := states.getD 0 0)
            · apply ih _ states
              · exact ⟨by simpa using hs.1,by simpa only [List.length_cons,List.getD_cons_succ] using hs.2.1,
                  fun i hi => by simpa only [List.getD_cons_succ] using hs.2.2 (i+1) (by simpa using hi)⟩
              · rfl
            · simpa using hs.2.2 0 (by simp)

theorem evaluates_enumerable :
    Uniform.Enumerable P (fun a : Input × ℕ => Evaluates V h0 hc a.1.1 a.1.2 a.2) := by
  have hr : Computable (fun a : (Input × ℕ) × List ℕ => (a.1.1,a.2)) :=
    Computable.pair (Computable.fst.comp Computable.fst) Computable.snd
  have he : REPred (fun a : (Input × ℕ) × List ℕ => a.2.getD 0 0=a.1.2) :=
    (Primrec.eq.comp ((Primrec.list_getD 0).comp Primrec.snd (.const 0)) (Primrec.snd.comp Primrec.fst)).computablePred.to_re
  exact ((Uniform.Enumerable.comp hr (record_enumerable V h0 hc)).and (Uniform.Enumerable.of_re he)).projection.of_eq
    (fun a => (evaluates_iff_record V h0 hc a.1.1 a.1.2 a.2).symm)

end CategoricalEssentialIncompleteness.V46.Miller.Lists
