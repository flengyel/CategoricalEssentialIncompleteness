/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerUniformFinite
import Mathlib.Data.List.GetD

/-! # Selected finite positive operation records

The step is an arbitrary uniformly represented partial operation. Finite
records carry its positive graph witnesses existentially; they are not
new syntax labels. The input, hence its external parameter, is unchanged
through every state. This module does not assert algebra initiality.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.UniformTrees

abbrev Input := ℕ × (ℕ × ℕ)
abbrev Call := Input × ℕ
abbrev RecordInput := (ℕ × ℕ) × List ℕ

def callAt (a : RecordInput) (i : ℕ) : Call :=
  ((a.1.1,(i,a.2.getD i 0)),a.2.getD (i+1) 0)

theorem callAt_primrec : Primrec₂ callAt := by
  have hx : Primrec (fun a : RecordInput × ℕ => a.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hl : Primrec (fun a : RecordInput × ℕ => a.1.2) := Primrec.snd.comp Primrec.fst
  have hv := (Primrec.list_getD 0).comp hl Primrec.snd
  have hw := (Primrec.list_getD 0).comp hl (Primrec.succ.comp Primrec.snd)
  exact Primrec.pair (Primrec.pair hx (Primrec.pair Primrec.snd hv)) hw

def calls (a : RecordInput) : List Call := (List.range a.1.2).map (callAt a)

theorem calls_primrec : Primrec calls :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)) callAt_primrec

variable {P : Uniform.Family}
variable (step : Input → Part ℕ) (initial : ℕ → ℕ)

def Record (x n : ℕ) (states : List ℕ) : Prop :=
  states.length = n+1 ∧ states.getD 0 0 = initial x ∧
    ∀ i < n,states.getD (i+1) 0 ∈ step (x,(i,states.getD i 0))

theorem calls_iff (x n : ℕ) (states : List ℕ) :
    (∀ a ∈ calls ((x,n),states),a.2 ∈ step a.1) ↔
      ∀ i < n,states.getD (i+1) 0 ∈ step (x,(i,states.getD i 0)) := by
  constructor
  · intro h i hi
    exact h (callAt ((x,n),states) i)
      (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  · intro h a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact h i (List.mem_range.mp hi)

theorem record_enumerable
    (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
    (hi : Computable initial) :
    Uniform.Enumerable P (fun a : RecordInput => Record step initial a.1.1 a.1.2 a.2) := by
  have hlen : REPred (fun a : RecordInput => a.2.length = a.1.2+1) :=
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).computablePred.to_re
  have hz : Computable (fun a : RecordInput => (a.1.1,a.2.getD 0 0)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      ((Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const 0))
  have hzero : REPred (fun a : RecordInput => a.2.getD 0 0 = initial a.1.1) := by
    exact (REPred.comp hz (OracleComputation.partrecGraph hi.partrec)).of_eq
      (fun _ => Part.mem_some_iff)
  have hcalls := Uniform.Enumerable.finiteRecord
    ((Uniform.represented_iff_graph_enumerable P (.product .nat (.product .nat .nat)) .nat step).mp hs)
    calls calls_primrec.to_comp
  exact ((Uniform.Enumerable.of_re hlen).and ((Uniform.Enumerable.of_re hzero).and hcalls)).of_eq
    (fun a => by
      rcases a with ⟨⟨x,n⟩,states⟩
      exact and_congr_right (fun _ => and_congr_right (fun _ => calls_iff step x n states)))

theorem record_zero (x : ℕ) : Record step initial x 0 [initial x] := by
  refine ⟨rfl,by simp,?_⟩
  intro i hi
  omega

theorem record_append {x n : ℕ} {states : List ℕ}
    (h : Record step initial x n states)
    {new : ℕ} (hn : new ∈ step (x,(n,states.getD n 0))) :
    Record step initial x (n+1) (states ++ [new]) := by
  have hlen := h.1
  refine ⟨by simp [h.1],?_,?_⟩
  · rw [List.getD_append states [new] 0 0 (by omega)]
    exact h.2.1
  · intro i hi
    rcases lt_or_eq_of_le (show i ≤ n by omega) with hil | hie
    · rw [List.getD_append states [new] 0 (i+1) (by omega),
        List.getD_append states [new] 0 i (by omega)]
      exact h.2.2 i hil
    · subst i
      rw [List.getD_append_right states [new] 0 (n+1) (by omega),
        List.getD_append states [new] 0 n (by omega),h.1,Nat.sub_self]
      simpa using hn

theorem record_values_unique {x n : ℕ} {left right : List ℕ}
    (hl : Record step initial x n left) (hr : Record step initial x n right) :
    ∀ i,i ≤ n → left.getD i 0 = right.getD i 0 := by
  intro i
  induction i with
  | zero => exact fun _ => hl.2.1.trans hr.2.1.symm
  | succ i ih =>
    intro hi
    have hlt : i<n := by omega
    have hv := hl.2.2 i hlt
    rw [ih (by omega)] at hv
    exact Part.mem_unique hv (hr.2.2 i hlt)

theorem record_states_unique {x n : ℕ} {left right : List ℕ}
    (hl : Record step initial x n left) (hr : Record step initial x n right) : left=right := by
  apply List.ext_getElem (hl.1.trans hr.1.symm)
  intro i hil hir
  rw [← List.getD_eq_getElem left 0 hil,← List.getD_eq_getElem right 0 hir]
  have hlen := hl.1
  exact record_values_unique step initial hl hr i (by omega)

variable (steps : ℕ → ℕ)

def Graph (x y : ℕ) : Prop :=
  ∃ states,Record step initial x (steps x) states ∧ states.getD (steps x) 0 = y

theorem graph_functional (x y y' : ℕ) (hy : Graph step initial steps x y)
    (hy' : Graph step initial steps x y') : y=y' := by
  obtain ⟨left,hl,hly⟩ := hy
  obtain ⟨right,hr,hry⟩ := hy'
  exact hly.symm.trans ((record_values_unique step initial hl hr (steps x) le_rfl).trans hry)

theorem graph_enumerable
    (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
    (hi : Computable initial) (hn : Computable steps) :
    Uniform.Enumerable P (fun a : ℕ × ℕ => Graph step initial steps a.1 a.2) := by
  have ha : Computable (fun a : (ℕ × ℕ) × List ℕ => ((a.1.1,steps a.1.1),a.2)) :=
    Computable.pair (Computable.pair (Computable.fst.comp Computable.fst)
      (hn.comp (Computable.fst.comp Computable.fst))) Computable.snd
  have hb : Computable (fun a : (ℕ × ℕ) × List ℕ => (a.2.getD (steps a.1.1) 0,a.1.2)) :=
    Computable.pair ((Primrec.list_getD 0).to_comp.comp Computable.snd
      (hn.comp (Computable.fst.comp Computable.fst))) (Computable.snd.comp Computable.fst)
  have heq : REPred (fun a : (ℕ × ℕ) × List ℕ => a.2.getD (steps a.1.1) 0 = a.1.2) :=
    REPred.comp hb ((Primrec.eq.comp Primrec.fst Primrec.snd).computablePred.to_re)
  exact ((Uniform.Enumerable.comp ha (record_enumerable step initial hs hi)).and
    (Uniform.Enumerable.of_re heq)).projection

def run (x : ℕ) : Part ℕ := ⟨∃ y,Graph step initial steps x y,fun h => Classical.choose h⟩

theorem mem_run (x y : ℕ) : y ∈ run step initial steps x ↔ Graph step initial steps x y := by
  constructor
  · intro hy
    obtain ⟨hd,he⟩ := Part.mem_mk_iff.mp hy
    exact he ▸ Classical.choose_spec hd
  · intro hy
    let hd : ∃ y,Graph step initial steps x y := ⟨y,hy⟩
    exact Part.mem_mk_iff.mpr
      ⟨hd,graph_functional step initial steps x _ y (Classical.choose_spec hd) hy⟩

theorem run_represented
    (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
    (hi : Computable initial) (hn : Computable steps) :
    Uniform.Represented P .nat .nat (run step initial steps) :=
  (Uniform.represented_iff_graph_enumerable P .nat .nat _).mpr
    ((graph_enumerable step initial steps hs hi hn).of_eq (fun a => (mem_run step initial steps a.1 a.2).symm))

theorem run_domain (x : ℕ) :
    (run step initial steps x).Dom ↔ ∃ states,Record step initial x (steps x) states := by
  rw [Part.dom_iff_mem]
  simp only [mem_run,Graph]
  constructor
  · rintro ⟨y,states,hrecord,_⟩
    exact ⟨states,hrecord⟩
  · rintro ⟨states,hrecord⟩
    exact ⟨states.getD (steps x) 0,states,hrecord,rfl⟩

theorem record_exists_on (A : Set ℕ) (I : ℕ → ℕ → ℕ → Prop)
    (hz : ∀ x ∈ A,I x 0 (initial x))
    (ht : ∀ x ∈ A,∀ i < steps x,∀ v,I x i v →
      ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w)
    (x : ℕ) (hx : x ∈ A) :
    ∀ n,n ≤ steps x → ∃ states,Record step initial x n states ∧ I x n (states.getD n 0) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨[initial x],record_zero step initial x,?_⟩
    simpa using hz x hx
  | succ n ih =>
    intro hn
    obtain ⟨states,hs,hI⟩ := ih (by omega)
    obtain ⟨new,hnew,hnI⟩ := ht x hx n (by omega) _ hI
    refine ⟨states ++ [new],record_append step initial hs hnew,?_⟩
    have hlen := hs.1
    rw [List.getD_append_right states [new] 0 (n+1) (by omega),hs.1,Nat.sub_self]
    simpa using hnI

theorem run_total_on (A : Set ℕ) (I : ℕ → ℕ → ℕ → Prop)
    (hz : ∀ x ∈ A,I x 0 (initial x))
    (ht : ∀ x ∈ A,∀ i < steps x,∀ v,I x i v →
      ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w) :
    ∀ x ∈ A,(run step initial steps x).Dom := by
  intro x hx
  obtain ⟨states,hs,_⟩ := record_exists_on step initial steps A I hz ht x hx (steps x) le_rfl
  exact (run_domain step initial steps x).mpr ⟨states,hs⟩

theorem run_output_invariant (A : Set ℕ) (I : ℕ → ℕ → ℕ → Prop)
    (hz : ∀ x ∈ A,I x 0 (initial x))
    (ht : ∀ x ∈ A,∀ i < steps x,∀ v,I x i v →
      ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w)
    {x y : ℕ} (hx : x ∈ A) (hy : y ∈ run step initial steps x) : I x (steps x) y := by
  obtain ⟨states,hs,hI⟩ := record_exists_on step initial steps A I hz ht x hx (steps x) le_rfl
  obtain ⟨other,ho,hy⟩ := (mem_run step initial steps x y).mp hy
  have he : states.getD (steps x) 0 = y :=
    (record_values_unique step initial hs ho (steps x) le_rfl).trans hy
  exact he ▸ hI

end CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
