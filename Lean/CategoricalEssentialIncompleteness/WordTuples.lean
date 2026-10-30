/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NonemptyWordCoding
import CategoricalEssentialIncompleteness.EffectiveForkUniversal
import Mathlib.Data.List.GetD

/-! # Recursive coordinatewise pairing of finite words -/

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.WordCoding

open EffectiveFork (quadCode leftCoordinate rightCoordinate)

def zipPair (xs ys : List ℕ) : List ℕ :=
  (List.range xs.length).map (fun i => Nat.pair (xs.getD i 0) (ys.getD i 0))

@[simp] theorem zipPair_nil (ys : List ℕ) : zipPair [] ys=[] := rfl

@[simp] theorem zipPair_cons (x y : ℕ) (xs ys : List ℕ) :
    zipPair (x::xs) (y::ys)=Nat.pair x y::zipPair xs ys := by
  simp [zipPair,List.range_succ_eq_map,Function.comp_def]

@[simp] theorem zipPair_length (xs ys : List ℕ) : (zipPair xs ys).length=xs.length := by
  simp [zipPair]

theorem zipPair_fst (xs ys : List ℕ) (h : xs.length=ys.length) :
    (zipPair xs ys).map (fun n => (Nat.unpair n).1)=xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at h
      simp [ih ys h]

theorem zipPair_snd (xs ys : List ℕ) (h : xs.length=ys.length) :
    (zipPair xs ys).map (fun n => (Nat.unpair n).2)=ys := by
  induction xs generalizing ys with
  | nil => exact (List.length_eq_zero_iff.mp h.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at h
      simp [ih ys h]

theorem zipPair_recover (xs : List ℕ) :
    zipPair (xs.map (fun n => (Nat.unpair n).1))
      (xs.map (fun n => (Nat.unpair n).2))=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,Nat.pair_unpair]

def zipQuad (ks zs as bs : List ℕ) : List ℕ := zipPair ks (zipPair zs (zipPair as bs))

@[simp] theorem zipQuad_cons (k z a b : ℕ) (ks zs as bs : List ℕ) :
    zipQuad (k::ks) (z::zs) (a::as) (b::bs)=quadCode (k,z,a,b)::zipQuad ks zs as bs := by
  simp only [zipQuad,zipPair_cons]
  rfl

theorem zipQuad_projections (ks zs as bs : List ℕ)
    (h1 : ks.length=zs.length) (h2 : ks.length=as.length) (h3 : ks.length=bs.length) :
    (zipQuad ks zs as bs).map (fun n => (quadCode.symm n).1)=ks ∧
    (zipQuad ks zs as bs).map (fun n => (quadCode.symm n).2.1)=zs ∧
    (zipQuad ks zs as bs).map (fun n => (quadCode.symm n).2.2.1)=as ∧
    (zipQuad ks zs as bs).map (fun n => (quadCode.symm n).2.2.2)=bs := by
  induction ks generalizing zs as bs with
  | nil =>
    have hz := List.length_eq_zero_iff.mp h1.symm
    have ha := List.length_eq_zero_iff.mp h2.symm
    have hb := List.length_eq_zero_iff.mp h3.symm
    subst zs; subst as; subst bs
    simp [zipQuad,quadCode]
  | cons k ks ih =>
    cases zs with
    | nil => simp at h1
    | cons z zs =>
      cases as with
      | nil => simp at h2
      | cons a as =>
        cases bs with
        | nil => simp at h3
        | cons b bs =>
          simp only [List.length_cons,Nat.succ.injEq] at h1 h2 h3
          obtain ⟨p0,p1,p2,p3⟩ := ih zs as bs h1 h2 h3
          simp only [zipQuad_cons,List.map_cons,Equiv.symm_apply_apply]
          exact ⟨congrArg (List.cons k) p0,congrArg (List.cons z) p1,
            congrArg (List.cons a) p2,congrArg (List.cons b) p3⟩

theorem zipQuad_recover (xs : List ℕ) :
    zipQuad (xs.map (fun n => (quadCode.symm n).1))
      (xs.map (fun n => (quadCode.symm n).2.1))
      (xs.map (fun n => (quadCode.symm n).2.2.1))
      (xs.map (fun n => (quadCode.symm n).2.2.2))=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,zipQuad_cons]
    have hq : quadCode ((quadCode.symm x).1,(quadCode.symm x).2.1,
        (quadCode.symm x).2.2.1,(quadCode.symm x).2.2.2)=x := quadCode.apply_symm_apply x
    rw [hq]
    exact congrArg (List.cons x) ih

theorem zipQuad_left (ks zs as bs : List ℕ)
    (h1 : ks.length=zs.length) (h2 : ks.length=as.length) (h3 : ks.length=bs.length) :
    (zipQuad ks zs as bs).map leftCoordinate=zipPair ks as := by
  induction ks generalizing zs as bs with
  | nil => simp [zipQuad]
  | cons k ks ih =>
    cases zs with
    | nil => simp at h1
    | cons z zs =>
      cases as with
      | nil => simp at h2
      | cons a as =>
        cases bs with
        | nil => simp at h3
        | cons b bs =>
          simp only [List.length_cons,Nat.succ.injEq] at h1 h2 h3
          simpa only [zipQuad_cons,List.map_cons,EffectiveFork.left_quad,zipPair_cons] using
            congrArg (List.cons (Nat.pair k a))
            (ih zs as bs h1 h2 h3)

theorem zipQuad_right (ks zs as bs : List ℕ)
    (h1 : ks.length=zs.length) (h2 : ks.length=as.length) (h3 : ks.length=bs.length) :
    (zipQuad ks zs as bs).map rightCoordinate=zipPair ks bs := by
  induction ks generalizing zs as bs with
  | nil => simp [zipQuad]
  | cons k ks ih =>
    cases zs with
    | nil => simp at h1
    | cons z zs =>
      cases as with
      | nil => simp at h2
      | cons a as =>
        cases bs with
        | nil => simp at h3
        | cons b bs =>
          simp only [List.length_cons,Nat.succ.injEq] at h1 h2 h3
          simpa only [zipQuad_cons,List.map_cons,EffectiveFork.right_quad,zipPair_cons] using
            congrArg (List.cons (Nat.pair k b))
            (ih zs as bs h1 h2 h3)

theorem zipPair_computable : Computable₂ zipPair := by
  have hh : Primrec (fun q : (List ℕ × List ℕ) × ℕ =>
      Nat.pair (q.1.1.getD q.2 0) (q.1.2.getD q.2 0)) :=
    Primrec₂.natPair.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    hh.to₂).to_comp

theorem zipQuad_computable : Computable (fun q : List ℕ × List ℕ × List ℕ × List ℕ =>
    zipQuad q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  zipPair_computable.comp Computable.fst (zipPair_computable.comp
    (Computable.fst.comp Computable.snd) (zipPair_computable.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (Computable.snd.comp (Computable.snd.comp Computable.snd))))

end CategoricalEssentialIncompleteness.LocalConnectedness.WordCoding
