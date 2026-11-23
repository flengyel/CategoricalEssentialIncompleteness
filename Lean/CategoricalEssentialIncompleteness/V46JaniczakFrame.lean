/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCanonical
public import CategoricalEssentialIncompleteness.V46JaniczakTransfer
public import CategoricalEssentialIncompleteness.V46JaniczakCoding

/-!
# Finite samples of the equivalence-relation models

For a bound $b$ on variable names, retain the selected finite classes of sizes at most $b$ and $b+1$ further classes with $b+1$ named elements each.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.Frame

variable {C : Set ℕ}
abbrev Point (C : Set ℕ) := (canonical C).Carrier

def small (b : ℕ) : C ⊕ ℕ → Prop
  | .inl i => i.val < b
  | .inr _ => False

def sample (b : ℕ) : Point C → Prop
  | ⟨.inl i, _⟩ => i.val < b
  | ⟨.inr k, y⟩ => k < b+1 ∧ Nat.lt (show ℕ from y) (b+1)

def center : Point C := ⟨.inr 0, (0 : ℕ)⟩

private def infinitePoint (k j : ℕ) : Point C := ⟨.inr k, j⟩

private theorem reserves (b : ℕ) :
    ∃ f : Fin (b+1) → Point C, Function.Injective (Sigma.fst ∘ f) ∧
      ∀ j, sample b (f j) ∧ ¬ small b (f j).1 := by
  let f : Fin (b+1) → Point C := fun j ↦ infinitePoint j 0
  exact ⟨f, fun i j h ↦ Fin.ext (Sum.inr.inj h),
    fun j ↦ ⟨⟨j.isLt, Nat.succ_pos _⟩, id⟩⟩

theorem fullReservoir (b : ℕ) :
    Transfer.Reservoir (Sigma.fst (β := Fiber C)) (small b) b (fun _ ↦ True) := by
  refine ⟨fun _ _ ↦ trivial, ?_, ?_⟩
  · rintro ⟨k,z⟩ - h
    cases k with
    | inl i =>
      have size : b+1 ≤ i.val+1 := by change ¬ i.val < b at h; omega
      let f : Fin (b+1) → Point C := fun j ↦ ⟨.inl i, j.castLE size⟩
      exact ⟨f, fun j k e ↦ Fin.ext (congrArg (fun t : Fin (i.val+1) ↦ t.val) (eq_of_heq (Sigma.mk.inj_iff.mp e).2)),
        fun _ ↦ ⟨trivial,rfl⟩⟩
    | inr k =>
      exact ⟨fun j ↦ infinitePoint k j,
        fun j l e ↦ Fin.ext (eq_of_heq (Sigma.mk.inj_iff.mp e).2), fun _ ↦ ⟨trivial,rfl⟩⟩
  · obtain ⟨f,h,hs⟩ := reserves (C := C) b
    exact ⟨f,h,fun j ↦ ⟨trivial,(hs j).2⟩⟩

theorem sampleReservoir (b : ℕ) :
    Transfer.Reservoir (Sigma.fst (β := Fiber C)) (small b) b (sample b) := by
  refine ⟨?_, ?_, reserves b⟩
  · rintro ⟨k,z⟩
    cases k with
    | inl => exact id
    | inr => exact False.elim
  · rintro ⟨k,z⟩ hs hl
    cases k with
    | inl i => exact (hl hs).elim
    | inr k =>
      exact ⟨fun j ↦ infinitePoint k j, fun i j e ↦ Fin.ext (eq_of_heq (Sigma.mk.inj_iff.mp e).2),
        fun j ↦ ⟨⟨hs.1,j.isLt⟩,rfl⟩⟩

def finiteCode (i j : ℕ) := Nat.pair (Nat.pair 0 i) j
def infiniteCode (k j : ℕ) := Nat.pair (Nat.pair 1 k) j

def keyCode : C ⊕ ℕ → ℕ
  | .inl i => Nat.pair 0 i.val
  | .inr k => Nat.pair 1 k

def code : Point C → ℕ
  | ⟨.inl i, j⟩ => finiteCode i.val j.val
  | ⟨.inr k, j⟩ => infiniteCode k j

theorem keyCode_injective : Function.Injective (keyCode (C := C)) := by
  rintro (i|i) (j|j) h <;> simp_all [keyCode]
  exact Subtype.ext h

theorem code_key (x : Point C) : (code x).unpair.1 = keyCode x.1 := by
  rcases x with ⟨i|k,j⟩ <;> exact congrArg Prod.fst (Nat.unpair_pair _ _)

theorem code_injective : Function.Injective (code (C := C)) := by
  rintro ⟨k,x⟩ ⟨l,y⟩ h
  have e := (code_key (C := C) ⟨k,x⟩).symm.trans ((congrArg (fun t : ℕ ↦ t.unpair.1) h).trans (code_key ⟨l,y⟩))
  have hk : k=l := keyCode_injective e
  subst l
  cases k with
  | inl i =>
    have he := (Nat.pair_eq_pair.mp (show Nat.pair (Nat.pair 0 i.val) x.val = Nat.pair (Nat.pair 0 i.val) y.val from h)).2
    exact congrArg (Sigma.mk (Sum.inl i)) (Fin.ext he)
  | inr k =>
    have he := (Nat.pair_eq_pair.mp (show Nat.pair (Nat.pair 1 k) x = Nat.pair (Nat.pair 1 k) y from h)).2
    exact congrArg (Sigma.mk (Sum.inr k)) he

def finiteRows (d : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | i+1 => finiteRows d i ++ bif d i then (List.range (i+1)).map (finiteCode i) else []

def sampleCodes (d : ℕ → Bool) (b : ℕ) : List ℕ :=
  finiteRows d b ++ (List.range (b+1)).flatMap (fun i ↦ (List.range (b+1)).map (infiniteCode i))

private theorem mem_finiteRows (d : ℕ → Bool) (b z : ℕ) :
    z ∈ finiteRows d b ↔ ∃ i < b, d i = true ∧ ∃ j < i+1, finiteCode i j = z := by
  induction b with
  | zero => simp [finiteRows]
  | succ b ih =>
    rw [finiteRows, List.mem_append, ih, Nat.exists_lt_succ_right]
    by_cases h : d b = true <;> simp [h]

theorem mem_sampleCodes {d : ℕ → Bool} (hd : ∀ i, d i = true ↔ i ∈ C) (b z : ℕ) :
    z ∈ sampleCodes d b ↔ ∃ x : Point C, sample b x ∧ code x = z := by
  simp only [sampleCodes, List.mem_append, mem_finiteRows, List.mem_flatMap, List.mem_map,
    List.mem_range, hd]
  constructor
  · rintro (⟨i,hi,hC,j,hj,e⟩ | ⟨k,hk,j,hj,e⟩)
    · exact ⟨⟨.inl ⟨i,hC⟩, (⟨j,hj⟩ : Fin (i+1))⟩,hi,e⟩
    · exact ⟨infinitePoint k j,⟨hk,hj⟩,e⟩
  · rintro ⟨⟨i|k,j⟩,h,e⟩
    · exact Or.inl ⟨i.val,h,i.property,j.val,j.isLt,e⟩
    · exact Or.inr ⟨k,h.1,j,h.2,e⟩

theorem computable_sampleCodes {d : ℕ → Bool} (hd : Computable d) : Computable (sampleCodes d) := by
  open Primrec in
  have pc : Primrec₂ finiteCode := to₂ (Primrec₂.natPair.comp (Primrec₂.natPair.comp (const 0) fst) snd)
  open Primrec in
  have pi : Primrec₂ infiniteCode := to₂ (Primrec₂.natPair.comp (Primrec₂.natPair.comp (const 1) fst) snd)
  open Primrec in
  have row : Primrec (fun i ↦ (List.range (i+1)).map (finiteCode i)) :=
    list_map (list_range.comp succ) pc
  open Computable in
  have finite : Computable (finiteRows d) := by
    have step : Computable₂ (fun (_ : ℕ) (z : ℕ × List ℕ) ↦
        z.2 ++ bif d z.1 then (List.range (z.1+1)).map (finiteCode z.1) else []) :=
      to₂ <| list_append.comp (snd.comp snd)
        ((hd.comp (fst.comp snd)).cond (row.to_comp.comp (fst.comp snd)) (const []))
    refine (nat_rec Computable.id (const []) step).of_eq fun i ↦ ?_
    induction i with
    | zero => rfl
    | succ i ih =>
      exact congrArg (fun xs ↦ xs ++ (bif d i then (List.range (i+1)).map (finiteCode i) else [])) ih
  open Primrec in
  have inf : Primrec (fun b ↦ (List.range (b+1)).flatMap (fun i ↦ (List.range (b+1)).map (infiniteCode i))) :=
    list_flatMap (list_range.comp succ) (to₂ <| list_map (list_range.comp (succ.comp fst))
      (pi.comp₂ (snd.comp₂ .left) .right))
  exact Computable.list_append.comp finite inf.to_comp

end Janiczak.Frame
