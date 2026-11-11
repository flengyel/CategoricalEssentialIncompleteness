/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutTopology
public import CategoricalEssentialIncompleteness.V46MillerCutDyadicArithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # The actual image of a binary cylinder as finite closed dyadic boxes

Finite rectangular completions retain all prescribed bits. Surjectivity
at the CLOSED right endpoint uses binary expansions of 1 as well as those
of points below 1; no canonical choice of a dyadic expansion is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable Set
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Boxes

/-- Binary expansions with any specified ordered finite prefix fill its
entire CLOSED dyadic interval, including both endpoints. -/
theorem binary_interval_surjective (a : Bits) (k : ℕ) (x : ℝ)
    (hx : (numeral a k : ℝ)/(2:ℝ)^k ≤ x ∧ x ≤ ((numeral a k:ℝ)+1)/(2:ℝ)^k) :
    ∃ b : Bits, (∀ j < k, b j=a j) ∧ Real.ofDigits b=x := by
  have hp : (0:ℝ)<2^k := by positivity
  have hlo := (div_le_iff₀ hp).mp hx.1
  have hhi := (le_div_iff₀ hp).mp hx.2
  have hu : (2:ℝ)^k*x-(numeral a k:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> nlinarith
  obtain ⟨tail,_,htail⟩ := Real.ofDigits_SurjOn (b:=2) (by decide) hu
  let b : Bits := fun j => if j<k then a j else tail (j-k)
  have hprefix : ∀ j<k, b j=a j := fun j hj => by simp only [b,ite_eq_left hj]
  have hnum : numeral b k=numeral a k := numeral_congr b a k hprefix
  have hshift : (fun i => b (i+k))=tail := by
    funext i
    simp [b,show ¬i+k<k by omega]
  have he := Real.ofDigits_eq_sum_add_ofDigits b k
  rw [numeral_partial_sum,hnum,hshift,htail] at he
  refine ⟨b,hprefix,he.trans ?_⟩
  field_simp
  ring

/-- A row-major rectangular word; only its first N by N entries are used. -/
def rowDigit (b : Word) (N n j : ℕ) : Fin 2 := (b[n*N+j]?).getD 0

def row (b : Word) (N n : ℕ) : Bits := rowDigit b N n

def rowNumeral (b : Word) (N n k : ℕ) : ℕ := numeral (row b N n) k

def lowerCode (N : ℕ) (b : Word) (n : ℕ) : Dyadic.Code := (rowNumeral b N n N,N)
def upperCode (N : ℕ) (b : Word) (n : ℕ) : Dyadic.Code := (rowNumeral b N n N+1,N)

def box (N : ℕ) (b : Word) : Set Point :=
  {z | ∀ n<N, Dyadic.value (lowerCode N b n) ≤ (z n:ℝ) ∧
    (z n:ℝ) ≤ Dyadic.value (upperCode N b n)}

def Compatible (s b : Word) : Prop := ∀ k ∈ List.range s.length,
  rowDigit b s.length (Nat.unpair k).1 (Nat.unpair k).2 = (s[k]?).getD 0

instance compatible_decidable : DecidableRel Compatible := fun s b =>
  inferInstanceAs (Decidable (∀ k ∈ List.range s.length,
    rowDigit b s.length (Nat.unpair k).1 (Nat.unpair k).2 = (s[k]?).getD 0))

def rectangleWords (s : Word) : List Word :=
  (FiniteCover.words (s.length*s.length)).filter (Compatible s)

private def packRectangle (p : Bits) (N : ℕ) : Word :=
  List.ofFn (fun i : Fin (N*N) => p (Nat.pair (i.val/N) (i.val%N)))

private theorem row_packed (p : Bits) (N n j : ℕ) (hn : n<N) (hj : j<N) :
    rowDigit (packRectangle p N) N n j = p (Nat.pair n j) := by
  have hN : 0<N := by omega
  have hidx : n*N+j<N*N := by nlinarith
  have hd : (n*N+j)/N=n := by
    rw [Nat.mul_comm n N,Nat.mul_add_div hN,Nat.div_eq_of_lt hj,Nat.add_zero]
  have hm : (n*N+j)%N=j := Nat.mul_add_mod_of_lt hj
  simp [rowDigit,packRectangle,hidx,hd,hm]

private theorem packed_compatible (p : Bits) (s : Word) (hp : p ∈ cylinder s) :
    Compatible s (packRectangle p s.length) := by
  intro k hk
  have hkl : k<s.length := List.mem_range.mp hk
  have hn : (Nat.unpair k).1<s.length := (Nat.unpair_left_le k).trans_lt hkl
  have hj : (Nat.unpair k).2<s.length := (Nat.unpair_right_le k).trans_lt hkl
  rw [row_packed p s.length _ _ hn hj,Nat.pair_unpair]
  have hh := (mem_cylinder_iff p s).mp hp k hkl
  simpa only [List.getElem?_eq_getElem hkl,Option.getD_some] using hh

/-- Every rectangle compatible with s has its entire box in the actual
rho-image of [s]. This is a proved binary-prefix lifting comparison. -/
theorem box_subset_image (s b : Word) (hb : Compatible s b) :
    box s.length b ⊆ rho '' cylinder s := by
  intro z hz
  obtain ⟨p0,hp0⟩ := rho_surjective z
  have hrows : ∀ n, ∃ c : Bits, Real.ofDigits c=(z n:ℝ) ∧
      (∀ j, n<s.length → j<s.length → c j=rowDigit b s.length n j) := by
    intro n
    by_cases hn : n<s.length
    · obtain ⟨c,hc,hcv⟩ := binary_interval_surjective (row b s.length n) s.length (z n)
        (by simpa only [lowerCode,upperCode,Dyadic.value,rowNumeral,Nat.cast_add,Nat.cast_one] using hz n hn)
      exact ⟨c,hcv,fun j _ hj => hc j hj⟩
    · refine ⟨fun j => p0 (Nat.pair n j),?_,fun _ hh _ => (hn hh).elim⟩
      exact congrArg (fun w : Point => (w n:ℝ)) hp0
  choose c hc hprefix using hrows
  let p : Bits := fun k => c (Nat.unpair k).1 (Nat.unpair k).2
  have hrho : rho p=z := by
    funext n
    apply Subtype.ext
    change Real.ofDigits (fun j => c (Nat.unpair (Nat.pair n j)).1
      (Nat.unpair (Nat.pair n j)).2)=(z n:ℝ)
    simpa only [Nat.unpair_pair] using hc n
  have hps : p ∈ cylinder s := by
    apply (mem_cylinder_iff p s).mpr
    intro k hk
    have hn := (Nat.unpair_left_le k).trans_lt hk
    have hj := (Nat.unpair_right_le k).trans_lt hk
    have h := (hprefix _ _ hn hj).trans (hb k (List.mem_range.mpr hk))
    simpa only [p,List.getElem?_eq_getElem hk,Option.getD_some] using h
  exact ⟨p,hps,hrho⟩

/-- Literal image equality with the finite, explicitly enumerated dyadic
rectangles. No image-membership comparison is an assumed field. -/
theorem cylinder_image (s : Word) :
    rho '' cylinder s = ⋃ b ∈ rectangleWords s, box s.length b := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    let b := packRectangle p s.length
    have hb : b ∈ rectangleWords s := List.mem_filter.mpr
      ⟨FiniteCover.mem_words_of_length (by simp [b,packRectangle]),decide_eq_true_iff.mpr (packed_compatible p s hp)⟩
    apply Set.mem_iUnion.mpr
    refine ⟨b,Set.mem_iUnion.mpr ⟨hb,?_⟩⟩
    intro n hn
    have hrow : ∀ j<s.length, row b s.length n j=p (Nat.pair n j) :=
      fun j hj => row_packed p s.length n j hn hj
    have hnum : rowNumeral b s.length n s.length =
        numeral (fun j => p (Nat.pair n j)) s.length :=
      numeral_congr _ _ _ hrow
    simpa only [box,lowerCode,upperCode,Dyadic.value,Nat.cast_add,Nat.cast_one,hnum,rho] using
      numeral_bounds (fun j => p (Nat.pair n j)) s.length
  · intro hz
    obtain ⟨b,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hb,hz⟩ := Set.mem_iUnion.mp hz
    exact box_subset_image s b (of_decide_eq_true (List.mem_filter.mp hb).2) hz

/-- Every generated box is nonempty, including dimension zero. -/
theorem box_nonempty (N : ℕ) (b : Word) : (box N b).Nonempty := by
  let z : Point := fun n => ⟨Real.ofDigits (row b N n),Real.ofDigits_nonneg _,Real.ofDigits_le_one _⟩
  refine ⟨z,?_⟩
  intro n hn
  simpa only [lowerCode,upperCode,Dyadic.value,rowNumeral,Nat.cast_add,Nat.cast_one] using
    numeral_bounds (row b N n) N

theorem numeral_lt_pow (a : Bits) (k : ℕ) : numeral a k < 2^k := by
  induction k with
  | zero => simp [numeral]
  | succ k ih =>
    rw [numeral,pow_succ]
    have hbit := (a k).isLt
    omega

theorem endpoint_bounds (N : ℕ) (b : Word) (n : ℕ) :
    0 ≤ Dyadic.value (lowerCode N b n) ∧
    Dyadic.value (lowerCode N b n) ≤ Dyadic.value (upperCode N b n) ∧
    Dyadic.value (upperCode N b n) ≤ 1 := by
  have hp : (0:ℝ)<2^N := by positivity
  have hnum : (rowNumeral b N n N:ℝ)+1 ≤ (2:ℝ)^N := by
    exact_mod_cast Nat.succ_le_of_lt (numeral_lt_pow (row b N n) N)
  simp only [lowerCode,upperCode,Dyadic.value,Nat.cast_add,Nat.cast_one]
  refine ⟨by positivity,?_,?_⟩
  · exact (div_le_div_iff_of_pos_right hp).mpr (by linarith)
  · exact (div_le_one hp).mpr hnum

theorem box_isClosed (N : ℕ) (b : Word) : IsClosed (box N b) := by
  have he : box N b = ⋂ n : Fin N,
      {z : Point | Dyadic.value (lowerCode N b n) ≤ (z n:ℝ) ∧
        (z n:ℝ) ≤ Dyadic.value (upperCode N b n)} := by
    ext z
    simp only [box,Set.mem_ofPred_eq,Set.mem_iInter]
    exact ⟨fun h n => h n n.isLt,fun h n hn => h ⟨n,hn⟩⟩
  rw [he]
  apply isClosed_iInter
  intro n
  have hc : Continuous (fun z : Point => (z n:ℝ)) :=
    continuous_subtype_val.comp (continuous_apply (n:ℕ))
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

/-- The integer data of each box is computed by a primitive-recursive
finite loop; no Real computability class is used. -/
theorem rowDigit_primrec :
    Primrec (fun a : (Word × ℕ) × (ℕ × ℕ) => rowDigit a.1.1 a.1.2 a.2.1 a.2.2) := by
  have hi : Primrec (fun a : (Word × ℕ) × (ℕ × ℕ) => a.2.1*a.1.2+a.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)
  simpa only [rowDigit,List.getD_eq_getElem?_getD] using
    ((Primrec.list_getD (0:Fin 2)).comp (Primrec.fst.comp Primrec.fst) hi)

theorem rowNumeral_primrec :
    Primrec (fun a : ((Word × ℕ) × ℕ) × ℕ => rowNumeral a.1.1.1 a.1.1.2 a.1.2 a.2) := by
  let P := (Word × ℕ) × ℕ
  have hg : Primrec (fun a : P × (ℕ × ℕ) => (rowDigit a.1.1.1 a.1.1.2 a.1.2 a.2.1).val) :=
    Primrec.fin_val.comp (rowDigit_primrec.comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))))
  have hs : Primrec (fun a : P × (ℕ × ℕ) => 2*a.2.2+(rowDigit a.1.1.1 a.1.1.2 a.1.2 a.2.1).val) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)) hg
  refine Primrec.of_eq (Primrec.nat_rec (Primrec.const 0) hs.to₂) ?_
  intro a
  exact (numeral_eq_rec (row a.1.1.1 a.1.1.2 a.1.2) a.2).symm

theorem compatible_primrec : PrimrecRel Compatible := by
  let A := Word × Word
  have hs : Primrec (fun a : ℕ × A => a.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun a : ℕ × A => a.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun a : ℕ × A => ((a.2.2,a.2.1.length),Nat.unpair a.1)) :=
    Primrec.pair (Primrec.pair hb (Primrec.list_length.comp hs)) (Primrec.unpair.comp Primrec.fst)
  have hR : PrimrecRel (fun k : ℕ => fun a : A =>
      rowDigit a.2 a.1.length (Nat.unpair k).1 (Nat.unpair k).2 = (a.1[k]?).getD 0) :=
    Primrec.eq.comp (rowDigit_primrec.comp hc)
      ((Primrec.list_getD (0:Fin 2)).comp hs Primrec.fst)
  exact (hR.forall_mem_list.comp (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    Primrec.id).of_eq (fun _ => Iff.rfl)

theorem rectangleWords_primrec : Primrec rectangleWords :=
  ((PrimrecRel.listFilter compatible_primrec.swap).comp
    (FiniteCover.words_primrec.comp (Primrec.nat_mul.comp Primrec.list_length Primrec.list_length))
    Primrec.id).of_eq (fun _ => rfl)

abbrev BoxCode := ℕ × Word

def boxesOfCylinder (s : Word) : List BoxCode := (rectangleWords s).map (fun b => (s.length,b))
def boxesOfWords (L : List Word) : List BoxCode := L.flatMap boxesOfCylinder

def union (L : List BoxCode) : Set Point := {z | ∃ c ∈ L, z ∈ box c.1 c.2}

theorem boxesOfWords_image (L : List Word) :
    union (boxesOfWords L) = rho '' Cut.cylinderUnion L := by
  ext z
  change (∃c∈boxesOfWords L,z∈box c.1 c.2) ↔ ∃p,(∃s∈L,p∈cylinder s) ∧ rho p=z
  constructor
  · rintro ⟨c,hc,hz⟩
    obtain ⟨s,hs,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    obtain ⟨p,hps,hpz⟩ := box_subset_image s b (of_decide_eq_true (List.mem_filter.mp hb).2) hz
    exact ⟨p,⟨s,hs,hps⟩,hpz⟩
  · rintro ⟨p,⟨s,hs,hps⟩,hpz⟩
    have hz : rho p ∈ ⋃ b ∈ rectangleWords s, box s.length b := by
      rw [← cylinder_image s]
      exact ⟨p,hps,rfl⟩
    obtain ⟨b,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hb,hz⟩ := Set.mem_iUnion.mp hz
    refine ⟨(s.length,b),List.mem_flatMap.mpr ⟨s,hs,List.mem_map.mpr ⟨b,hb,rfl⟩⟩,?_⟩
    exact hpz ▸ hz

def badBoxes (e m t : ℕ) : List BoxCode :=
  boxesOfWords (Cut.complementWords (Cut.stageWords e m t))

theorem badBoxes_spec (e m t : ℕ) : union (badBoxes e m t) = Cut.badImage e m t := by
  rw [badBoxes,boxesOfWords_image,Cut.badImage,Cut.haltingStage,Cut.complement_cylinderUnion]

theorem boxesOfCylinder_primrec : Primrec boxesOfCylinder :=
  Primrec.list_map rectangleWords_primrec
    (Primrec.pair (Primrec.list_length.comp Primrec.fst) Primrec.snd).to₂

theorem boxesOfWords_primrec : Primrec boxesOfWords :=
  Primrec.list_flatMap Primrec.id (boxesOfCylinder_primrec.comp Primrec.snd).to₂

theorem badBoxes_primrec :
    Primrec (fun a : (ℕ × ℕ) × ℕ => badBoxes a.1.1 a.1.2 a.2) :=
  boxesOfWords_primrec.comp (Cut.complementWords_primrec.comp Cut.stageWords_primrec)

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Boxes
