/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerBinaryCore
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Partrec
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.FinCases

/-! # Deciding finite coverage by binary cylinders

At the maximum length of the listed words, coverage reduces to an
explicit finite test on all binary words of that length. The finite
enumeration, bound and bounded tests are primitive recursive. No
decision procedure on Cantor space is supplied as a hypothesis.
-/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteCover

def wordsStep (L : List Word) : List Word :=
  L.map (fun s => (0 : Fin 2) :: s) ++ L.map (fun s => (1 : Fin 2) :: s)

/-- Both possible first digits are enumerated, retaining the remaining
ordered digits. At depth zero the empty word is the single possibility. -/
def words : ℕ → List Word
  | 0 => [[]]
  | n + 1 => wordsStep (words n)

@[simp] theorem words_zero : words 0 = [[]] := rfl
@[simp] theorem words_succ (n : ℕ) : words (n+1) = wordsStep (words n) := rfl

theorem wordsStep_primrec : Primrec wordsStep := by
  have h₀ : Primrec (fun L : List Word => L.map (fun s => (0 : Fin 2) :: s)) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const (0 : Fin 2)) Primrec.snd).to₂
  have h₁ : Primrec (fun L : List Word => L.map (fun s => (1 : Fin 2) :: s)) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp (Primrec.const (1 : Fin 2)) Primrec.snd).to₂
  exact Primrec.list_append.comp h₀ h₁

theorem words_primrec : Primrec words := by
  apply (Primrec.nat_rec₁ ([[]] : List Word)
    (wordsStep_primrec.comp Primrec.snd).to₂).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg wordsStep ih

theorem words_computable : Computable words := words_primrec.to_comp

theorem mem_words_length {n : ℕ} {s : Word} (h : s ∈ words n) : s.length = n := by
  induction n generalizing s with
  | zero =>
    change s ∈ [[]] at h
    have hs : s = [] := List.mem_singleton.mp h
    exact hs ▸ rfl
  | succ n ih =>
    change s ∈ (words n).map (fun t => (0 : Fin 2) :: t) ++
      (words n).map (fun t => (1 : Fin 2) :: t) at h
    obtain h | h := List.mem_append.mp h
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      exact congrArg Nat.succ (ih ht)
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      exact congrArg Nat.succ (ih ht)

theorem mem_words_of_length {n : ℕ} {s : Word} (hs : s.length = n) : s ∈ words n := by
  induction n generalizing s with
  | zero =>
    have h : s = [] := List.length_eq_zero_iff.mp hs
    subst s
    exact List.mem_singleton_self []
  | succ n ih =>
    cases s with
    | nil => cases hs
    | cons b t =>
      have ht : t.length = n := Nat.succ.inj hs
      have hmem := ih ht
      fin_cases b
      · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨t,hmem,rfl⟩))
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨t,hmem,rfl⟩))

theorem mem_words_iff_length (n : ℕ) (s : Word) : s ∈ words n ↔ s.length = n :=
  ⟨mem_words_length,mem_words_of_length⟩

/-- This is a computed finite depth, including zero on an empty list. -/
def depth (L : List Word) : ℕ := L.foldr (fun s n => max s.length n) 0

@[simp] theorem depth_nil : depth [] = 0 := rfl
@[simp] theorem depth_cons (s : Word) (L : List Word) :
    depth (s :: L) = max s.length (depth L) := rfl

theorem depth_primrec : Primrec depth :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem depth_computable : Computable depth := depth_primrec.to_comp

theorem length_le_depth {s : Word} {L : List Word} (hs : s ∈ L) : s.length ≤ depth L := by
  induction L with
  | nil => cases hs
  | cons t L ih =>
    obtain rfl | hs := List.mem_cons.mp hs
    · exact le_max_left _ _
    · exact (ih hs).trans (le_max_right _ _)

/-- All quantification in this predicate is over the given finite list. -/
def coveredAt (L : List Word) (t : Word) : Prop :=
  ∃ s ∈ L,t.take s.length = s

instance coveredAt_decidable (L : List Word) (t : Word) : Decidable (coveredAt L t) :=
  inferInstanceAs (Decidable (∃ s ∈ L,t.take s.length = s))

def test (L : List Word) : Prop := ∀ t ∈ words (depth L),coveredAt L t

instance test_decidable (L : List Word) : Decidable (test L) :=
  inferInstanceAs (Decidable (∀ t ∈ words (depth L),coveredAt L t))

/-- The program searches exactly a finite list of finite binary words.
It makes no oracle queries and is total on every input list. -/
def covers (L : List Word) : Bool := decide (test L)

theorem prefix_relation_primrec : PrimrecRel (fun s t : Word => t.take s.length = s) :=
  Primrec.eq.comp
    (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
    Primrec.fst

theorem coveredAt_primrec : PrimrecRel coveredAt :=
  prefix_relation_primrec.exists_mem_list

theorem test_primrec : PrimrecPred test :=
  (coveredAt_primrec.swap.forall_mem_list).comp (words_primrec.comp depth_primrec) Primrec.id

theorem covers_primrec : Primrec covers := test_primrec.decide

theorem covers_computable : Computable covers := covers_primrec.to_comp

@[simp] theorem covers_iff_test (L : List Word) : covers L = true ↔ test L :=
  decide_eq_true_iff

/-! These elementary bitPrefix facts make the finite test equivalent to
coverage of infinite sequences. The extension is only a mathematical
witness; no coding or computability of infinite sequences is assumed. -/

theorem take_prefix (p : Bits) {m n : ℕ} (h : m ≤ n) :
    (bitPrefix p n).take m = bitPrefix p m := by
  rw [CategoricalEssentialIncompleteness.V46.Miller.prefix_take,Nat.min_eq_left h]

abbrev extension (s : Word) : Bits := CategoricalEssentialIncompleteness.V46.Miller.extend s

theorem prefix_extension (s : Word) : bitPrefix (extension s) s.length = s :=
  CategoricalEssentialIncompleteness.V46.Miller.prefix_extend s

theorem covers_iff (L : List Word) :
    covers L = true ↔ ∀ p : Bits,∃ s ∈ L,p ∈ cylinder s := by
  rw [covers_iff_test]
  constructor
  · intro h p
    have ht : bitPrefix p (depth L) ∈ words (depth L) :=
      mem_words_of_length (prefix_length p (depth L))
    obtain ⟨s,hs,hst⟩ := h (bitPrefix p (depth L)) ht
    refine ⟨s,hs,?_⟩
    change bitPrefix p s.length = s
    exact (take_prefix p (length_le_depth hs)).symm.trans hst
  · intro h t ht
    have hlen : t.length = depth L := mem_words_length ht
    obtain ⟨s,hs,hp⟩ := h (extension t)
    refine ⟨s,hs,?_⟩
    change bitPrefix (extension t) s.length = s at hp
    calc
      t.take s.length = (bitPrefix (extension t) t.length).take s.length := by
        rw [prefix_extension]
      _ = bitPrefix (extension t) s.length := take_prefix _
        (hlen.symm ▸ length_le_depth hs)
      _ = s := hp

/-- Decidability is obtained from the proved finite program. -/
def coverageDecidable (L : List Word) : Decidable (∀ p : Bits,∃ s ∈ L,p ∈ cylinder s) :=
  decidable_of_iff (covers L = true) (covers_iff L)

theorem covers_of_nil_mem {L : List Word} (h : [] ∈ L) : covers L = true := by
  apply (covers_iff L).mpr
  intro p
  exact ⟨[],h,rfl⟩

@[simp] theorem covers_nil : covers [] = false := rfl
@[simp] theorem covers_singleton_nil : covers [[]] = true := rfl

end CategoricalEssentialIncompleteness.V46.Miller.FiniteCover
