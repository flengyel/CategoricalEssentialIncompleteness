/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDyadicSeparation
public import Foundation.Vorspiel.Computability

/-! # Primitive-recursive tests for the finite dyadic certificates -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller

theorem numeral_eq_rec (b : Bits) (k : ℕ) :
    numeral b k = k.rec 0 (fun j m => 2*m+(b j).val) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun m => 2*m+(b k).val) ih

theorem wordNumeral_primrec :
    Primrec (fun t : (Word × ℕ) × ℕ => wordNumeral t.1.1 t.1.2 t.2) := by
  let P := Word × ℕ
  have hi : Primrec (fun a : P × (ℕ × ℕ) => Nat.pair a.1.2 a.2.1) :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hg : Primrec (fun a : P × (ℕ × ℕ) =>
      ((a.1.1[Nat.pair a.1.2 a.2.1]?).getD 0).val) := by
    simpa only [List.getD_eq_getElem?_getD] using
      (Primrec.fin_val.comp ((Primrec.list_getD (0 : Fin 2)).comp
        (Primrec.fst.comp Primrec.fst) hi))
  have hs : Primrec (fun a : P × (ℕ × ℕ) =>
      2*a.2.2 + ((a.1.1[Nat.pair a.1.2 a.2.1]?).getD 0).val) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)) hg
  refine Primrec.of_eq (Primrec.nat_rec (Primrec.const 0) hs.to₂) ?_
  intro t
  exact (numeral_eq_rec (wordDigits t.1.1 t.1.2) t.2).symm

theorem located_primrec :
    PrimrecPred (fun t : (Word × ℕ) × ℕ => Located t.1.1 t.1.2 t.2) := by
  have h : PrimrecRel (fun j : ℕ => fun a : Word × ℕ => Nat.pair a.2 j < a.1.length) :=
    Primrec.nat_lt.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
  exact ((h.forall_mem_list).comp (Primrec.list_range.comp Primrec.snd)
    Primrec.fst).of_eq (fun _ => by simp [Located])

theorem apartAt_primrec :
    PrimrecPred (fun t : (Word × Word) × (ℕ × ℕ) =>
      ApartAt t.1.1 t.1.2 t.2.1 t.2.2) := by
  let A := (Word × Word) × (ℕ × ℕ)
  have hu : Primrec (fun t : A => ((t.1.1,t.2.1),t.2.2)) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun t : A => ((t.1.2,t.2.1),t.2.2)) :=
    Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  have nu := wordNumeral_primrec.comp hu
  have nv := wordNumeral_primrec.comp hv
  exact (located_primrec.comp hu).and ((located_primrec.comp hv).and
    ((Primrec.nat_lt.comp (Primrec.nat_add.comp nu (Primrec.const 1)) nv).or
      (Primrec.nat_lt.comp (Primrec.nat_add.comp nv (Primrec.const 1)) nu)))

theorem apart_re : REPred (fun t : Word × Word => ∃ n k, ApartAt t.1 t.2 n k) :=
  apartAt_primrec.computablePred.to_re.projection.of_eq (fun _ =>
    ⟨fun ⟨⟨n,k⟩,h⟩ => ⟨n,k,h⟩,fun ⟨n,k,h⟩ => ⟨(n,k),h⟩⟩)

/-- All finite oracle tables are normalized, including tables whose entries
are not binary. This keeps the compiler's prefix theorem unconditional. -/
def normalizeBit (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩

def normalizeWord (l : List ℕ) : Word := l.map normalizeBit

theorem normalizeBit_primrec : Primrec normalizeBit :=
  Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))

theorem normalizeWord_primrec : Primrec normalizeWord :=
  Primrec.list_map Primrec.id (normalizeBit_primrec.comp Primrec.snd).to₂

@[simp] theorem normalizeBit_val (b : Fin 2) : normalizeBit b.val = b := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt b.isLt

@[simp] theorem normalizeWord_numericalPrefix (p : Bits) (k : ℕ) :
    normalizeWord ((bitPrefix p k).map Fin.val) = bitPrefix p k := by
  simp [normalizeWord,List.map_map,Function.comp_def]

theorem normalizeWord_prefix (l l' : List ℕ) (h : l <+: l') :
    normalizeWord l <+: normalizeWord l' := by
  obtain ⟨t,rfl⟩ := h
  exact ⟨normalizeWord t,(List.map_append ..).symm⟩

end CategoricalEssentialIncompleteness.V46.Miller
