/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveOperations

/-! # Native primitive certificates for the actual list codes

The length code contains minimization, so its primitive certificate requires
the explicit bound furnished by the canonical list decoder. The other list
constructors use the actual composition and recursion codes unchanged.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding

def nativeTail (l : ℕ) : ℕ := (l - 1).unpair.2
def nativeDrop (l i : ℕ) : ℕ := i.rec l (fun _ prev => nativeTail prev)

@[simp] theorem nativeDrop_zero (l : ℕ) : nativeDrop l 0 = l := rfl
@[simp] theorem nativeDrop_succ (l i : ℕ) :
    nativeDrop l (i + 1) = nativeTail (nativeDrop l i) := rfl

theorem nativeTail_primrec : Primrec nativeTail :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem nativeDrop_primrec : Primrec₂ nativeDrop :=
  Primrec.nat_rec Primrec.id
    (Primrec.to₂ (nativeTail_primrec.comp (Primrec.snd.comp Primrec.snd)))

@[simp] theorem nativeTail_pack (l : List ℕ) : nativeTail (pack l) = pack l.tail := by
  cases l with
  | nil => simp [nativeTail]
  | cons x xs => simp [nativeTail]

theorem nativeDrop_pack (l : List ℕ) (i : ℕ) :
    nativeDrop (pack l) i = pack (l.drop i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [nativeDrop_succ, ih, nativeTail_pack, List.tail_drop]

theorem nativeDrop_zero_iff (l i : ℕ) :
    nativeDrop l i = 0 ↔ (Nat.natToList l).length ≤ i := by
  have he := nativeDrop_pack (Nat.natToList l) i
  rw [pack_natToList] at he
  rw [he]
  constructor
  · intro h
    apply List.drop_eq_nil_iff.mp
    exact pack_injective h
  · intro h
    rw [List.drop_eq_nil_iff.mpr h, pack_nil]

theorem computes_dropCore :
    Computes codeListDropCore (fun v => nativeDrop (v.get 1) (v.get 0)) := by
  have hc := computes_codePrec (computes_proj (0 : Fin 1))
    (computes_codeUnpair₂ (computes_codeSub (computes_proj (1 : Fin 3)) (computes_codeConst 1)))
  apply hc.of_eq
  intro v
  simp only [List.Vector.get_zero, List.Vector.get_one, List.Vector.head_cons,
    List.Vector.tail_cons, nativeDrop, nativeTail]

theorem computes_nativeDrop {n : ℕ} {dlist didx : Code n}
    {f g : List.Vector ℕ n → ℕ} (hl : Computes dlist f) (hi : Computes didx g) :
    Computes (codeListDrop dlist didx) (fun v => nativeDrop (f v) (g v)) :=
  computes_comp₂ (f := fun i l => nativeDrop l i) computes_dropCore hi hl

/-- The first zero tail is exactly the decoded length. This supplies
both a witness and every smaller failure for the literal minimization. -/
theorem computes_nativeLength {n : ℕ} {dlist : Code n}
    {f : List.Vector ℕ n → ℕ} (hl : Computes dlist f) :
    Computes (codeListLength dlist) (fun v => (Nat.natToList (f v)).length) := by
  have hdrop := computes_nativeDrop (computes_codeLift hl) computes_codeHead
  have hcheck := computes_codeInv hdrop
  have h := eval_codeRfindPos hcheck
  apply eval_of_eq h
  funext v
  simp only [List.Vector.head_cons, List.Vector.tail_cons, Part.coe_some]
  rw [Part.eq_some_iff, Nat.mem_rfind]
  constructor
  · rw [Part.mem_some_iff, eq_comm, decide_eq_true_eq]
    rw [Nat.inv_pos_iff]
    have hz : nativeDrop (f v) (Nat.natToList (f v)).length = 0 :=
      (nativeDrop_zero_iff _ _).mpr (le_refl _)
    rw [hz]
    exact Nat.lt_irrefl 0
  · intro i hi
    rw [Part.mem_some_iff, eq_comm, decide_eq_false_iff_not]
    rw [Nat.inv_pos_iff]
    have hz : nativeDrop (f v) i ≠ 0 := by
      intro hzero
      exact Nat.not_le.mpr hi ((nativeDrop_zero_iff _ _).mp hzero)
    intro hn
    exact hn (Nat.pos_of_ne_zero hz)

namespace PrimitiveTotal

theorem listNil (n : ℕ) : PrimitiveTotal (codeListNil (n := n)) := zero n

theorem listCons {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeListCons c d) := succ (pair hc hd)

theorem listHead {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codeListHead? c) :=
  ifPos hc (succ (unpair1 (sub hc (const n 1)))) (zero n)

theorem listTail {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codeListTail c) := unpair2 (sub hc (const n 1))

theorem listDrop {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeListDrop c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  exact ⟨fun v => nativeDrop (f v) (g v), computes_nativeDrop hcf hcg,
    nativeDrop_primrec.comp hpf hpg⟩

theorem listGet {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeListGet? c d) := listHead (listDrop hc hd)

theorem listLength {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codeListLength c) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  exact ⟨fun v => (Nat.natToList (f v)).length, computes_nativeLength hcf,
    Primrec.list_length.comp (Primrec.nat_natToList.comp hpf)⟩

theorem optionBind {n : ℕ} {c : Code n} {d : Code (n + 1)}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) : PrimitiveTotal (codeOptionBind c d) :=
  ifPos hc (bind (sub hc (one n)) hd) (zero n)

theorem listSnocCore {n : ℕ} {c d : Code n}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) : PrimitiveTotal (codeListSnocCore c d) :=
  prec (listCons hd (listNil n))
    (listCons
      (sub (listGet (lift (lift hc))
        (sub (listLength (lift (lift hc))) (succ (proj 0)))) (const (n + 2) 1))
      (proj 1))

theorem listSnoc {n : ℕ} {c d : Code n}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) : PrimitiveTotal (codeListSnoc c d) :=
  bind (listLength hc) (listSnocCore hc hd)

end PrimitiveTotal
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding
