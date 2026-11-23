/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalInseparability
public import Mathlib.Computability.PartrecCode

/-! # Recursive inseparability of classes of a precomplete equivalence relation -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46

open Nat.Partrec (Code)
open Denumerable Encodable

/-- A partial recursive function has a total recursive representative modulo the relation
at every input where the partial function is defined (§8.6). -/
def Precomplete (R : ℕ → ℕ → Prop) : Prop :=
  ∀ f : ℕ →. ℕ, Partrec f → ∃ h : ℕ → ℕ, Computable h ∧ ∀ n j, j ∈ f n → R (h n) j

/-- Disjoint nonempty unions of equivalence classes cannot be separated by a recursive set. -/
theorem Precomplete.inseparable_unions {R : ℕ → ℕ → Prop} (pre : Precomplete R)
    {U V : Set ℕ} (hU : U.Nonempty) (hV : V.Nonempty) (dis : Disjoint U V)
    (satU : ∀ x y, R x y → y ∈ U → x ∈ U) (satV : ∀ x y, R x y → y ∈ V → x ∈ V) :
    Numerical.RecursivelyInseparable U V := by
  classical
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  refine ⟨dis, ?_⟩
  rintro ⟨D, hD, hUD, hDV⟩
  let diag (n : ℕ) := (ofNat Code n).eval n
  have hd : Partrec diag := Code.eval_part.comp ((Computable.ofNat Code).comp Computable.id)
    Computable.id
  obtain ⟨h, hh, totalize⟩ := pre diag hd
  obtain ⟨dec, hdec, hset⟩ := ComputablePred.computable_iff.mp hD
  let flip (n : ℕ) := cond (dec (h n)) b a
  have hf : Computable flip := (hdec.comp hh).cond (Computable.const b) (Computable.const a)
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  let k := encode c
  have hdiag : flip k ∈ diag k := by
    change flip k ∈ (ofNat Code (encode c)).eval k
    rw [ofNat_encode, hc]
    exact Part.mem_some _
  have hr := totalize k (flip k) hdiag
  have hm : h k ∈ D ↔ dec (h k) = true := (congrFun hset (h k)).to_iff
  cases he : dec (h k) with
  | false =>
    have hu := satU (h k) a (by simpa [flip, he] using hr) ha
    simpa [he] using hm.mp (hUD hu)
  | true =>
    have hv := satV (h k) b (by simpa [flip, he] using hr) hb
    exact Set.disjoint_left.mp hDV (hm.mpr he) hv

/-- Two distinct classes of a precomplete equivalence relation are recursively inseparable. -/
theorem Precomplete.inseparable_classes {R : ℕ → ℕ → Prop} (pre : Precomplete R)
    (eqv : Equivalence R) {a b : ℕ} (hab : ¬ R a b) :
    Numerical.RecursivelyInseparable {x | R x a} {x | R x b} :=
  pre.inseparable_unions ⟨a, eqv.refl _⟩ ⟨b, eqv.refl _⟩
    (Set.disjoint_left.mpr fun _ hxa hxb => hab (eqv.trans (eqv.symm hxa) hxb))
    (fun _ _ hxy hya => eqv.trans hxy hya) (fun _ _ hxy hyb => eqv.trans hxy hyb)

end CategoricalEssentialIncompleteness.V46
