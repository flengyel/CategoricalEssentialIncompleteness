/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableWords
import Mathlib.Data.List.Chain

/-! # Finite paths enumerate the equivalence closure of a c.e. relation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableRelationPaths

def adjacentCodes : List ℕ → List ℕ
  | [] => []
  | x::xs => if xs.length=0 then [] else Nat.pair x xs.headI :: adjacentCodes xs

theorem adjacentCodes_primrec : Primrec adjacentCodes := by
  have hp : PrimrecPred (fun q : List ℕ × ℕ × List ℕ × List ℕ => q.2.2.1.length=0) :=
    Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const 0)
  have hs : Primrec (fun q : List ℕ × ℕ × List ℕ × List ℕ =>
      if q.2.2.1.length=0 then [] else
        Nat.pair q.2.1 q.2.2.1.headI :: q.2.2.2) :=
    Primrec.ite hp (Primrec.const [])
      (Primrec.list_cons.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.list_headI.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hs.to₂).of_eq (by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (if xs.length=0 then [] else Nat.pair x xs.headI :: _) = _
      exact congrArg (fun ys => if xs.length=0 then [] else Nat.pair x xs.headI::ys) ih)

@[simp] theorem adjacentCodes_cons_cons (x y : ℕ) (xs : List ℕ) :
    adjacentCodes (x::y::xs)=Nat.pair x y::adjacentCodes (y::xs) := by
  simp [adjacentCodes]

theorem isChain_iff_codes (R : ℕ → ℕ → Prop) (xs : List ℕ) :
    xs.IsChain R ↔ ∀ n ∈ adjacentCodes xs,R (Nat.unpair n).1 (Nat.unpair n).2 := by
  induction xs with
  | nil => simp [adjacentCodes]
  | cons x xs ih =>
    cases xs with
    | nil => simp [adjacentCodes]
    | cons y xs => simp only [List.isChain_cons_cons,adjacentCodes_cons_cons,
        List.forall_mem_cons,Nat.unpair_pair,ih]

theorem listAll_re {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun xs : List ℕ => ∀ x ∈ xs,p x) := by
  let X : EnumerableCarriers.Carrier := ⟨{x | p x},hp⟩
  apply (PartialLists.traverse_partrec (EnumerableCarriers.val_partrec (𝟙 X))).dom_re.of_eq
  exact PartialLists.identity_dom X

theorem isChain_re {R : ℕ → ℕ → Prop}
    (hR : REPred (fun p : ℕ × ℕ => R p.1 p.2)) : REPred (List.IsChain R) := by
  have hr := REPred.comp Computable.unpair hR
  exact (REPred.comp adjacentCodes_primrec.to_comp (listAll_re hr)).of_eq
    (fun xs => (isChain_iff_codes R xs).symm)

theorem reverse_headI (xs : List ℕ) (h : xs≠[]) : xs.reverse.headI=xs.getLast h := by
  have hh (ys : List ℕ) (hy : ys≠[]) : ys.headI=ys.head hy := by
    cases ys
    · exact False.elim (hy rfl)
    · rfl
  rw [hh _ (by simpa using h),← List.getLast_eq_head_reverse]

/-- A path records its starting vertex and its last vertex, including the
length-zero path. This is precisely reflexive transitive closure. -/
theorem reflTransGen_iff_path (R : ℕ → ℕ → Prop) (x y : ℕ) :
    Relation.ReflTransGen R x y ↔ ∃ xs : List ℕ,
      (x::xs).IsChain R ∧ (x::xs).reverse.headI=y := by
  constructor
  · intro h
    obtain ⟨xs,hxs,hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    refine ⟨xs,hxs,?_⟩
    rw [reverse_headI _ (by simp)]
    exact hl
  · rintro ⟨xs,hxs,hl⟩
    apply List.relationReflTransGen_of_exists_isChain_cons xs hxs
    rw [reverse_headI _ (by simp)] at hl
    exact hl

theorem reflTransGen_re {R : ℕ → ℕ → Prop}
    (hR : REPred (fun p : ℕ × ℕ => R p.1 p.2)) :
    REPred (fun p : ℕ × ℕ => Relation.ReflTransGen R p.1 p.2) := by
  have hc : Computable (fun p : (ℕ × ℕ) × List ℕ => p.1.1::p.2) :=
    Primrec.list_cons.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd
  have he : ComputablePred (fun p : (ℕ × ℕ) × List ℕ =>
      (p.1.1::p.2).reverse.headI=p.1.2) :=
    (Primrec.eq.comp
      (Primrec.list_headI.comp (Primrec.list_reverse.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))
      (Primrec.snd.comp Primrec.fst)).computablePred
  exact ((REPred.comp hc (isChain_re hR)).and he.to_re).projection.of_eq
    (fun p => (reflTransGen_iff_path R p.1 p.2).symm)

/-- No decidability of the relation is required: finite paths in its
symmetric edge relation enumerate exactly the generated equivalence. -/
theorem eqvGen_re {R : ℕ → ℕ → Prop}
    (hR : REPred (fun p : ℕ × ℕ => R p.1 p.2)) :
    REPred (fun p : ℕ × ℕ => Relation.EqvGen R p.1 p.2) := by
  have hs : REPred (fun p : ℕ × ℕ => Relation.SymmGen R p.1 p.2) :=
    (hR.or (REPred.comp (Computable.pair Computable.snd Computable.fst) hR)).of_eq
      (fun _ => Iff.rfl)
  exact (reflTransGen_re hs).of_eq (fun p => by rw [Relation.EqvGen.reflTransGen_symmGen])

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableRelationPaths
