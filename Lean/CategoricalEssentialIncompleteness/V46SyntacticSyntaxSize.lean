/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoding

/-! # Every ordered child has smaller literal node count than its constructor -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

/-- The bound applies to every recursive child word, retaining the
finite polynomial's complete nested arity and sum-tag structure. -/
def childSizeGraph : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => .mkSigma “n u. ∃ l, !lenDef.val l u ∧ l < n”
  | .formula => .mkSigma “n u. ∃ l, !lenDef.val l u ∧ l < n”
  | .coefficient _ => .mkSigma “n u. 0 = 0”
  | .unit => .mkSigma “n u. 0 = 0”
  | .product a b =>
      let A := childSizeGraph a
      let B := childSizeGraph b
      .mkSigma “n u. ∃ x y, !pairDef.val u x y ∧ !A.val n x ∧ !B.val n y”
  | .sum a b =>
      let A := childSizeGraph a
      let B := childSizeGraph b
      .mkSigma “n u. ∃ x k, !pairDef.val u x k ∧
        ((k = 0 ∧ !A.val n x) ∨ (k ≠ 0 ∧ !B.val n x))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance syntaxSizeDecidableEq : DecidableEq M := Classical.decEq M

noncomputable def ChildSize : RawPolynomial → M → M → Prop
  | .term, n, u => len u < n
  | .formula, n, u => len u < n
  | .coefficient _, _, _ => True
  | .unit, _, _ => True
  | .product a b, n, u => ChildSize a n (π₁ u) ∧ ChildSize b n (π₂ u)
  | .sum a b, n, u => if π₂ u = 0 then ChildSize a n (π₁ u) else ChildSize b n (π₁ u)

@[simp] theorem childSizeGraph_eval (q : RawPolynomial) (n u : M) :
    (childSizeGraph q).val.Evalb ![n, u] ↔ ChildSize q n u := by
  induction q generalizing u with
  | term => simp [childSizeGraph, ChildSize]
  | formula => simp [childSizeGraph, ChildSize]
  | coefficient C => simp [childSizeGraph, ChildSize]
  | unit => simp [childSizeGraph, ChildSize]
  | product a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, u = ⟪x, y⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      simp [childSizeGraph, ChildSize, ia, ib]
  | sum a b ia ib =>
      obtain ⟨x, k, rfl⟩ : ∃ x k : M, u = ⟪x, k⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      by_cases hk : k = 0 <;> simp [childSizeGraph, ChildSize, ia, ib, hk]

theorem ChildSize.mono (q : RawPolynomial) (n m u : M)
    (hnm : n ≤ m) (h : ChildSize q n u) : ChildSize q m u := by
  induction q generalizing u with
  | term => exact lt_of_lt_of_le h hnm
  | formula => exact lt_of_lt_of_le h hnm
  | coefficient C => trivial
  | unit => trivial
  | product a b ia ib => exact ⟨ia (π₁ u) h.1, ib (π₂ u) h.2⟩
  | sum a b ia ib =>
      by_cases hk : π₂ u = 0
      · exact (by simpa [ChildSize, hk] using ia (π₁ u) (by simpa [ChildSize, hk] using h))
      · exact (by simpa [ChildSize, hk] using ib (π₁ u) (by simpa [ChildSize, hk] using h))

/-- Since a constructor appends one actual node record, every recursive
child has strictly smaller numerical node count, in every PA model. -/
theorem children_smaller (formula : Bool) (q : RawPolynomial) (u : M) :
    (childSizeGraph q).val.Evalb ![len (constructor formula q u), u] := by
  rw [childSizeGraph_eval, constructor_length]
  induction q generalizing u with
  | term => simp [ChildSize, childrenWord]
  | formula => simp [ChildSize, childrenWord]
  | coefficient C => trivial
  | unit => trivial
  | product a b ia ib =>
      have ha := ia (π₁ u)
      have hb := ib (π₂ u)
      have hal : len (childrenWord a (π₁ u)) + 1 ≤
          len (Words.append (childrenWord a (π₁ u)) (childrenWord b (π₂ u))) + 1 := by
        rw [Words.len_append]
        have h : len (childrenWord a (π₁ u)) ≤
            len (childrenWord a (π₁ u)) + len (childrenWord b (π₂ u)) :=
          le_iff_exists_add.mpr ⟨len (childrenWord b (π₂ u)), rfl⟩
        simpa only [add_comm] using add_le_add_right h 1
      have hbl : len (childrenWord b (π₂ u)) + 1 ≤
          len (Words.append (childrenWord a (π₁ u)) (childrenWord b (π₂ u))) + 1 := by
        rw [Words.len_append, add_comm (len (childrenWord a (π₁ u)))]
        have h : len (childrenWord b (π₂ u)) ≤
            len (childrenWord b (π₂ u)) + len (childrenWord a (π₁ u)) :=
          le_iff_exists_add.mpr ⟨len (childrenWord a (π₁ u)), rfl⟩
        simpa only [add_comm] using add_le_add_right h 1
      exact ⟨ChildSize.mono a _ _ _ hal ha, ChildSize.mono b _ _ _ hbl hb⟩
  | sum a b ia ib =>
      by_cases hk : π₂ u = 0
      · simpa [ChildSize, childrenWord, hk] using ia (π₁ u)
      · simpa [ChildSize, childrenWord, hk] using ib (π₁ u)

/-- A finite polynomial compares two graph-defined child maps by
applying the supplied comparison only to strictly smaller child words.
This is the finite arity step used in numerical node-count induction. -/
theorem mapRaw_compare (P : SyntacticPredicates.Carrier)
    (hT hF gT gF : TernaryGraph) (q : RawPolynomial) (n p u v w : M)
    (hsize : (childSizeGraph q).val.Evalb ![n, u])
    (hterm : ∀ child x y : M, len child < n → hT.val.Evalb ![p, child, x] →
      gT.val.Evalb ![p, child, y] → x = y)
    (hformula : ∀ child x y : M, len child < n → hF.val.Evalb ![p, child, x] →
      gF.val.Evalb ![p, child, y] → x = y)
    (hv : (mapRaw P hT hF q).val.Evalb ![p, u, v])
    (hw : (mapRaw P gT gF q).val.Evalb ![p, u, w]) : v = w := by
  induction q generalizing u v w with
  | term => exact hterm u v w (by simpa [ChildSize] using hsize) hv hw
  | formula => exact hformula u v w (by simpa [ChildSize] using hsize) hv hw
  | coefficient C =>
      have hv' : P.val.Evalb ![p] ∧ C.val.Evalb ![u] ∧ v = u := by simpa [mapRaw] using hv
      have hw' : P.val.Evalb ![p] ∧ C.val.Evalb ![u] ∧ w = u := by simpa [mapRaw] using hw
      exact hv'.2.2.trans hw'.2.2.symm
  | unit =>
      have hv' : P.val.Evalb ![p] ∧ u = 0 ∧ v = 0 := by simpa [mapRaw] using hv
      have hw' : P.val.Evalb ![p] ∧ u = 0 ∧ w = 0 := by simpa [mapRaw] using hw
      exact hv'.2.2.trans hw'.2.2.symm
  | product a b ia ib =>
      obtain ⟨x, y, r, s, hu, rfl, hr, hs⟩ := (mapRaw_product_eval P hT hF a b p u v).mp hv
      obtain ⟨x', y', r', s', hu', rfl, hr', hs'⟩ := (mapRaw_product_eval P gT gF a b p u w).mp hw
      obtain ⟨hxx, hyy⟩ := (pair_eq_pair_iff _ _ _ _).mp (hu.symm.trans hu')
      subst x'
      subst y'
      have hsz : (childSizeGraph a).val.Evalb ![n, x] ∧ (childSizeGraph b).val.Evalb ![n, y] := by
        simpa [hu, ChildSize] using hsize
      rw [ia x r r' hsz.1 hr hr', ib y s s' hsz.2 hs hs']
  | sum a b ia ib =>
      rcases (mapRaw_sum_eval P hT hF a b p u v).mp hv with
        ⟨x, r, hu, rfl, hr⟩ | ⟨y, s, hu, rfl, hs⟩
      · rcases (mapRaw_sum_eval P gT gF a b p u w).mp hw with
          ⟨x', r', hu', rfl, hr'⟩ | ⟨y', s', hu', _, _⟩
        · have hxx : x = x' := by simpa using hu.symm.trans hu'
          subst x'
          have hsz : (childSizeGraph a).val.Evalb ![n, x] := by
            simpa [hu, ChildSize] using hsize
          rw [ia x r r' hsz hr hr']
        · have hz := congrArg (pi₂ : M → M) (hu.symm.trans hu')
          simp at hz
      · rcases (mapRaw_sum_eval P gT gF a b p u w).mp hw with
          ⟨x', r', hu', _, _⟩ | ⟨y', s', hu', rfl, hs'⟩
        · have hz := congrArg (pi₂ : M → M) (hu.symm.trans hu')
          simp at hz
        · have hyy : y = y' := by simpa using hu.symm.trans hu'
          subst y'
          have hsz : (childSizeGraph b).val.Evalb ![n, y] := by
            simpa [hu, ChildSize] using hsize
          rw [ib y s s' hsz hs hs']

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
