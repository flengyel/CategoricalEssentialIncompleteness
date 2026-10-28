/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProofSearchTemplate
import Foundation.Vorspiel.Computability

/-!
# Coded objects and their arithmetic membership formulas

This module defines the object expressions generated from the number object by
binary products and coproducts.  Their external elements are natural numbers.
Products use `Nat.pair`, while coproducts use `Nat.pair value tag`, with tags
`0` and `1` for the left and right injections.

For every fixed object expression, Boolean membership is primitive recursive.
The formula `memberFormula Q` is a one-variable Sigma-one arithmetic formula
for the same predicate.  Its recursive definition uses Foundation's
`pairDef`, whose standard interpretation is exactly `Nat.pair`; it does not use
the distinct bit-interleaving `Metamath.Feferman.codePair` operation.  The
formula has compositional semantics in every model of PA, and PA proves its
constructor laws and every closed positive or negative membership decision.

Object expressions remain syntactic data.  No numerical encoding of all
expressions, typed program admissibility condition, source-guarded equality,
or categorical product or coproduct is introduced here.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition.CodedObjectMembership

/-! ## Object expressions and external membership -/

/-- Object expressions generated from the number object by binary products
and coproducts. -/
inductive STObjectCode where
  | omega
  | product (left right : STObjectCode)
  | coproduct (left right : STObjectCode)
  deriving DecidableEq, Repr

/-- The code of a product element. -/
def productCode (u v : ℕ) : ℕ := Nat.pair u v

/-- The code of a left coproduct element, with the value before the tag. -/
def coproductLeftCode (u : ℕ) : ℕ := Nat.pair u 0

/-- The code of a right coproduct element, with the value before the tag. -/
def coproductRightCode (v : ℕ) : ℕ := Nat.pair v 1

/-- Boolean membership in the natural-number realization of an object
expression. -/
def STObjectCode.member : STObjectCode → ℕ → Bool
  | .omega, _ => true
  | .product Q R, n =>
      Q.member n.unpair.1 && R.member n.unpair.2
  | .coproduct Q R, n =>
      (Q.member n.unpair.1 && n.unpair.2 == 0) ||
      (R.member n.unpair.1 && n.unpair.2 == 1)

@[simp] theorem member_omega (n : ℕ) :
    STObjectCode.member .omega n = true :=
  rfl

theorem member_product_iff (Q R : STObjectCode) (n : ℕ) :
    STObjectCode.member (.product Q R) n = true ↔
      STObjectCode.member Q n.unpair.1 = true ∧
      STObjectCode.member R n.unpair.2 = true := by
  simp only [STObjectCode.member, Bool.and_eq_true]

theorem member_coproduct_iff (Q R : STObjectCode) (n : ℕ) :
    STObjectCode.member (.coproduct Q R) n = true ↔
      (n.unpair.2 = 0 ∧ STObjectCode.member Q n.unpair.1 = true) ∨
      (n.unpair.2 = 1 ∧ STObjectCode.member R n.unpair.1 = true) := by
  simp only [STObjectCode.member, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro (⟨hQ, h0⟩ | ⟨hR, h1⟩)
    · exact Or.inl ⟨h0, hQ⟩
    · exact Or.inr ⟨h1, hR⟩
  · rintro (⟨h0, hQ⟩ | ⟨h1, hR⟩)
    · exact Or.inl ⟨hQ, h0⟩
    · exact Or.inr ⟨hR, h1⟩

theorem member_productCode_iff (Q R : STObjectCode) (u v : ℕ) :
    STObjectCode.member (.product Q R) (productCode u v) = true ↔
      STObjectCode.member Q u = true ∧
      STObjectCode.member R v = true := by
  rw [member_product_iff, productCode]
  simp only [Nat.unpair_pair]

theorem member_coproductLeftCode_iff (Q R : STObjectCode) (u : ℕ) :
    STObjectCode.member (.coproduct Q R) (coproductLeftCode u) = true ↔
      STObjectCode.member Q u = true := by
  rw [member_coproduct_iff, coproductLeftCode]
  simp only [Nat.unpair_pair]
  simp

theorem member_coproductRightCode_iff (Q R : STObjectCode) (v : ℕ) :
    STObjectCode.member (.coproduct Q R) (coproductRightCode v) = true ↔
      STObjectCode.member R v = true := by
  rw [member_coproduct_iff, coproductRightCode]
  simp only [Nat.unpair_pair]
  simp

/-- An arbitrary coproduct member has one of the two value/tag forms. -/
theorem member_coproduct_iff_exists_code
    (Q R : STObjectCode) (n : ℕ) :
    STObjectCode.member (.coproduct Q R) n = true ↔
      (∃ u, n = coproductLeftCode u ∧ STObjectCode.member Q u = true) ∨
      (∃ v, n = coproductRightCode v ∧ STObjectCode.member R v = true) := by
  constructor
  · intro h
    rcases (member_coproduct_iff Q R n).mp h with
      ⟨h0, hQ⟩ | ⟨h1, hR⟩
    · apply Or.inl
      refine ⟨n.unpair.1, ?_, hQ⟩
      simpa [coproductLeftCode, h0] using (Nat.pair_unpair n).symm
    · apply Or.inr
      refine ⟨n.unpair.1, ?_, hR⟩
      simpa [coproductRightCode, h1] using (Nat.pair_unpair n).symm
  · rintro (⟨u, rfl, hQ⟩ | ⟨v, rfl, hR⟩)
    · exact (member_coproductLeftCode_iff Q R u).mpr hQ
    · exact (member_coproductRightCode_iff Q R v).mpr hR

/-- A coproduct code with a tag other than `0` or `1` is rejected. -/
theorem member_coproduct_eq_false_of_tag_ne
    (Q R : STObjectCode) (n : ℕ)
    (h0 : n.unpair.2 ≠ 0) (h1 : n.unpair.2 ≠ 1) :
    STObjectCode.member (.coproduct Q R) n = false := by
  have h : ¬STObjectCode.member (.coproduct Q R) n = true := by
    rw [member_coproduct_iff]
    rintro (⟨ht, -⟩ | ⟨ht, -⟩)
    · exact h0 ht
    · exact h1 ht
  simpa using h

/-- Rejection of an explicitly paired invalid coproduct tag. -/
theorem member_coproductCode_eq_false_of_tag_ne
    (Q R : STObjectCode) (u t : ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    STObjectCode.member (.coproduct Q R) (Nat.pair u t) = false :=
  member_coproduct_eq_false_of_tag_ne Q R (Nat.pair u t)
    (by simpa only [Nat.unpair_pair] using h0)
    (by simpa only [Nat.unpair_pair] using h1)

/-- Membership is primitive recursive for every fixed object expression. -/
theorem primrec_member (Q : STObjectCode) :
    Primrec (STObjectCode.member Q) := by
  induction Q with
  | omega =>
      exact (Primrec.const true).of_eq (fun _ => rfl)
  | product Q R ihQ ihR =>
      have hQ : Primrec (fun n : ℕ => Q.member n.unpair.1) :=
        ihQ.comp (Primrec.fst.comp Primrec.unpair)
      have hR : Primrec (fun n : ℕ => R.member n.unpair.2) :=
        ihR.comp (Primrec.snd.comp Primrec.unpair)
      exact (Primrec₂.comp Primrec.and hQ hR).of_eq (fun _ => rfl)
  | coproduct Q R ihQ ihR =>
      have hQu : Primrec (fun n : ℕ => Q.member n.unpair.1) :=
        ihQ.comp (Primrec.fst.comp Primrec.unpair)
      have hRu : Primrec (fun n : ℕ => R.member n.unpair.1) :=
        ihR.comp (Primrec.fst.comp Primrec.unpair)
      have hTag : Primrec (fun n : ℕ => n.unpair.2) :=
        Primrec.snd.comp Primrec.unpair
      have hL : Primrec (fun n : ℕ =>
          Q.member n.unpair.1 && (n.unpair.2 == 0)) :=
        Primrec₂.comp Primrec.and hQu
          (Primrec₂.comp Primrec.beq hTag (Primrec.const 0))
      have hR : Primrec (fun n : ℕ =>
          R.member n.unpair.1 && (n.unpair.2 == 1)) :=
        Primrec₂.comp Primrec.and hRu
          (Primrec₂.comp Primrec.beq hTag (Primrec.const 1))
      exact (Primrec₂.comp Primrec.or hL hR).of_eq (fun _ => rfl)

/-- The predicate form of fixed-object primitive-recursive membership. -/
theorem primrecPred_member (Q : STObjectCode) :
    PrimrecPred (fun n => STObjectCode.member Q n = true) :=
  Primrec.eq.comp (primrec_member Q) (Primrec.const true)

/-! ## The arithmetic pairing graph -/

/-- Foundation's arithmetic graph for the pairing operation.  Its variable
order is output, left input, right input. -/
noncomputable abbrev natPairFormula : 𝚺₀.Semisentence 3 := pairDef

@[simp] theorem natPairFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (z x y : M) :
    natPairFormula.val.Evalb ![z, x, y] ↔ z = pair x y := by
  simp [natPairFormula]

/-- On standard natural numbers, `natPairFormula` represents `Nat.pair`, not
the separate Feferman bit-interleaving operation. -/
theorem natPairFormula_nat_iff (z x y : ℕ) :
    natPairFormula.val.Evalb ![z, x, y] ↔ z = Nat.pair x y := by
  simp [nat_pair_eq]

/-- The arithmetic pairing graph is total and functional in its output. -/
theorem natPairFormula_existsUnique_output
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (x y : M) :
    ∃! z : M, natPairFormula.val.Evalb ![z, x, y] := by
  refine ⟨pair x y, (natPairFormula_eval _ _ _).mpr rfl, ?_⟩
  intro z hz
  exact (natPairFormula_eval z x y).mp hz

@[simp] theorem pair_eq_pair_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (x y x' y' : M) :
    pair x y = pair x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    constructor
    · simpa only [pi₁_pair] using congrArg pi₁ h
    · simpa only [pi₂_pair] using congrArg pi₂ h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The pairing graph has a unique input pair for every output. -/
theorem natPairFormula_existsUnique_inputs
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (z : M) :
    ∃! p : M × M, natPairFormula.val.Evalb ![z, p.1, p.2] := by
  refine ⟨unpair z, ?_, ?_⟩
  · apply (natPairFormula_eval z (unpair z).1 (unpair z).2).mpr
    exact (pair_unpair z).symm
  · intro p hp
    have hp' : z = pair p.1 p.2 := (natPairFormula_eval z p.1 p.2).mp hp
    simpa only [unpair_pair] using (congrArg unpair hp').symm

/-! ## Compositional arithmetic membership -/

/-- A one-variable Sigma-one membership formula for a fixed object
expression. -/
noncomputable def memberFormula : STObjectCode → 𝚺₁.Semisentence 1
  | .omega => .mkSigma “z. ⊤”
  | .product Q R => .mkSigma
      “z. ∃ x, ∃ y, !natPairFormula.val z x y ∧
        !(memberFormula Q).val x ∧ !(memberFormula R).val y”
  | .coproduct Q R => .mkSigma
      “z. (∃ x, !natPairFormula.val z x 0 ∧ !(memberFormula Q).val x) ∨
        (∃ y, !natPairFormula.val z y 1 ∧ !(memberFormula R).val y)”

section ModelSemantics

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private noncomputable instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem memberFormula_omega_eval (z : M) :
    (memberFormula .omega).val.Evalb ![z] := by
  simp [memberFormula]

@[simp] theorem memberFormula_product_eval
    (Q R : STObjectCode) (z : M) :
    (memberFormula (.product Q R)).val.Evalb ![z] ↔
      ∃ x y : M, z = pair x y ∧
        (memberFormula Q).val.Evalb ![x] ∧
        (memberFormula R).val.Evalb ![y] := by
  simp [memberFormula]

@[simp] theorem memberFormula_coproduct_eval
    (Q R : STObjectCode) (z : M) :
    (memberFormula (.coproduct Q R)).val.Evalb ![z] ↔
      (∃ x : M, z = pair x 0 ∧ (memberFormula Q).val.Evalb ![x]) ∨
      (∃ y : M, z = pair y 1 ∧ (memberFormula R).val.Evalb ![y]) := by
  simp [memberFormula]

@[simp] theorem memberFormula_product_pair_eval
    (Q R : STObjectCode) (x y : M) :
    (memberFormula (.product Q R)).val.Evalb ![pair x y] ↔
      (memberFormula Q).val.Evalb ![x] ∧
      (memberFormula R).val.Evalb ![y] := by
  rw [memberFormula_product_eval]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hxa, hyb⟩ := (pair_eq_pair_iff x y a b).mp hab
    simpa only [hxa, hyb] using And.intro ha hb
  · rintro ⟨hx, hy⟩
    exact ⟨x, y, rfl, hx, hy⟩

@[simp] theorem memberFormula_coproduct_left_pair_eval
    (Q R : STObjectCode) (x : M) :
    (memberFormula (.coproduct Q R)).val.Evalb ![pair x 0] ↔
      (memberFormula Q).val.Evalb ![x] := by
  rw [memberFormula_coproduct_eval]
  constructor
  · rintro (⟨a, ha, hQ⟩ | ⟨b, hb, -⟩)
    · exact (pair_eq_pair_iff x 0 a 0).mp ha |>.1 ▸ hQ
    · have h01 : (0 : M) = 1 := (pair_eq_pair_iff x 0 b 1).mp hb |>.2
      exact False.elim (zero_ne_one h01)
  · intro hQ
    exact Or.inl ⟨x, rfl, hQ⟩

@[simp] theorem memberFormula_coproduct_right_pair_eval
    (Q R : STObjectCode) (y : M) :
    (memberFormula (.coproduct Q R)).val.Evalb ![pair y 1] ↔
      (memberFormula R).val.Evalb ![y] := by
  rw [memberFormula_coproduct_eval]
  constructor
  · rintro (⟨a, ha, -⟩ | ⟨b, hb, hR⟩)
    · have h10 : (1 : M) = 0 := (pair_eq_pair_iff y 1 a 0).mp ha |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · exact (pair_eq_pair_iff y 1 b 1).mp hb |>.1 ▸ hR
  · intro hR
    exact Or.inr ⟨y, rfl, hR⟩

/-- The arithmetic membership formula rejects a paired coproduct value with
an internal tag distinct from `0` and `1`. -/
theorem not_memberFormula_coproduct_pair_of_tag_ne
    (Q R : STObjectCode) (u t : M)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    ¬(memberFormula (.coproduct Q R)).val.Evalb ![pair u t] := by
  rw [memberFormula_coproduct_eval]
  rintro (⟨x, hx, -⟩ | ⟨y, hy, -⟩)
  · exact h0 ((pair_eq_pair_iff u t x 0).mp hx).2
  · exact h1 ((pair_eq_pair_iff u t y 1).mp hy).2

/-- A standard numeral satisfies the arithmetic membership formula in every
PA model exactly when the external Boolean test accepts it. -/
theorem memberFormula_numeral_iff (Q : STObjectCode) (n : ℕ) :
    (memberFormula Q).val.Evalb ![(n : M)] ↔
      STObjectCode.member Q n = true := by
  induction Q generalizing n with
  | omega => simp
  | product Q R ihQ ihR =>
      let a := n.unpair.1
      let b := n.unpair.2
      have hn : (n : M) = pair (a : M) (b : M) := by
        calc
          (n : M) = (Nat.pair a b : M) :=
            congrArg (fun k : ℕ => (k : M)) (Nat.pair_unpair n).symm
          _ = pair (a : M) (b : M) := coe_pair_eq_pair_coe a b
      rw [memberFormula_product_eval, member_product_iff]
      constructor
      · rintro ⟨x, y, hxy, hQ, hR⟩
        obtain ⟨hax, hby⟩ :=
          (pair_eq_pair_iff (a : M) (b : M) x y).mp (hn.symm.trans hxy)
        subst x
        subst y
        exact ⟨(ihQ a).mp hQ, (ihR b).mp hR⟩
      · rintro ⟨hQ, hR⟩
        exact ⟨(a : M), (b : M), hn,
          (ihQ a).mpr hQ, (ihR b).mpr hR⟩
  | coproduct Q R ihQ ihR =>
      let a := n.unpair.1
      let b := n.unpair.2
      have hn : (n : M) = pair (a : M) (b : M) := by
        calc
          (n : M) = (Nat.pair a b : M) :=
            congrArg (fun k : ℕ => (k : M)) (Nat.pair_unpair n).symm
          _ = pair (a : M) (b : M) := coe_pair_eq_pair_coe a b
      rw [memberFormula_coproduct_eval, member_coproduct_iff]
      constructor
      · rintro (⟨x, hx, hQ⟩ | ⟨y, hy, hR⟩)
        · obtain ⟨hax, hb0⟩ :=
            (pair_eq_pair_iff (a : M) (b : M) x 0).mp (hn.symm.trans hx)
          have hb0' : b = 0 := by simpa using hb0
          subst x
          exact Or.inl ⟨hb0', (ihQ a).mp hQ⟩
        · obtain ⟨hay, hb1⟩ :=
            (pair_eq_pair_iff (a : M) (b : M) y 1).mp (hn.symm.trans hy)
          have hb1' : b = 1 := by simpa using hb1
          subst y
          exact Or.inr ⟨hb1', (ihR a).mp hR⟩
      · rintro (⟨hb0, hQ⟩ | ⟨hb1, hR⟩)
        · apply Or.inl
          refine ⟨(a : M), ?_, (ihQ a).mpr hQ⟩
          have hb0' : (b : M) = 0 := by simpa using hb0
          exact hn.trans (congrArg (pair (a : M)) hb0')
        · apply Or.inr
          refine ⟨(a : M), ?_, (ihR a).mpr hR⟩
          have hb1' : (b : M) = 1 := by simpa using hb1
          exact hn.trans (congrArg (pair (a : M)) hb1')

end ModelSemantics

/-- Exact standard-natural adequacy of the arithmetic membership formula. -/
theorem memberFormula_nat_iff (Q : STObjectCode) (n : ℕ) :
    (memberFormula Q).val.Evalb (M := ℕ) ![n] ↔
      STObjectCode.member Q n = true := by
  simpa using memberFormula_numeral_iff (M := ℕ) Q n

/-! ## PA constructor laws -/

noncomputable def memberOmegaLaw : ArithmeticSentence :=
  “∀ z, !(memberFormula .omega).val z”

noncomputable def memberProductLaw (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ z, !(memberFormula (.product Q R)).val z ↔
    ∃ x, ∃ y, !natPairFormula.val z x y ∧
      !(memberFormula Q).val x ∧ !(memberFormula R).val y”

noncomputable def memberCoproductLaw (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ z, !(memberFormula (.coproduct Q R)).val z ↔
    (∃ x, !natPairFormula.val z x 0 ∧ !(memberFormula Q).val x) ∨
    (∃ y, !natPairFormula.val z y 1 ∧ !(memberFormula R).val y)”

noncomputable def memberProductPairLaw (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ x y z, !natPairFormula.val z x y →
    (!(memberFormula (.product Q R)).val z ↔
      !(memberFormula Q).val x ∧ !(memberFormula R).val y)”

noncomputable def memberCoproductLeftLaw (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ x z, !natPairFormula.val z x 0 →
    (!(memberFormula (.coproduct Q R)).val z ↔ !(memberFormula Q).val x)”

noncomputable def memberCoproductRightLaw (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ y z, !natPairFormula.val z y 1 →
    (!(memberFormula (.coproduct Q R)).val z ↔ !(memberFormula R).val y)”

noncomputable def memberCoproductInvalidTagLaw
    (Q R : STObjectCode) : ArithmeticSentence :=
  “∀ u t z, !natPairFormula.val z u t → t ≠ 0 → t ≠ 1 →
    ¬!(memberFormula (.coproduct Q R)).val z”

theorem pa_proves_memberOmegaLaw :
    𝗣𝗔 ⊢ memberOmegaLaw := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, memberOmegaLaw, memberFormula]

theorem pa_proves_memberProductLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberProductLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simp [memberProductLaw]

theorem pa_proves_memberCoproductLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberCoproductLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simp [memberCoproductLaw]

theorem pa_proves_memberProductPairLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberProductPairLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simp [memberProductPairLaw]

theorem pa_proves_memberCoproductLeftLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberCoproductLeftLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simp [memberCoproductLeftLaw]

theorem pa_proves_memberCoproductRightLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberCoproductRightLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simp [memberCoproductRightLaw]

theorem pa_proves_memberCoproductInvalidTagLaw (Q R : STObjectCode) :
    𝗣𝗔 ⊢ memberCoproductInvalidTagLaw Q R := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff]
  simpa [memberCoproductInvalidTagLaw] using
    (fun u t : M => not_memberFormula_coproduct_pair_of_tag_ne
      (M := M) Q R u t)

/-! ## Closed numeral decisions -/

@[simp] theorem memberFormula_instance_eval
    {M : Type*} [ORingStructure M] (Q : STObjectCode) (n : ℕ) :
    ((memberFormula Q).val/[n]).Evalb (M := M) ![] ↔
      (memberFormula Q).val.Evalb
        ![(ORingStructure.numeral n : M)] := by
  simp

/-- PA proves every accepted closed membership instance. -/
theorem pa_proves_member_of_true (Q : STObjectCode) (n : ℕ)
    (h : STObjectCode.member Q n = true) :
    𝗣𝗔 ⊢ (memberFormula Q).val/[n] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, memberFormula_instance_eval]
  simpa only [numeral_eq_natCast] using
    (memberFormula_numeral_iff (M := M) Q n).mpr h

/-- PA proves the negation of every rejected closed membership instance. -/
theorem pa_proves_not_member_of_false (Q : STObjectCode) (n : ℕ)
    (h : STObjectCode.member Q n = false) :
    𝗣𝗔 ⊢ ∼(memberFormula Q).val/[n] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simp only [LogicalConnective.HomClass.map_neg, memberFormula_instance_eval]
  intro hM
  have ht : STObjectCode.member Q n = true :=
    (memberFormula_numeral_iff (M := M) Q n).mp
      (by simpa only [numeral_eq_natCast] using hM)
  rw [h] at ht
  exact Bool.false_ne_true ht

/-! ## Nested-object applications -/

/-- A product whose left factor is a coproduct; this is a small application
object, not a claim of a categorical universal property. -/
def nestedExample : STObjectCode :=
  .product (.coproduct .omega .omega) .omega

@[simp] theorem nestedExample_left_member (u v : ℕ) :
    nestedExample.member (productCode (coproductLeftCode u) v) = true := by
  simp [nestedExample, member_productCode_iff,
    member_coproductLeftCode_iff]

@[simp] theorem nestedExample_right_member (u v : ℕ) :
    nestedExample.member (productCode (coproductRightCode u) v) = true := by
  simp [nestedExample, member_productCode_iff,
    member_coproductRightCode_iff]

@[simp] theorem nestedExample_invalid_tag_not_member (u v : ℕ) :
    nestedExample.member (productCode (Nat.pair u 2) v) = false := by
  simp [nestedExample, STObjectCode.member, productCode]

theorem pa_proves_nestedExample_left (u v : ℕ) :
    𝗣𝗔 ⊢ (memberFormula nestedExample).val/[
      productCode (coproductLeftCode u) v] :=
  pa_proves_member_of_true nestedExample _ (nestedExample_left_member u v)

theorem pa_proves_nestedExample_right (u v : ℕ) :
    𝗣𝗔 ⊢ (memberFormula nestedExample).val/[
      productCode (coproductRightCode u) v] :=
  pa_proves_member_of_true nestedExample _ (nestedExample_right_member u v)

theorem pa_proves_not_nestedExample_invalid_tag (u v : ℕ) :
    𝗣𝗔 ⊢ ∼(memberFormula nestedExample).val/[
      productCode (Nat.pair u 2) v] :=
  pa_proves_not_member_of_false nestedExample _
    (nestedExample_invalid_tag_not_member u v)

end FailureOfComposition.CodedObjectMembership
