/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Foundation.FirstOrder.Arithmetic.Schemata
import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Primitive-recursive substitution of numerals into a fixed formula

For a fixed arithmetic formula, its syntax after substituting two or three
numerals is primitive recursive in those numerals.  The result concerns the
actual `Encodable` syntax, rather than a separate numbering of formulas.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace Arith.FixedFormulaNumeralSubstitution

private abbrev ATerm (n : ℕ) := ArithmeticSemiterm Empty n

private def zeroTerm (n : ℕ) : ATerm n := (↑(0 : ℕ) : ATerm n)

private def oneTerm (n : ℕ) : ATerm n := (↑(1 : ℕ) : ATerm n)

private def addOneTerm (n : ℕ) (t : ATerm n) : ATerm n :=
  Semiterm.func Language.Add.add ![t, oneTerm n]

private lemma addOperator (n : ℕ) (v : Fin 2 → ATerm n) :
    (Semiterm.Operator.Add.add (L := ℒₒᵣ)).operator v =
      Semiterm.func Language.Add.add v := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  congr 1

private lemma addOneTerm_numeral (n z : ℕ) :
    addOneTerm n (↑(z + 1) : ATerm n) = (↑(z + 2) : ATerm n) := by
  have h : ((↑(z + 2) : ATerm n)) =
      Semiterm.func Language.Add.add ![(↑(z + 1) : ATerm n), oneTerm n] := by
    change (Semiterm.Operator.numeral ℒₒᵣ (z + 2)).operator ![] =
      Semiterm.func Language.Add.add ![(↑(z + 1) : ATerm n), oneTerm n]
    rw [Semiterm.Operator.numeral_add_two, Semiterm.Operator.operator_comp,
      ← addOperator n]
    congr 1
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  simp only [addOneTerm]
  exact h.symm

private def addOneCode (n : ℕ) (a : ℕ) : ℕ :=
  Nat.pair 2
    (Nat.pair 2
      (Nat.pair (Encodable.encode (Language.Add.add : (ℒₒᵣ : Language).Func 2))
        (Nat.pair a (Nat.pair (Encodable.encode (oneTerm n)) 0 + 1) + 1))) + 1

private lemma encode_addOneTerm (n : ℕ) (t : ATerm n) :
    Encodable.encode (addOneTerm n t) = addOneCode n (Encodable.encode t) := by
  simp [addOneTerm, addOneCode, Semiterm.encode_eq_toNat, Semiterm.toNat_func,
    Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail]

private lemma primrec_addOneCode (n : ℕ) : Primrec (addOneCode n) := by
  have h1 : Primrec (fun a : ℕ =>
      Nat.pair a (Nat.pair (Encodable.encode (oneTerm n)) 0 + 1) + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const _))
  have h2 := Primrec₂.natPair.comp
    (Primrec.const (Encodable.encode (Language.Add.add : (ℒₒᵣ : Language).Func 2))) h1
  have h3 := Primrec₂.natPair.comp (Primrec.const 2) h2
  have h4 := Primrec₂.natPair.comp (Primrec.const 2) h3
  exact Primrec.succ.comp h4

private lemma primrec_addOneTerm (n : ℕ) : Primrec (addOneTerm n) :=
  Primrec.encode_iff.mp
    (((primrec_addOneCode n).comp Primrec.encode).of_eq
      (fun t => (encode_addOneTerm n t).symm))

private lemma primrec_numeralSucc (n : ℕ) :
    Primrec (fun k : ℕ => (↑(k + 1) : ATerm n)) := by
  have hstep : Primrec₂ (fun (_ : ℕ) (t : ATerm n) => addOneTerm n t) :=
    (primrec_addOneTerm n).comp Primrec.snd
  refine (Primrec.nat_rec₁ (oneTerm n) hstep).of_eq ?_
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change addOneTerm n
        (Nat.rec (motive := fun _ => ATerm n) (oneTerm n)
          (fun _ t => addOneTerm n t) k) = (↑(k + 2) : ATerm n)
      rw [ih]
      exact addOneTerm_numeral n k

/-- The arithmetic numeral term is primitive recursive in its value, at every
fixed number of free variables. -/
theorem primrec_arithmeticNumeral (n : ℕ) :
    Primrec (fun x : ℕ => (↑x : ArithmeticSemiterm Empty n)) := by
  refine (Primrec.nat_casesOn₁ (zeroTerm n) (primrec_numeralSucc n)).of_eq ?_
  intro x
  cases x with
  | zero => rfl
  | succ k => rfl

private def func₂Code (c a b : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair 2 (Nat.pair c (Nat.pair a (Nat.pair b 0 + 1) + 1))) + 1

private lemma encode_func₂ {n : ℕ} (f : (ℒₒᵣ : Language).Func 2)
    (a b : ArithmeticSemiterm Empty n) :
    Encodable.encode (Semiterm.func f ![a, b]) =
      func₂Code (Encodable.encode f) (Encodable.encode a) (Encodable.encode b) := by
  simp [func₂Code, Semiterm.encode_eq_toNat, Semiterm.toNat_func,
    Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail]

private lemma primrec_func₂Code (c : ℕ) : Primrec₂ (func₂Code c) := by
  have h1 : Primrec₂ (fun a b : ℕ => Nat.pair a (Nat.pair b 0 + 1) + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst
      (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))))
  have h2 := Primrec₂.natPair.comp (Primrec.const c) h1
  have h3 := Primrec₂.natPair.comp (Primrec.const 2) h2
  have h4 := Primrec₂.natPair.comp (Primrec.const 2) h3
  exact Primrec.succ.comp h4

private theorem primrec_func₂ {A : Type} [Primcodable A] {n : ℕ}
    (f : (ℒₒᵣ : Language).Func 2)
    {g h : A → ArithmeticSemiterm Empty n}
    (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x : A => Semiterm.func f ![g x, h x]) := by
  refine Primrec.encode_iff.mp ?_
  refine ((primrec_func₂Code (Encodable.encode f)).comp
    (Primrec.encode.comp hg) (Primrec.encode.comp hh)).of_eq ?_
  intro x
  exact (encode_func₂ f (g x) (h x)).symm

private theorem primrec_rew_fixedArithmeticTerm {A : Type} [Primcodable A]
    {n m : ℕ} (omega : A → Rew ℒₒᵣ Empty n Empty m)
    (homega : ∀ i : Fin n,
      Primrec (fun x : A => omega x (#i : ArithmeticSemiterm Empty n))) :
    ∀ t : ArithmeticSemiterm Empty n, Primrec (fun x : A => omega x t) := by
  intro t
  induction t with
  | bvar i => exact homega i
  | fvar e => exact e.elim
  | func f v ih =>
      cases f with
      | zero =>
          refine (Primrec.const
            (Semiterm.func Language.ORing.Func.zero
              (![] : Fin 0 → ArithmeticSemiterm Empty m))).of_eq ?_
          intro x
          simp only [Rew.func]
          congr 1
          funext i
          exact i.elim0
      | one =>
          refine (Primrec.const
            (Semiterm.func Language.ORing.Func.one
              (![] : Fin 0 → ArithmeticSemiterm Empty m))).of_eq ?_
          intro x
          simp only [Rew.func]
          congr 1
          funext i
          exact i.elim0
      | add =>
          refine (primrec_func₂ Language.ORing.Func.add (ih 0) (ih 1)).of_eq ?_
          intro x
          simp only [Rew.func]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
      | mul =>
          refine (primrec_func₂ Language.ORing.Func.mul (ih 0) (ih 1)).of_eq ?_
          intro x
          simp only [Rew.func]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl

private def CoordShape {A : Type} [Primcodable A] {n m : ℕ}
    (omega : A → Rew ℒₒᵣ Empty n Empty m) : Prop :=
  ∀ i : Fin n,
    (∃ j : Fin m, ∀ x : A, omega x (#i) = #j) ∨
    (∃ f : A → ℕ, Primrec f ∧
      ∀ x : A, omega x (#i) = (↑(f x) : ArithmeticSemiterm Empty m))

private lemma CoordShape.primrec {A : Type} [Primcodable A] {n m : ℕ}
    {omega : A → Rew ℒₒᵣ Empty n Empty m}
    (h : CoordShape omega) (i : Fin n) :
    Primrec (fun x : A => omega x (#i : ArithmeticSemiterm Empty n)) := by
  rcases h i with ⟨j, hj⟩ | ⟨f, hf, hformula⟩
  · exact (Primrec.const (#j : ArithmeticSemiterm Empty m)).of_eq
      (fun x => (hj x).symm)
  · exact ((primrec_arithmeticNumeral m).comp hf).of_eq
      (fun x => (hformula x).symm)

private lemma CoordShape.q {A : Type} [Primcodable A] {n m : ℕ}
    {omega : A → Rew ℒₒᵣ Empty n Empty m} (h : CoordShape omega) :
    CoordShape (fun x => (omega x).q) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact Or.inl ⟨0, fun x => by simp⟩
  · intro j
    rcases h j with ⟨k, hk⟩ | ⟨f, hf, hformula⟩
    · refine Or.inl ⟨k.succ, fun x => ?_⟩
      simp only [Rew.q_bvar_succ, hk x]
      simp
    · refine Or.inr ⟨f, hf, fun x => ?_⟩
      simp only [Rew.q_bvar_succ, hformula x]
      simp

private def rel₂Code (tag c a b : ℕ) : ℕ :=
  Nat.pair tag
    (Nat.pair 2
      (Nat.pair c
        (Nat.pair a (Nat.pair b 0 + 1) + 1))) + 1

private lemma primrec_rel₂Code (tag c : ℕ) : Primrec₂ (rel₂Code tag c) := by
  have h1 : Primrec₂ (fun a b : ℕ => Nat.pair a (Nat.pair b 0 + 1) + 1) :=
    Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst
      (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))))
  have h2 := Primrec₂.natPair.comp (Primrec.const c) h1
  have h3 := Primrec₂.natPair.comp (Primrec.const 2) h2
  have h4 := Primrec₂.natPair.comp (Primrec.const tag) h3
  exact Primrec.succ.comp h4

private lemma encode_rel₂ {n : ℕ} (r : (ℒₒᵣ : Language).Rel 2)
    (a b : ArithmeticSemiterm Empty n) :
    Encodable.encode (Semiformula.rel r ![a, b]) =
      rel₂Code 0 (Encodable.encode r) (Encodable.encode a) (Encodable.encode b) := by
  simp [rel₂Code, Semiformula.encode_rel, Matrix.vecToNat,
    Matrix.vecHead, Matrix.vecTail]

private lemma encode_nrel₂ {n : ℕ} (r : (ℒₒᵣ : Language).Rel 2)
    (a b : ArithmeticSemiterm Empty n) :
    Encodable.encode (Semiformula.nrel r ![a, b]) =
      rel₂Code 1 (Encodable.encode r) (Encodable.encode a) (Encodable.encode b) := by
  simp [rel₂Code, Semiformula.encode_nrel, Matrix.vecToNat,
    Matrix.vecHead, Matrix.vecTail]

private lemma primrec_relFormula {A : Type} [Primcodable A] {n : ℕ}
    (r : (ℒₒᵣ : Language).Rel 2)
    {g h : A → ArithmeticSemiterm Empty n}
    (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x : A => Semiformula.rel r ![g x, h x]) := by
  refine Primrec.encode_iff.mp ?_
  refine ((primrec_rel₂Code 0 (Encodable.encode r)).comp
    (Primrec.encode.comp hg) (Primrec.encode.comp hh)).of_eq ?_
  intro x
  exact (encode_rel₂ r (g x) (h x)).symm

private lemma primrec_nrelFormula {A : Type} [Primcodable A] {n : ℕ}
    (r : (ℒₒᵣ : Language).Rel 2)
    {g h : A → ArithmeticSemiterm Empty n}
    (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x : A => Semiformula.nrel r ![g x, h x]) := by
  refine Primrec.encode_iff.mp ?_
  refine ((primrec_rel₂Code 1 (Encodable.encode r)).comp
    (Primrec.encode.comp hg) (Primrec.encode.comp hh)).of_eq ?_
  intro x
  exact (encode_nrel₂ r (g x) (h x)).symm

private def binCode (tag a b : ℕ) : ℕ := Nat.pair tag (Nat.pair a b) + 1

private lemma primrec_binCode (tag : ℕ) : Primrec₂ (binCode tag) := by
  have h1 : Primrec₂ (fun a b : ℕ => Nat.pair a b) := Primrec₂.natPair
  have h2 := Primrec₂.natPair.comp (Primrec.const tag) h1
  exact Primrec.succ.comp h2

private lemma encode_andFormula {n : ℕ}
    (phi psi : ArithmeticSemiformula Empty n) :
    Encodable.encode (phi ⋏ psi) =
      binCode 4 (Encodable.encode phi) (Encodable.encode psi) := by
  simp [binCode, Semiformula.encode_and, ← Semiformula.encode_eq_toNat]

private lemma encode_orFormula {n : ℕ}
    (phi psi : ArithmeticSemiformula Empty n) :
    Encodable.encode (phi ⋎ psi) =
      binCode 5 (Encodable.encode phi) (Encodable.encode psi) := by
  simp [binCode, Semiformula.encode_or, ← Semiformula.encode_eq_toNat]

private lemma primrec_andFormula {A : Type} [Primcodable A] {n : ℕ}
    {g h : A → ArithmeticSemiformula Empty n}
    (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x : A => g x ⋏ h x) := by
  refine Primrec.encode_iff.mp ?_
  refine ((primrec_binCode 4).comp
    (Primrec.encode.comp hg) (Primrec.encode.comp hh)).of_eq ?_
  intro x
  exact (encode_andFormula (g x) (h x)).symm

private lemma primrec_orFormula {A : Type} [Primcodable A] {n : ℕ}
    {g h : A → ArithmeticSemiformula Empty n}
    (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x : A => g x ⋎ h x) := by
  refine Primrec.encode_iff.mp ?_
  refine ((primrec_binCode 5).comp
    (Primrec.encode.comp hg) (Primrec.encode.comp hh)).of_eq ?_
  intro x
  exact (encode_orFormula (g x) (h x)).symm

private def quantCode (tag a : ℕ) : ℕ := Nat.pair tag a + 1

private lemma primrec_quantCode (tag : ℕ) : Primrec (quantCode tag) :=
  Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag) Primrec.id)

private lemma encode_allFormula {n : ℕ}
    (phi : ArithmeticSemiformula Empty (n + 1)) :
    Encodable.encode (∀¹ phi : ArithmeticSemiformula Empty n) =
      quantCode 6 (Encodable.encode phi) := by
  simp [quantCode, Semiformula.encode_all, ← Semiformula.encode_eq_toNat]

private lemma encode_exsFormula {n : ℕ}
    (phi : ArithmeticSemiformula Empty (n + 1)) :
    Encodable.encode (∃¹ phi : ArithmeticSemiformula Empty n) =
      quantCode 7 (Encodable.encode phi) := by
  simp [quantCode, Semiformula.encode_ex, ← Semiformula.encode_eq_toNat]

private lemma primrec_allFormula {n : ℕ} :
    Primrec (fun phi : ArithmeticSemiformula Empty (n + 1) =>
      (∀¹ phi : ArithmeticSemiformula Empty n)) :=
  Primrec.encode_iff.mp
    (((primrec_quantCode 6).comp Primrec.encode).of_eq
      (fun phi => (encode_allFormula phi).symm))

private lemma primrec_exsFormula {n : ℕ} :
    Primrec (fun phi : ArithmeticSemiformula Empty (n + 1) =>
      (∃¹ phi : ArithmeticSemiformula Empty n)) :=
  Primrec.encode_iff.mp
    (((primrec_quantCode 7).comp Primrec.encode).of_eq
      (fun phi => (encode_exsFormula phi).symm))

/-! ### Primitive-recursive logical constructors on variable formulas -/

/-- The numerical action of negation on a classical formula code.  Zero and
malformed constructor tags are sent to zero; only the behavior on actual
formula codes is used below. -/
def formulaNegCode : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let tag := e.unpair.1
      let c := e.unpair.2
      if tag = 0 then Nat.pair 1 c + 1
      else if tag = 1 then Nat.pair 0 c + 1
      else if tag = 2 then Nat.pair 3 c + 1
      else if tag = 3 then Nat.pair 2 c + 1
      else if tag = 4 then
        Nat.pair 5
          (Nat.pair (formulaNegCode c.unpair.1)
            (formulaNegCode c.unpair.2)) + 1
      else if tag = 5 then
        Nat.pair 4
          (Nat.pair (formulaNegCode c.unpair.1)
            (formulaNegCode c.unpair.2)) + 1
      else if tag = 6 then Nat.pair 7 (formulaNegCode c) + 1
      else if tag = 7 then Nat.pair 6 (formulaNegCode c) + 1
      else 0
termination_by e => e
decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    first
    | exact le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
    | exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
    | exact Nat.unpair_right_le _

private def formulaNegStep (history : List ℕ) : Option ℕ :=
  Nat.casesOn history.length (some 0) fun e =>
    let tag := e.unpair.1
    let c := e.unpair.2
    some <|
      if tag = 0 then Nat.pair 1 c + 1
      else if tag = 1 then Nat.pair 0 c + 1
      else if tag = 2 then Nat.pair 3 c + 1
      else if tag = 3 then Nat.pair 2 c + 1
      else if tag = 4 then
        Nat.pair 5
          (Nat.pair (history.getD c.unpair.1 0)
            (history.getD c.unpair.2 0)) + 1
      else if tag = 5 then
        Nat.pair 4
          (Nat.pair (history.getD c.unpair.1 0)
            (history.getD c.unpair.2 0)) + 1
      else if tag = 6 then Nat.pair 7 (history.getD c 0) + 1
      else if tag = 7 then Nat.pair 6 (history.getD c 0) + 1
      else 0

private theorem primrec_formulaNegStep : Primrec formulaNegStep := by
  have hstep : Primrec (fun x : List ℕ × ℕ =>
      some <|
        if x.2.unpair.1 = 0 then Nat.pair 1 x.2.unpair.2 + 1
        else if x.2.unpair.1 = 1 then Nat.pair 0 x.2.unpair.2 + 1
        else if x.2.unpair.1 = 2 then Nat.pair 3 x.2.unpair.2 + 1
        else if x.2.unpair.1 = 3 then Nat.pair 2 x.2.unpair.2 + 1
        else if x.2.unpair.1 = 4 then
          Nat.pair 5
            (Nat.pair (x.1.getD x.2.unpair.2.unpair.1 0)
              (x.1.getD x.2.unpair.2.unpair.2 0)) + 1
        else if x.2.unpair.1 = 5 then
          Nat.pair 4
            (Nat.pair (x.1.getD x.2.unpair.2.unpair.1 0)
              (x.1.getD x.2.unpair.2.unpair.2 0)) + 1
        else if x.2.unpair.1 = 6 then
          Nat.pair 7 (x.1.getD x.2.unpair.2 0) + 1
        else if x.2.unpair.1 = 7 then
          Nat.pair 6 (x.1.getD x.2.unpair.2 0) + 1
        else 0) := by
    have he : Primrec (fun x : List ℕ × ℕ => x.2) := Primrec.snd
    have hu := Primrec.unpair.comp he
    have htag : Primrec (fun x : List ℕ × ℕ => x.2.unpair.1) :=
      Primrec.fst.comp hu
    have hc : Primrec (fun x : List ℕ × ℕ => x.2.unpair.2) :=
      Primrec.snd.comp hu
    have hcu := Primrec.unpair.comp hc
    have hcl : Primrec (fun x : List ℕ × ℕ => x.2.unpair.2.unpair.1) :=
      Primrec.fst.comp hcu
    have hcr : Primrec (fun x : List ℕ × ℕ => x.2.unpair.2.unpair.2) :=
      Primrec.snd.comp hcu
    have hgetl : Primrec (fun x : List ℕ × ℕ =>
        x.1.getD x.2.unpair.2.unpair.1 0) :=
      (Primrec.list_getD 0).comp Primrec.fst hcl
    have hgetr : Primrec (fun x : List ℕ × ℕ =>
        x.1.getD x.2.unpair.2.unpair.2 0) :=
      (Primrec.list_getD 0).comp Primrec.fst hcr
    have hgetc : Primrec (fun x : List ℕ × ℕ =>
        x.1.getD x.2.unpair.2 0) :=
      (Primrec.list_getD 0).comp Primrec.fst hc
    have hnode (tag : ℕ) (payload : (List ℕ × ℕ) → ℕ)
        (hpayload : Primrec payload) :
        Primrec (fun x => Nat.pair tag (payload x) + 1) :=
      Primrec.succ.comp
        (Primrec₂.natPair.comp (Primrec.const tag) hpayload)
    have hbinary (tag : ℕ) : Primrec (fun x : List ℕ × ℕ =>
        Nat.pair tag (Nat.pair (x.1.getD x.2.unpair.2.unpair.1 0)
          (x.1.getD x.2.unpair.2.unpair.2 0)) + 1) :=
      hnode tag (fun x => Nat.pair
        (x.1.getD x.2.unpair.2.unpair.1 0)
        (x.1.getD x.2.unpair.2.unpair.2 0))
        (Primrec₂.natPair.comp hgetl hgetr)
    have hquant (tag : ℕ) : Primrec (fun x : List ℕ × ℕ =>
        Nat.pair tag (x.1.getD x.2.unpair.2 0) + 1) :=
      hnode tag _ hgetc
    have hatom (tag : ℕ) : Primrec (fun x : List ℕ × ℕ =>
        Nat.pair tag x.2.unpair.2 + 1) := hnode tag _ hc
    refine Primrec.option_some.comp <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) (hatom 1) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (hatom 0) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) (hatom 3) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) (hatom 2) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) (hbinary 5) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) (hbinary 4) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) (hquant 7) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) (hquant 6)
        (Primrec.const 0)
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const (some 0))
    hstep

private theorem getD_map_range {A : Type} (f : ℕ → A) (n k : ℕ)
    (h : k < n) (d : A) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa using h)]
  rfl

private theorem formulaNegStep_history (n : ℕ) :
    formulaNegStep ((List.range n).map formulaNegCode) =
      some (formulaNegCode n) := by
  cases n with
  | zero => simp [formulaNegStep, formulaNegCode]
  | succ e =>
      have hlen : ((List.range (e + 1)).map formulaNegCode).length = e + 1 := by
        simp
      have hc : e.unpair.2 < e + 1 :=
        Nat.lt_succ_of_le (Nat.unpair_right_le e)
      have hcl : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_of_le
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le e))
      have hcr : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_of_le
          (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le e))
      unfold formulaNegStep
      rw [hlen]
      simp only
      rw [formulaNegCode,
        getD_map_range formulaNegCode (e + 1) e.unpair.2.unpair.1 hcl 0,
        getD_map_range formulaNegCode (e + 1) e.unpair.2.unpair.2 hcr 0,
        getD_map_range formulaNegCode (e + 1) e.unpair.2 hc 0]

/-- Negation of a classical arithmetic formula is primitive recursive on its
actual `Encodable` syntax. -/
theorem primrec_formulaNegCode : Primrec formulaNegCode := by
  have h : Primrec₂ (fun (_ : Unit) (n : ℕ) => formulaNegCode n) :=
    Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => formulaNegCode n)
      (primrec_formulaNegStep.comp Primrec.snd).to₂
      (fun _ n => formulaNegStep_history n)
  exact Primrec₂.comp h (Primrec.const ()) Primrec.id

/-- Raw-code negation agrees with syntactic negation for arithmetic formulas,
including formulas with free variables. -/
theorem formulaNegCode_encode {ξ : Type} [Encodable ξ] {n : ℕ} :
    ∀ phi : ArithmeticSemiformula ξ n,
      formulaNegCode (Encodable.encode phi) = Encodable.encode (∼phi) := by
  intro phi
  change formulaNegCode (Encodable.encode phi) =
    Encodable.encode (Semiformula.neg phi)
  induction phi with
  | rel r v =>
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | nrel r v =>
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | verum => simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
      Semiformula.toNat]
  | falsum => simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
      Semiformula.toNat]
  | and phi psi ihphi ihpsi =>
      have ihphi' : formulaNegCode phi.toNat = phi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ihphi
      have ihpsi' : formulaNegCode psi.toNat = psi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ihpsi
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat, ihphi', ihpsi']
  | or phi psi ihphi ihpsi =>
      have ihphi' : formulaNegCode phi.toNat = phi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ihphi
      have ihpsi' : formulaNegCode psi.toNat = psi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ihpsi
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat, ihphi', ihpsi']
  | all phi ih =>
      have ih' : formulaNegCode phi.toNat = phi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ih
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat, ih']
  | exs phi ih =>
      have ih' : formulaNegCode phi.toNat = phi.neg.toNat := by
        simpa only [Semiformula.encode_eq_toNat] using ih
      simp [formulaNegCode, Semiformula.neg, Semiformula.encode_eq_toNat,
        Semiformula.toNat, ih']

theorem primrec_formulaNeg {n : ℕ} :
    Primrec (fun phi : ArithmeticSemiformula Empty n => ∼phi) :=
  Primrec.encode_iff.mp
    ((primrec_formulaNegCode.comp Primrec.encode).of_eq
      (fun phi => formulaNegCode_encode phi))

theorem primrec_formulaImply {n : ℕ} :
    Primrec₂ (fun phi psi : ArithmeticSemiformula Empty n =>
      Arrow.arrow phi psi) := by
  exact (primrec_orFormula
    (primrec_formulaNeg.comp Primrec.fst) Primrec.snd).to₂

theorem primrec_formulaIff {n : ℕ} :
    Primrec₂ (fun phi psi : ArithmeticSemiformula Empty n =>
      LogicalConnective.iff phi psi) := by
  have hforward : Primrec (fun z :
      ArithmeticSemiformula Empty n × ArithmeticSemiformula Empty n =>
      Arrow.arrow z.1 z.2) := primrec_formulaImply
  have hreverse : Primrec (fun z :
      ArithmeticSemiformula Empty n × ArithmeticSemiformula Empty n =>
      Arrow.arrow z.2 z.1) :=
    primrec_formulaImply.comp Primrec.snd Primrec.fst
  exact (primrec_andFormula hforward hreverse).to₂

theorem primrec_formulaAll {A : Type} [Primcodable A] {n : ℕ}
    {f : A → ArithmeticSemiformula Empty (n + 1)} (hf : Primrec f) :
    Primrec (fun x => (∀¹ f x : ArithmeticSemiformula Empty n)) :=
  primrec_allFormula.comp hf

theorem primrec_formulaExs {A : Type} [Primcodable A] {n : ℕ}
    {f : A → ArithmeticSemiformula Empty (n + 1)} (hf : Primrec f) :
    Primrec (fun x => (∃¹ f x : ArithmeticSemiformula Empty n)) :=
  primrec_exsFormula.comp hf

private theorem primrec_rew_fixedArithmeticFormula {A : Type} [Primcodable A] :
    ∀ {n : ℕ} (phi : ArithmeticSemiformula Empty n) {m : ℕ}
      (omega : A → Rew ℒₒᵣ Empty n Empty m), CoordShape omega →
      Primrec (fun x : A => omega x ▹ phi) := by
  intro n phi
  induction phi with
  | verum =>
      intro m omega h
      exact (Primrec.const (⊤ : ArithmeticSemiformula Empty m)).of_eq (fun _ => rfl)
  | falsum =>
      intro m omega h
      exact (Primrec.const (⊥ : ArithmeticSemiformula Empty m)).of_eq (fun _ => rfl)
  | rel r v =>
      intro m omega h
      cases r with
      | eq =>
          refine (primrec_relFormula Language.ORing.Rel.eq
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 0))
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 1))).of_eq ?_
          intro x
          simp only [Semiformula.rew_rel]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
      | lt =>
          refine (primrec_relFormula Language.ORing.Rel.lt
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 0))
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 1))).of_eq ?_
          intro x
          simp only [Semiformula.rew_rel]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
  | nrel r v =>
      intro m omega h
      cases r with
      | eq =>
          refine (primrec_nrelFormula Language.ORing.Rel.eq
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 0))
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 1))).of_eq ?_
          intro x
          simp only [Semiformula.rew_nrel]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
      | lt =>
          refine (primrec_nrelFormula Language.ORing.Rel.lt
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 0))
            (primrec_rew_fixedArithmeticTerm omega h.primrec (v 1))).of_eq ?_
          intro x
          simp only [Semiformula.rew_nrel]
          congr 1
          funext i
          match i with
          | 0 => rfl
          | 1 => rfl
  | and phi psi ihphi ihpsi =>
      intro m omega h
      exact (primrec_andFormula (ihphi omega h) (ihpsi omega h)).of_eq
        (fun _ => rfl)
  | or phi psi ihphi ihpsi =>
      intro m omega h
      exact (primrec_orFormula (ihphi omega h) (ihpsi omega h)).of_eq
        (fun _ => rfl)
  | all phi ihphi =>
      intro m omega h
      exact (primrec_allFormula.comp
        (ihphi (fun x => (omega x).q) h.q)).of_eq (fun _ => rfl)
  | exs phi ihphi =>
      intro m omega h
      exact (primrec_exsFormula.comp
        (ihphi (fun x => (omega x).q) h.q)).of_eq (fun _ => rfl)

private def numeralSubst₂Rew (z : ℕ × ℕ) :
    Rew ℒₒᵣ Empty 2 Empty 0 :=
  Rew.subst ![
    (↑z.1 : ArithmeticSemiterm Empty 0),
    (↑z.2 : ArithmeticSemiterm Empty 0)]

private lemma numeralSubst₂Rew_shape : CoordShape numeralSubst₂Rew := by
  intro i
  match i with
  | 0 =>
      exact Or.inr ⟨fun z : ℕ × ℕ => z.1, Primrec.fst,
        fun z => by simp [numeralSubst₂Rew]⟩
  | 1 =>
      exact Or.inr ⟨fun z : ℕ × ℕ => z.2, Primrec.snd,
        fun z => by simp [numeralSubst₂Rew]⟩

/-- Substitution of two displayed numerals into a fixed two-place arithmetic
formula is primitive recursive. -/
theorem primrec₂_arithmeticSemisentenceNumeralSubst
    (phi : ArithmeticSemisentence 2) :
    Primrec₂ (fun x y : ℕ =>
      (phi/[
        (↑x : ArithmeticSemiterm Empty 0),
        (↑y : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) := by
  change Primrec (fun z : ℕ × ℕ =>
    (phi/[
      (↑z.1 : ArithmeticSemiterm Empty 0),
      (↑z.2 : ArithmeticSemiterm Empty 0)] : ArithmeticSentence))
  exact (primrec_rew_fixedArithmeticFormula phi numeralSubst₂Rew
    numeralSubst₂Rew_shape).of_eq (fun _ => rfl)

private def numeralSubst₃Rew (z : (ℕ × ℕ) × ℕ) :
    Rew ℒₒᵣ Empty 3 Empty 0 :=
  Rew.subst ![
    (↑z.1.1 : ArithmeticSemiterm Empty 0),
    (↑z.1.2 : ArithmeticSemiterm Empty 0),
    (↑z.2 : ArithmeticSemiterm Empty 0)]

private lemma numeralSubst₃Rew_shape : CoordShape numeralSubst₃Rew := by
  intro i
  match i with
  | 0 =>
      exact Or.inr ⟨fun z : (ℕ × ℕ) × ℕ => z.1.1,
        Primrec.fst.comp Primrec.fst,
        fun z => by simp [numeralSubst₃Rew]⟩
  | 1 =>
      exact Or.inr ⟨fun z : (ℕ × ℕ) × ℕ => z.1.2,
        Primrec.snd.comp Primrec.fst,
        fun z => by simp [numeralSubst₃Rew]⟩
  | 2 =>
      exact Or.inr ⟨fun z : (ℕ × ℕ) × ℕ => z.2,
        Primrec.snd,
        fun z => by simp [numeralSubst₃Rew]⟩

/-- Substitution of three displayed numerals into a fixed three-place
arithmetic formula is primitive recursive, using packed arguments
`((x, y), z)`. -/
theorem primrec_arithmeticSemisentenceNumeralSubst₃
    (phi : ArithmeticSemisentence 3) :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      (phi/[
        (↑z.1.1 : ArithmeticSemiterm Empty 0),
        (↑z.1.2 : ArithmeticSemiterm Empty 0),
        (↑z.2 : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) := by
  exact (primrec_rew_fixedArithmeticFormula phi numeralSubst₃Rew
    numeralSubst₃Rew_shape).of_eq (fun _ => rfl)

/-- Insert the first packed argument as the leading numeral of a fixed
three-place formula and use the two bound variables in the order required by
`∀ x y`.  The second packed argument is intentionally unused. -/
theorem primrec₂_firstNumeralUnderTwoBinders
    (phi : ArithmeticSemisentence 3) :
    Primrec₂ (fun (q : ℕ) (_r : ℕ) =>
      (Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)]) ▹ phi) := by
  let omega : ℕ × ℕ → Rew ℒₒᵣ Empty 3 Empty 2 := fun z =>
    Rew.subst ![
      (↑z.1 : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2),
      (#0 : ArithmeticSemiterm Empty 2)]
  have homega : CoordShape omega := by
    intro i
    match i with
    | 0 =>
        exact Or.inr ⟨fun z : ℕ × ℕ => z.1, Primrec.fst,
          fun z => by simp [omega]⟩
    | 1 => exact Or.inl ⟨1, fun z => by simp [omega]⟩
    | 2 => exact Or.inl ⟨0, fun z => by simp [omega]⟩
  change Primrec (fun z : ℕ × ℕ =>
    (Rew.subst ![
      (↑z.1 : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2),
      (#0 : ArithmeticSemiterm Empty 2)]) ▹ phi)
  exact (primrec_rew_fixedArithmeticFormula phi omega homega).of_eq
    (fun _ => rfl)

/-- Insert the second packed argument as the program numeral in a fixed
four-place stage formula, retaining the existential stage and the two bound
graph variables. -/
theorem primrec₂_secondNumeralUnderStageAndTwoBinders
    (phi : ArithmeticSemisentence 4) :
    Primrec₂ (fun (_q : ℕ) (r : ℕ) =>
      (Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 3),
        (↑r : ArithmeticSemiterm Empty 3),
        (#2 : ArithmeticSemiterm Empty 3),
        (#1 : ArithmeticSemiterm Empty 3)]) ▹ phi) := by
  let omega : ℕ × ℕ → Rew ℒₒᵣ Empty 4 Empty 3 := fun z =>
    Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 3),
      (↑z.2 : ArithmeticSemiterm Empty 3),
      (#2 : ArithmeticSemiterm Empty 3),
      (#1 : ArithmeticSemiterm Empty 3)]
  have homega : CoordShape omega := by
    intro i
    match i with
    | 0 => exact Or.inl ⟨0, fun z => by simp [omega]⟩
    | 1 =>
        exact Or.inr ⟨fun z : ℕ × ℕ => z.2, Primrec.snd,
          fun z => by simp [omega]⟩
    | 2 => exact Or.inl ⟨2, fun z => by simp [omega]⟩
    | 3 => exact Or.inl ⟨1, fun z => by simp [omega]⟩
  change Primrec (fun z : ℕ × ℕ =>
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 3),
      (↑z.2 : ArithmeticSemiterm Empty 3),
      (#2 : ArithmeticSemiterm Empty 3),
      (#1 : ArithmeticSemiterm Empty 3)]) ▹ phi)
  exact (primrec_rew_fixedArithmeticFormula phi omega homega).of_eq
    (fun _ => rfl)

/-- Insert one numeral into the last coordinate of a fixed three-place
formula, retaining the first two coordinates as bound variables. -/
theorem primrec_lastNumeralPreservingTwo
    (phi : ArithmeticSemisentence 3) :
    Primrec (fun q : ℕ =>
      (Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2),
        (↑q : ArithmeticSemiterm Empty 2)]) ▹ phi) := by
  let omega : ℕ → Rew ℒₒᵣ Empty 3 Empty 2 := fun q =>
    Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2),
      (↑q : ArithmeticSemiterm Empty 2)]
  have homega : CoordShape omega := by
    intro i
    match i with
    | 0 => exact Or.inl ⟨0, fun q => by simp [omega]⟩
    | 1 => exact Or.inl ⟨1, fun q => by simp [omega]⟩
    | 2 =>
        exact Or.inr ⟨id, Primrec.id, fun q => by simp [omega]⟩
  exact (primrec_rew_fixedArithmeticFormula phi omega homega).of_eq
    (fun _ => rfl)

/-- Insert two numerals into the last two coordinates of a fixed three-place
formula, retaining the first coordinate as a bound variable. -/
theorem primrec₂_lastTwoNumeralsPreservingOne
    (phi : ArithmeticSemisentence 3) :
    Primrec₂ (fun q r : ℕ =>
      (Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 1),
        (↑r : ArithmeticSemiterm Empty 1),
        (↑q : ArithmeticSemiterm Empty 1)]) ▹ phi) := by
  let omega : ℕ × ℕ → Rew ℒₒᵣ Empty 3 Empty 1 := fun z =>
    Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 1),
      (↑z.2 : ArithmeticSemiterm Empty 1),
      (↑z.1 : ArithmeticSemiterm Empty 1)]
  have homega : CoordShape omega := by
    intro i
    match i with
    | 0 => exact Or.inl ⟨0, fun z => by simp [omega]⟩
    | 1 =>
        exact Or.inr ⟨fun z : ℕ × ℕ => z.2, Primrec.snd,
          fun z => by simp [omega]⟩
    | 2 =>
        exact Or.inr ⟨fun z : ℕ × ℕ => z.1, Primrec.fst,
          fun z => by simp [omega]⟩
  change Primrec (fun z : ℕ × ℕ =>
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 1),
      (↑z.2 : ArithmeticSemiterm Empty 1),
      (↑z.1 : ArithmeticSemiterm Empty 1)]) ▹ phi)
  exact (primrec_rew_fixedArithmeticFormula phi omega homega).of_eq
    (fun _ => rfl)

end Arith.FixedFormulaNumeralSubstitution
