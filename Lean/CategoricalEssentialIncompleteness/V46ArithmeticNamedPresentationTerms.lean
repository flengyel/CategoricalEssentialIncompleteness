/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationBasic
public import Mathlib.Tactic.IntervalCases

/-! # Exact arithmetic-term and relation presentation

The given symbol predicates have precisely their printed arithmetic arities.
Their ordered children are retained in both directions.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature

/-- The actual arithmetic symbol predicates exclude the other arities and
labels. This induction principle retains the given ordered children. -/
theorem term_induction {C : Term → Prop}
    (hvar : ∀ x, C (.var x)) (hzero : C zero) (hone : C one)
    (hadd : ∀ r t, C r → C t → C (add r t))
    (hmul : ∀ r t, C r → C t → C (mul r t)) : ∀ r, C r := by
  intro r
  induction r with
  | var x => exact hvar x
  | app k symbol children ih =>
      rcases k with ⟨k,hk⟩
      change k < 3 at hk
      interval_cases k
      · have hs : symbol.val = 0 ∨ symbol.val = 1 :=
          (functionSymbols_zero_eval symbol.val).mp symbol.property
        have hc : children = Fin.elim0 := funext fun i => i.elim0
        rw [hc]
        rcases hs with hs | hs
        · have he : symbol = zeroSymbol := Subtype.ext hs
          subst symbol
          exact hzero
        · have he : symbol = oneSymbol := Subtype.ext hs
          subst symbol
          exact hone
      · exact False.elim ((functionSymbols_other_eval (M := ℕ) 1 (by decide) (by decide)
          symbol.val) symbol.property)
      · have hs : symbol.val = 0 ∨ symbol.val = 1 :=
          (functionSymbols_two_eval symbol.val).mp symbol.property
        have hc : children = ![children 0,children 1] := by
          funext i
          fin_cases i <;> rfl
        rcases hs with hs | hs
        · have he : symbol = addSymbol := Subtype.ext hs
          subst symbol
          have h := hadd (children 0) (children 1) (ih 0) (ih 1)
          change C (.app ⟨2,hk⟩ addSymbol ![children 0,children 1]) at h
          rw [← hc] at h
          exact h
        · have he : symbol = mulSymbol := Subtype.ext hs
          subst symbol
          have h := hmul (children 0) (children 1) (ih 0) (ih 1)
          change C (.app ⟨2,hk⟩ mulSymbol ![children 0,children 1]) at h
          rw [← hc] at h
          exact h

theorem relation_presentation (k : Fin (bound+1)) (s : RelationSymbols k.val)
    (children : Fin k.val → Term) :
    ∃ r t, NamedFiniteSyntax.Formula.relation k s children = less r t := by
  rcases k with ⟨k,hk⟩
  change k < 3 at hk
  interval_cases k
  · exact False.elim ((relationSymbols_other_eval (M := ℕ) 0 (by decide) s.val) s.property)
  · exact False.elim ((relationSymbols_other_eval (M := ℕ) 1 (by decide) s.val) s.property)
  · have hs : s.val = 1 := (relationSymbols_two_eval s.val).mp s.property
    have he : s = ltSymbol := Subtype.ext hs
    subst s
    refine ⟨children 0,children 1,?_⟩
    congr 1
    funext i
    fin_cases i <;> rfl

@[simp] theorem term_zero (n : ℕ) : term n zero = .func .zero Fin.elim0 := by
  simp [term,zero,zeroSymbol]
@[simp] theorem term_one (n : ℕ) : term n one = .func .one Fin.elim0 := by
  simp [term,one,oneSymbol]
@[simp] theorem term_add (n : ℕ) (r t : Term) :
    term n (add r t) = .func .add ![term n r,term n t] := by
  simp [term,add,addSymbol]
@[simp] theorem term_mul (n : ℕ) (r t : Term) :
    term n (mul r t) = .func .mul ![term n r,term n t] := by
  simp [term,mul,mulSymbol]

/-- Back translation followed by elaboration retains literal names and
all ordered arithmetic children; it is equality of native terms. -/
theorem term_roundtrip (n : ℕ) (r : Term) (hr : TermBound n r) :
    ArithmeticNamedOpenTranslation.term ![] Fin.val (term n r) = r := by
  induction r using term_induction with
  | hvar x =>
      have hx : x < n := hr x (by simp [NamedFiniteSyntax.Term.freeVariables])
      simp [term,hx,ArithmeticNamedOpenTranslation.term]
  | hzero => rfl
  | hone => rfl
  | hadd r t ir it =>
      have hb : TermBound n r ∧ TermBound n t := by
        simpa only [TermBound,add_freeVariables,List.mem_append,or_imp,forall_and] using hr
      simpa only [term_add,ArithmeticNamedOpenTranslation.term,Matrix.cons_val_zero,
        Matrix.cons_val_one] using congrArg₂ add (ir hb.1) (it hb.2)
  | hmul r t ir it =>
      have hb : TermBound n r ∧ TermBound n t := by
        simpa only [TermBound,mul_freeVariables,List.mem_append,or_imp,forall_and] using hr
      simpa only [term_mul,ArithmeticNamedOpenTranslation.term,Matrix.cons_val_zero,
        Matrix.cons_val_one] using congrArg₂ mul (ir hb.1) (it hb.2)

/-- Every free source name occurs in the original native term. -/
theorem term_fvar (n : ℕ) (r : Term) (x : Fin n)
    (hx : (term n r).FVar? x) : x.val ∈ r.freeVariables := by
  induction r using term_induction with
  | hvar y =>
      by_cases hy : y < n
      · have he : (⟨y,hy⟩ : Fin n) = x := by simpa [term,hy] using hx
        simp [NamedFiniteSyntax.Term.freeVariables,← he]
      · simp [term,hy] at hx
  | hzero => simp at hx
  | hone => simp at hx
  | hadd r t ir it =>
      have h : (term n r).FVar? x ∨ (term n t).FVar? x := by
        simpa [Fin.exists_fin_two] using hx
      rw [add_freeVariables]
      exact List.mem_append.mpr (h.imp ir it)
  | hmul r t ir it =>
      have h : (term n r).FVar? x ∨ (term n t).FVar? x := by
        simpa [Fin.exists_fin_two] using hx
      rw [mul_freeVariables]
      exact List.mem_append.mpr (h.imp ir it)

universe w
variable {K : Type w} [ORingStructure K]

/-- Native and source term semantics agree in the semantic arithmetic
structure K, independently of the arithmetic word-code model. -/
theorem term_value (n : ℕ) (r : Term) (hr : TermBound n r) (ρ : ℕ → K) :
    (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) =
      r.evaluate ArithmeticNamedTranslation.functions ρ := by
  induction r using term_induction with
  | hvar x =>
      have hx : x < n := hr x (by simp [NamedFiniteSyntax.Term.freeVariables])
      simp [term,hx,NamedFiniteSyntax.Term.evaluate]
  | hzero => exact (ArithmeticNamedTranslation.evaluate_zero ρ).symm
  | hone => exact (ArithmeticNamedTranslation.evaluate_one ρ).symm
  | hadd r t ir it =>
      have hb : TermBound n r ∧ TermBound n t := by
        simpa only [TermBound,add_freeVariables,List.mem_append,or_imp,forall_and] using hr
      change (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) +
        (term n t).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) = _
      rw [ArithmeticNamedTranslation.evaluate_add]
      exact congrArg₂ (fun x y : K => x+y) (ir hb.1) (it hb.2)
  | hmul r t ir it =>
      have hb : TermBound n r ∧ TermBound n t := by
        simpa only [TermBound,mul_freeVariables,List.mem_append,or_imp,forall_and] using hr
      change (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) *
        (term n t).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) = _
      rw [ArithmeticNamedTranslation.evaluate_mul]
      exact congrArg₂ (fun x y : K => x*y) (ir hb.1) (it hb.2)

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
