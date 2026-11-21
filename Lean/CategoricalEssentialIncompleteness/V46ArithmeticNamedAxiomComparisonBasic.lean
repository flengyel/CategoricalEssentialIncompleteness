/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofTranslation
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertReplacement

/-! # Named PA axiom matrices and universal closure

The matrices use the named arithmetic constructors. Universal closures retain their
variable names, and sentencehood is checked by the free-variable list.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
open NamedArithmeticSignature

abbrev Tm := NamedArithmeticSignature.Term
abbrev Fm := NamedArithmeticSignature.Formula

def le (s t : Tm) : Fm := ArithmeticNamedTranslation.disjunction (.equal s t) (less s t)

def inductionMatrix (x : ℕ) (φ φ0 φs : Fm) : Fm :=
  .imp φ0 (.imp (.all x (.imp φ φs)) (.all x φ))

/-- The arithmetic and order axiom matrices of PA⁻, together with the induction matrices
for named formulas. -/
inductive PASeed : Fm → Prop
  | addZero (x : ℕ) : PASeed (.equal (add (.var x) zero) (.var x))
  | addAssoc (x y z : ℕ) : PASeed
      (.equal (add (add (.var x) (.var y)) (.var z)) (add (.var x) (add (.var y) (.var z))))
  | addComm (x y : ℕ) : PASeed (.equal (add (.var x) (.var y)) (add (.var y) (.var x)))
  | addEqOfLt (x y z : ℕ) (hzx : z ≠ x) (hzy : z ≠ y) : PASeed
      (.imp (less (.var x) (.var y))
        (ArithmeticNamedTranslation.existential z (.equal (add (.var x) (.var z)) (.var y))))
  | zeroLe (x : ℕ) : PASeed (le zero (.var x))
  | zeroLtOne : PASeed (less zero one)
  | oneLeOfZeroLt (x : ℕ) : PASeed (.imp (less zero (.var x)) (le one (.var x)))
  | addLtAdd (x y z : ℕ) : PASeed
      (.imp (less (.var x) (.var y)) (less (add (.var x) (.var z)) (add (.var y) (.var z))))
  | mulZero (x : ℕ) : PASeed (.equal (mul (.var x) zero) zero)
  | mulOne (x : ℕ) : PASeed (.equal (mul (.var x) one) (.var x))
  | mulAssoc (x y z : ℕ) : PASeed
      (.equal (mul (mul (.var x) (.var y)) (.var z)) (mul (.var x) (mul (.var y) (.var z))))
  | mulComm (x y : ℕ) : PASeed (.equal (mul (.var x) (.var y)) (mul (.var y) (.var x)))
  | mulLtMul (x y z : ℕ) : PASeed
      (.imp (ArithmeticNamedTranslation.conjunction (less (.var x) (.var y)) (less zero (.var z)))
        (less (mul (.var x) (.var z)) (mul (.var y) (.var z))))
  | distr (x y z : ℕ) : PASeed
      (.equal (mul (.var x) (add (.var y) (.var z)))
        (add (mul (.var x) (.var y)) (mul (.var x) (.var z))))
  | ltIrrefl (x : ℕ) : PASeed (.neg (less (.var x) (.var x)))
  | ltTrans (x y z : ℕ) : PASeed
      (.imp (ArithmeticNamedTranslation.conjunction (less (.var x) (.var y)) (less (.var y) (.var z)))
        (less (.var x) (.var z)))
  | ltTri (x y : ℕ) : PASeed
      (ArithmeticNamedTranslation.disjunction (less (.var x) (.var y))
        (ArithmeticNamedTranslation.disjunction (.equal (.var x) (.var y)) (less (.var y) (.var x))))
  | «induction» (x : ℕ) (φ φ0 φs : Fm)
      (h0 : φ.FreeFor x zero) (hs : φ.FreeFor x (add (.var x) one))
      (s0 : φ.substitute x zero = some φ0)
      (ss : φ.substitute x (add (.var x) one) = some φs) :
      PASeed (inductionMatrix x φ φ0 φs)

inductive UniversalClosure (φ : Fm) : Fm → Prop
  | refl : UniversalClosure φ φ
  | all (x : ℕ) {ψ : Fm} : UniversalClosure φ ψ → UniversalClosure φ (.all x ψ)

def PAAxiom (ψ : Fm) : Prop :=
  ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ

def ExtendsPA (A : SyntacticPredicates.Carrier) : Prop :=
  ∀ ψ, PAAxiom ψ → SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ

def closure (names : List ℕ) (φ : Fm) : Fm := names.foldr NamedFiniteSyntax.Formula.all φ

def freeBound (φ : Fm) : ℕ := φ.freeVariables.foldr (fun x b => max (x+1) b) 0

def canonicalClosure (φ : Fm) : Fm := closure (List.range (freeBound φ)) φ

variable (A : SyntacticPredicates.Carrier)
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A

theorem UniversalClosure.derives {φ ψ : Fm} (h : UniversalClosure φ ψ)
    (hp : D φ) : D ψ := by
  induction h with
  | refl => exact hp
  | all x h ih => exact .generalization x ih

theorem closure_derives (names : List ℕ) (φ : Fm) (h : D φ) : D (closure names φ) := by
  induction names with
  | nil => exact h
  | cons x names ih => exact .generalization x ih

theorem derives_of_closure (names : List ℕ) (φ : Fm) (h : D (closure names φ)) : D φ := by
  revert h
  induction names with
  | nil => intro h; exact h
  | cons x names ih =>
      intro h
      exact ih (.modusPonens h (NamedHilbertQuantifiers.all_elim_self
        functionSymbols relationSymbols bound A x (closure names φ)))

theorem closure_isUniversal (names : List ℕ) (φ : Fm) : UniversalClosure φ (closure names φ) := by
  induction names with
  | nil => exact .refl
  | cons x names ih => exact .all x ih

private theorem mem_below_bound (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    x < l.foldr (fun y b => max (y+1) b) 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (Nat.lt_succ_self x).trans_le (Nat.le_max_left _ _)
      · exact (ih hx).trans_le (Nat.le_max_right _ _)

theorem closure_freeVariables (names : List ℕ) (φ : Fm) (x : ℕ) :
    x ∈ (closure names φ).freeVariables ↔ x ∈ φ.freeVariables ∧ x ∉ names := by
  induction names with
  | nil => simp [closure]
  | cons y names ih =>
      simp only [closure,List.foldr_cons,NamedFiniteSyntax.Formula.freeVariables,List.mem_filter]
      change (x ∈ (closure names φ).freeVariables ∧ (x != y) = true) ↔
        x ∈ φ.freeVariables ∧ x ∉ y :: names
      rw [ih]
      simp only [bne_iff_ne,List.mem_cons,not_or]
      tauto

theorem canonicalClosure_sentence (φ : Fm) : (canonicalClosure φ).freeVariables = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have h := (closure_freeVariables (List.range (freeBound φ)) φ x).mp hx
  exact h.2 (List.mem_range.mpr (mem_below_bound φ.freeVariables x h.1))

theorem extendsPA_iff_canonical : ExtendsPA A ↔ ∀ φ, PASeed φ → D (canonicalClosure φ) := by
  constructor
  · intro h φ hφ
    exact h _ ⟨canonicalClosure_sentence φ,φ,hφ,closure_isUniversal _ _⟩
  · intro h ψ hψ
    obtain ⟨_,φ,hφ,hcl⟩ := hψ
    exact UniversalClosure.derives A hcl (derives_of_closure A _ _ (h φ hφ))

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
