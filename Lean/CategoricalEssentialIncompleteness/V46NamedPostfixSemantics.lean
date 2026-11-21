/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixComparison
public import CategoricalEssentialIncompleteness.V46NamedFiniteSoundness
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAlgebra

/-! # Semantics on the standard accepted-word carriers

The decoding equivalences retain every numerical name and symbol. The
semantic structure is independent of the arithmetic model of the codes.
-/

@[expose] public section

noncomputable section
universe u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixSemantics
open NamedPostfixEncoding
variable {σ π : ℕ → Carrier} {d : ℕ} {K : Type u}

/-- The term-word subtype is the standard interpretation of the constructed
predicate-category term carrier. -/
def termModelEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Term (Symbols σ) d ≃
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
        (SyntacticSyntax.termCarrier (termPolynomial σ d) (formulaPolynomial π d)) :=
  termEquiv σ π d

/-- No binder-name quotient is taken in this model comparison. -/
def formulaModelEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
        (SyntacticSyntax.formulaCarrier (termPolynomial σ d) (formulaPolynomial π d)) :=
  formulaEquiv σ π d

variable (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

def termValue (r : termWords σ π d) (assignment : ℕ → K) : K :=
  ((termEquiv σ π d).symm r).evaluate functions assignment

def Holds (φ : formulaWords σ π d) (assignment : ℕ → K) : Prop :=
  ((formulaEquiv σ π d).symm φ).Holds functions relations assignment

def Valid (φ : formulaWords σ π d) : Prop :=
  ∀ assignment : ℕ → K, Holds functions relations φ assignment

@[simp] theorem termValue_encoded (r : NamedFiniteSyntax.Term (Symbols σ) d)
    (assignment : ℕ → K) :
    termValue functions (termEquiv σ π d r) assignment = r.evaluate functions assignment := by
  simp [termValue]

@[simp] theorem holds_encoded (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (assignment : ℕ → K) :
    Holds functions relations (formulaEquiv σ π d φ) assignment ↔
      φ.Holds functions relations assignment := by
  simp [Holds]

@[simp] theorem valid_encoded (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    Valid functions relations (formulaEquiv σ π d φ) ↔
      NamedFiniteSyntax.Formula.Valid functions relations φ := by
  simp [Valid, NamedFiniteSyntax.Formula.Valid]

/-- The semantic negation acts by the literal constructor. Its comparison with the
categorical sentence morphism is a further equation. -/
def negWord (φ : formulaWords σ π d) : formulaWords σ π d :=
  formulaEquiv σ π d (.neg ((formulaEquiv σ π d).symm φ))

theorem negWord_val (φ : formulaWords σ π d) :
    (negWord φ).val = SyntacticSyntax.Coding.constructor true (formulaPolynomial π d)
      (negInput φ.val) := by
  have he : formulaCode ((formulaEquiv σ π d).symm φ) = φ.val :=
    congrArg Subtype.val ((formulaEquiv σ π d).apply_symm_apply φ)
  simp only [negWord, formulaEquiv_val, formulaCode]
  rw [he]

@[simp] theorem holds_negWord (φ : formulaWords σ π d) (assignment : ℕ → K) :
    Holds functions relations (negWord φ) assignment ↔
      ¬ Holds functions relations φ assignment := by
  simp [negWord, Holds, NamedFiniteSyntax.Formula.Holds]

theorem valid_negation_disjoint [Nonempty K] (φ : formulaWords σ π d)
    (hφ : Valid functions relations φ) (hn : Valid functions relations (negWord φ)) : False := by
  let assignment : ℕ → K := fun _ => Classical.choice inferInstance
  exact (holds_negWord functions relations φ assignment).mp (hn assignment) (hφ assignment)

/-- Semantics on encoded terms agrees with the proved named term substitution, before the
numerical algorithm comparison is applied. -/
theorem termValue_substitute (r t : NamedFiniteSyntax.Term (Symbols σ) d)
    (x : ℕ) (assignment : ℕ → K) :
    termValue functions (termEquiv σ π d (r.substitute x t)) assignment =
      termValue functions (termEquiv σ π d r)
        (Function.update assignment x (termValue functions (termEquiv σ π d t) assignment)) := by
  simpa using r.evaluate_substitute functions t x assignment

/-- The literal option success equation has its semantic meaning on
standard accepted words. The source success pullback is compared later. -/
theorem holds_substitute (φ ψ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) (assignment : ℕ → K)
    (h : φ.substitute x t = some ψ) :
    Holds functions relations (formulaEquiv σ π d ψ) assignment ↔
      Holds functions relations (formulaEquiv σ π d φ)
        (Function.update assignment x (termValue functions (termEquiv σ π d t) assignment)) := by
  simpa using φ.holds_substitute functions relations ψ t x assignment h

end CategoricalEssentialIncompleteness.V46.NamedPostfixSemantics
