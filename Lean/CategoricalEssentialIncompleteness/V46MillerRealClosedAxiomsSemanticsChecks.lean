/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxiomsSemantics


/-! # Literal field-axiom semantics and the real model of T_a -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Semantics
open OrderedFieldSyntax
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [IsRealClosed K] (constants : ℕ → K)

omit [IsStrictOrderedRing K] in
example (n : ℕ) : ∀ ρ,Holds constants (oddSentence n) ρ := oddSentence_valid constants n
example (φ : Formula) (h : φ∈finiteSentences) : ∀ ρ,Holds constants φ ρ :=
  finiteSentences_valid constants φ h
example (word : ℕ) (h : word∈RCFAxiomWords) :
    ∃ φ : Formula,formulaCode φ=word ∧ ∀ ρ,Holds constants φ ρ := rcf_words_valid constants word h
example (f : Polynomial ℝ) (h : Odd f.natDegree) : ∃ x : ℝ,f.IsRoot x := real_odd_root f h
example : IsRealClosed ℝ := realClosedReal
example (a : Point) (n j : ℕ) (ρ : ℕ → ℝ) :
    Holds (fun i => (a i : ℝ)) (belowSentence n j) ρ ↔ (Rationals.q j : ℝ)<(a n : ℝ) :=
  belowSentence_holds a n j ρ
example (a : Point) (n j : ℕ) (ρ : ℕ → ℝ) :
    Holds (fun i => (a i : ℝ)) (aboveSentence n j) ρ ↔ (a n : ℝ)<(Rationals.q j : ℝ) :=
  aboveSentence_holds a n j ρ
example (a : Point) (word : ℕ) (h : word∈RCFAxiomWords ∨ word∈cutAxioms a) :
    ∃ φ : Formula,formulaCode φ=word ∧
      ∀ ρ,φ.Holds (functions (fun i => (a i : ℝ))) relations ρ := theory_words_valid a word h
example (a : Point) (φ : Formula) (h : formulaCode φ∈theoryAxioms a) :
    ∀ ρ,φ.Holds (functions (fun i => (a i : ℝ))) relations ρ := theory_formula_valid a φ h

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Semantics
