/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxioms
public import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs

/-! # Actual finite proof bounds for arbitrary extensions of T_a

An extension proves every literal T_a axiom. It need not contain the axiom
codes literally, be enumerable, or have the real model of T_a. The negative
bound uses two actual named instantiations of the closed asymmetry axiom.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedBounds
open OrderedFieldSyntax RealClosedAxioms

abbrev Proof (Γ : Set ℕ) (φ : Formula) : Prop :=
  FiniteAxiomProof functionSymbols relationSymbols bound Γ φ

def Extends (a : Point) (Γ : Set ℕ) : Prop :=
  ∀ φ : Formula,formulaCode φ∈theoryAxioms a → Proof Γ φ

theorem theory_formula_closed (a : Point) (φ : Formula) (h : formulaCode φ∈theoryAxioms a) :
    φ.freeVariables=[] := (sentence_formulaCode φ).mp (theoryAxioms_sentences a _ h)

theorem extends_iff_proof_transport (a : Point) (Γ : Set ℕ) :
    Extends a Γ ↔ ∀ φ : Formula,Proof (theoryAxioms a) φ → Proof Γ φ := by
  constructor
  · intro h φ hφ
    exact FiniteAxiomProof.replace_axioms functionSymbols relationSymbols bound
      (fun ψ hψ _ => h ψ hψ) hφ
  · intro h φ hφ
    exact h φ (FiniteAxiomProof.axiom_of_mem functionSymbols relationSymbols bound φ hφ
      (theory_formula_closed a φ hφ))

theorem extends_of_inclusion (a : Point) {Γ : Set ℕ} (h : theoryAxioms a⊆Γ) : Extends a Γ := by
  intro φ hφ
  exact FiniteAxiomProof.axiom_of_mem functionSymbols relationSymbols bound φ (h hφ)
    (theory_formula_closed a φ hφ)

@[simp] theorem one_substitute (name : ℕ) (t : Term) : one.substitute name t=one :=
  NamedFiniteSyntax.Term.substitute_absent one name t (by simp)

@[simp] theorem var_substitute (name : ℕ) (t : Term) (x : ℕ) :
    (var x).substitute name t=if x=name then t else var x := rfl

@[simp] theorem lt_substitute (s t replacement : Term) (name : ℕ) :
    (lt s t).substitute name replacement=
      some (lt (s.substitute name replacement) (t.substitute name replacement)) := by
  change some (NamedFiniteSyntax.Formula.relation ⟨2,by decide⟩ ltSymbol
      (fun i => (![s,t] i).substitute name replacement))=
    some (NamedFiniteSyntax.Formula.relation ⟨2,by decide⟩ ltSymbol
      ![s.substitute name replacement,t.substitute name replacement])
  apply congrArg some
  apply congrArg (NamedFiniteSyntax.Formula.relation ⟨2,by decide⟩ ltSymbol)
  funext i
  fin_cases i <;> rfl

def asymmetryBody : Formula := all 1
  (imp (lt (var 0) (var 1)) (negation (lt (var 1) (var 0))))
def asymmetryAtOne : Formula := all 1
  (imp (lt one (var 1)) (negation (lt (var 1) one)))
def asymmetryAtOneBody : Formula := imp (lt one (var 1)) (negation (lt (var 1) one))
def upperHalfSentence (n : ℕ) : Formula := lt one (mul (natural 2) (c n))

theorem asymmetry_freeFor_one : asymmetryBody.FreeFor 0 one := by
  simp [asymmetryBody,all,imp,negation,lt,NamedFiniteSyntax.Formula.FreeFor]

theorem asymmetry_substitute_one : asymmetryBody.substitute 0 one=some asymmetryAtOne := by
  simp [asymmetryBody,asymmetryAtOne,all,imp,negation,NamedFiniteSyntax.Formula.substitute]

theorem asymmetryAtOne_freeFor (n : ℕ) :
    asymmetryAtOneBody.FreeFor 1 (mul (natural 2) (c n)) := by
  simp [asymmetryAtOneBody,imp,negation,lt,NamedFiniteSyntax.Formula.FreeFor]

theorem asymmetryAtOne_substitute (n : ℕ) :
    asymmetryAtOneBody.substitute 1 (mul (natural 2) (c n))=
      some (imp (upperHalfSentence n) (negation (thetaSentence n))) := by
  simp [asymmetryAtOneBody,upperHalfSentence,thetaSentence,imp,negation,
    NamedFiniteSyntax.Formula.substitute]

/-- The two instances come from the seven-scheme calculus itself. -/
theorem asymmetry_instance {Γ : Set ℕ} (n : ℕ) (h : Proof Γ asymmetrySentence) :
    Proof Γ (imp (upperHalfSentence n) (negation (thetaSentence n))) := by
  have hfirst : Proof Γ asymmetryAtOne :=
    FiniteAxiomProof.modusPonens functionSymbols relationSymbols bound h
      (FiniteAxiomProof.instantiation functionSymbols relationSymbols bound
        0 asymmetryBody one asymmetryAtOne asymmetry_freeFor_one asymmetry_substitute_one)
  exact FiniteAxiomProof.modusPonens functionSymbols relationSymbols bound hfirst
    (FiniteAxiomProof.instantiation functionSymbols relationSymbols bound
      1 asymmetryAtOneBody (mul (natural 2) (c n))
      (imp (upperHalfSentence n) (negation (thetaSentence n)))
      (asymmetryAtOne_freeFor n) (asymmetryAtOne_substitute n))

theorem lower_cut_gamma_theta (a : Point) (Γ : Set ℕ) (hΓ : Extends a Γ)
    (n : ℕ) (h : (a n : ℝ)<1/2) : Proof Γ (thetaSentence n) :=
  hΓ (thetaSentence n) (theory_lower_cut_axiom a n h)

theorem upper_cut_gamma_negtheta (a : Point) (Γ : Set ℕ) (hΓ : Extends a Γ)
    (n : ℕ) (h : 1/2<(a n : ℝ)) : Proof Γ (negation (thetaSentence n)) := by
  have ha : Proof Γ asymmetrySentence := hΓ asymmetrySentence (theory_asymmetry_mem a)
  have hp : Proof Γ (upperHalfSentence n) := hΓ (upperHalfSentence n) (theory_upper_cut_axiom a n h)
  exact FiniteAxiomProof.modusPonens functionSymbols relationSymbols bound hp (asymmetry_instance n ha)

/-- Both supports are actual finite subsets of the arbitrary external Γ. -/
theorem lower_finite_support (a : Point) (Γ : Set ℕ) (hΓ : Extends a Γ)
    (n : ℕ) (h : (a n : ℝ)<1/2) : ∃ L : List ℕ,(∀ word∈L,word∈Γ) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) (thetaSentence n) :=
  lower_cut_gamma_theta a Γ hΓ n h

theorem upper_finite_support (a : Point) (Γ : Set ℕ) (hΓ : Extends a Γ)
    (n : ℕ) (h : 1/2<(a n : ℝ)) : ∃ L : List ℕ,(∀ word∈L,word∈Γ) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L)
        (negation (thetaSentence n)) := upper_cut_gamma_negtheta a Γ hΓ n h

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedBounds
