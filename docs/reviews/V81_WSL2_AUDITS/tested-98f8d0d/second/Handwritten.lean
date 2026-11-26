module

import CategoricalEssentialIncompleteness.V46TrivialDominicalCategoryChecks
import CategoricalEssentialIncompleteness.V46TuringObjectRecognition
import CategoricalEssentialIncompleteness.V46SliceUnitFactorization
import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46ForkUndecidedAtoms
import CategoricalEssentialIncompleteness.V46FinitaryInductiveDefinitions
import CategoricalEssentialIncompleteness.ArithmeticInseparability

set_option autoImplicit false
open CategoryTheory CategoryTheory.PCategoryStruct CategoryTheory.RestrictionCategory
open CategoryTheory.Limits CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
universe v u

namespace ReaderTwo
section
open TrivialDominicalCategory
example : ∃ τ : nearProd One.obj One.obj ⟶ coprod One.obj One.obj,
    DiPaolaHeller.IsTuringMorphism τ ∧
    ¬ Inseparable (Idem.pull (diag One.obj ≫ τ) (summand0 One.obj One.obj))
      (Idem.pull (diag One.obj ≫ τ) (summand1 One.obj One.obj)) := by
  obtain ⟨h, _, d⟩ := TrivialDominicalCategory.Checks.turing_with_separable_domains
  exact ⟨evaluator,h,d⟩
end

section
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
open RecursionCategory
example (U : C) (typed : ∀ A B : C, ∃ t : nearProd U A ⟶ B, IsTuringMorphism t)
    (X : C) : ∃ (r : U ⟶ X) (m : X ⟶ U), m ≫ r = 𝟙 X ∧ isTotal m := by
  obtain ⟨m,r,ht,hr⟩ := ((turingObject_iff U).mp typed).2 X
  exact ⟨r,m,hr,ht⟩

open RestrictionSubobjects PartialSliceChangeBase
variable [Splits C] [HasPullbacks (Tot C)] {T U : Tot C}
example (i : T ⟶ U) [Mono i] (inv : MonoInverses C) (q : PartialMaps.Par (Over U)) :
    (∃ s : q.obj.left ⟶ T, s ≫ i = q.obj.hom) ↔
      isTotal ((rightAdjunction i inv).unit.app q) :=
  (right_unit_total_iff i inv q).symm
end

section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open NamedArithmeticSignature
example : ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
    ∀ e, Entailment.Consistent (ArithmeticNamedProofConnectives.system (ArithmeticUniformIndependent.gamma e)) →
    ∃ φ : Formula, φ.freeVariables = [] ∧
      formulaCode φ = ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
      ¬(SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
        (ArithmeticUniformIndependent.gamma e) φ ∨ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (ArithmeticUniformIndependent.gamma e) (.neg φ)) := by
  obtain ⟨q,all⟩ := ArithmeticUniformIndependent.uniform_independent_sentences
  refine ⟨q,fun e h => ?_⟩
  obtain ⟨p,hc,hw,hp,hn⟩ := all e h
  exact ⟨p,hc,hw,fun bad => bad.elim hp hn⟩

example (T : ArithmeticTheory) [Entailment.Consistent T]
    (h : ∀ A : Set ℕ, ComputablePred (· ∈ A) → ∃ φ : ArithmeticSemisentence 1,
      ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    Numerical.RecursivelyInseparable (ArithmeticSyntax.theoremSupport T)
      (ArithmeticSyntax.refutationSupport T) :=
  ArithmeticSyntax.supports_recursivelyInseparable_of_definability T h
end

section
open Miller
example : ∃ a : ℕ → Set.Icc (0 : ℝ) 1, ∀ r : Set.Icc (0 : ℝ) 1, ∀ d : ℕ,
    (∀ p : ℕ → Fin 2, rho p = a → ∀ k : ℕ, ∃ j : ℕ,
      j ∈ OracleProgram.numberedEval d p k ∧
      |(Rationals.q j : ℝ) - r.val| < ((2 : ℝ)^k)⁻¹) → r = a d := by
  obtain ⟨a,h⟩ := exists_isMiller
  exact ⟨a,fun r d approx => (h d r approx).symm⟩
end

section
open ForkSyntax ForkAxiomClosure
example (i : Bool) (A : Set ℕ) (enum : REPred (· ∈ A))
    (extended : EnumerableCarriers.support (endpointTheory i categoricalTheory) ⊆ theoremCodes A)
    (consistent : ∀ φ : ForkSyntax.Formula, ¬(Derives A φ ∧ Derives A (.neg φ))) :
    ∃ k : ℕ, ¬(Derives A (.atom k) ∨ Derives A (.neg (.atom k))) := by
  obtain ⟨k,hp,hn⟩ := axioms_undecided_atom i A enum extended consistent
  exact ⟨k, fun proof => proof.elim hp hn⟩
end

section
open InductiveDefinition
example {α : Type u} (rules : RuleSet α) (finite : Finitary rules) (x : α) :
    Nonempty (FiniteProofTree rules x) ↔ x ∈ closure rules :=
  (mem_closure_iff_finiteTree rules finite x).symm
end
end ReaderTwo
