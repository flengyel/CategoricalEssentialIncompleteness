/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityCore
public import CategoricalEssentialIncompleteness.V46NamedGammaEvidenceSoundness
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertReplacement
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Essential incompleteness from the proved categorical separator obstruction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
open NamedArithmeticSignature
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound

/-- Sigma-one carrier membership is c.e.; no derivability presentation
or imported arithmetic incompleteness result is used. -/
theorem carrier_enumerable (C : SyntacticPredicates.Carrier) :
    REPred (fun n : ℕ => C.val.Evalb (M := ℕ) ![n]) := by
  apply rePred_iff_sigma1.mpr
  refine ⟨C.rew Rew.emb,?_⟩
  intro v
  simp [← Matrix.fun_eq_vec_one]

theorem carrier_set_enumerable (C : SyntacticPredicates.Carrier) :
    REPred (· ∈ {n : ℕ | C.val.Evalb (M := ℕ) ![n]}) :=
  carrier_enumerable C

theorem theoremSet_enumerable (A : SyntacticPredicates.Carrier) :
    REPred (· ∈ theoremSet A) :=
  carrier_set_enumerable (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A)

theorem refutationSet_enumerable (A : SyntacticPredicates.Carrier) :
    REPred (· ∈ refutationSet A) :=
  carrier_set_enumerable (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound A)

theorem carrier_set_disjoint (C Q : SyntacticPredicates.Carrier)
    (h : ∀ n : ℕ, ¬ (C.val.Evalb (M := ℕ) ![n] ∧ Q.val.Evalb (M := ℕ) ![n])) :
    Disjoint {n : ℕ | C.val.Evalb (M := ℕ) ![n]}
      {n : ℕ | Q.val.Evalb (M := ℕ) ![n]} :=
  Set.disjoint_left.mpr (fun n hp hn => h n ⟨hp,hn⟩)

theorem eval_literal_set (C : SyntacticPredicates.Carrier) (w : ℕ)
    (h : w ∈ {z : ℕ | C.val.Evalb (M := ℕ) ![z]}) : C.val.Evalb (M := ℕ) ![w] := h

theorem carrier_eval_transport {C Q : SyntacticPredicates.Carrier} (h : C = Q)
    (w : ℕ) (hw : C.val.Evalb (M := ℕ) ![w]) : Q.val.Evalb (M := ℕ) ![w] := h ▸ hw

theorem theoremCarrier_variables_eq (A : SyntacticPredicates.Carrier) :
    SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A =
    SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      (NamedPostfixEncoding.variableCarrier : SyntacticPredicates.PredicateCategory 𝗣𝗔)
      functionSymbols relationSymbols bound A :=
  congrArg (fun V : SyntacticPredicates.PredicateCategory 𝗣𝗔 =>
    SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 V functionSymbols relationSymbols bound A)
      (show (variableSymbols : SyntacticPredicates.PredicateCategory 𝗣𝗔) =
        NamedPostfixEncoding.variableCarrier from rfl)

theorem refutationCarrier_variables_eq (A : SyntacticPredicates.Carrier) :
    SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A =
    SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      (NamedPostfixEncoding.variableCarrier : SyntacticPredicates.PredicateCategory 𝗣𝗔)
      functionSymbols relationSymbols bound A :=
  congrArg (fun V : SyntacticPredicates.PredicateCategory 𝗣𝗔 =>
    SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔 V functionSymbols relationSymbols bound A)
      (show (variableSymbols : SyntacticPredicates.PredicateCategory 𝗣𝗔) =
        NamedPostfixEncoding.variableCarrier from rfl)

/-- Corollary 8.4 for the theorem/refutation programs. The semantic model used for
disjointness is constructed from external consistency; the nonseparator is the
categorical Corollary 3.2. -/
theorem recursively_inseparable (A : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) :
    Numerical.RecursivelyInseparable (theoremSet A) (refutationSet A) :=
  ⟨Set.disjoint_left.mpr (fun word hp hn =>
      NamedGammaEvidenceSoundness.consistent_standard_word_disjoint A hPA hc word
        ⟨carrier_eval_transport (theoremCarrier_variables_eq A) word
            (eval_literal_set _ word hp),
          carrier_eval_transport (refutationCarrier_variables_eq A) word
            (eval_literal_set _ word hn)⟩),
    no_recursive_separator A hPA⟩

/-- The parallel-enumeration argument is first proved for opaque sets
and an opaque computable function, before any large syntax predicates
are substituted into it. The contradiction is the categorical separator
theorem already proved above. -/
theorem recursive_fiber_gap (P Q : Set ℕ) (hd : Disjoint P Q)
    (hP : REPred (· ∈ P)) (hQ : REPred (· ∈ Q))
    (f : ℕ → ℕ) (hf : Computable f)
    (hAlpha : ∀ n : ℕ, ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n] → f n ∈ P)
    (hBeta : ∀ n : ℕ, ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n] → f n ∈ Q) :
    ∃ n : ℕ, f n ∉ P ∧ f n ∉ Q := by
  classical
  by_contra hnone
  have hcover : ∀ n : ℕ, f n ∈ P ∨ f n ∈ Q := by
    intro n
    by_contra h
    exact hnone ⟨n,not_or.mp h⟩
  have hcompl : ∀ n : ℕ, f n ∈ Q ↔ f n ∉ P := by
    intro n
    constructor
    · intro hn hp
      exact Set.disjoint_left.mp hd hp hn
    · intro hp
      exact (hcover n).resolve_left hp
  have hrP : REPred (fun n => f n ∈ P) := REPred.comp hf hP
  have hrQ : REPred (fun n => f n ∈ Q) := REPred.comp hf hQ
  have hdec : ComputablePred (fun n => f n ∈ P) :=
    ComputablePred.computable_iff_re_compl_re'.mpr ⟨hrP,REPred.of_eq hrQ hcompl⟩
  apply diagonal_no_recursive_separator
  refine ⟨f ⁻¹' P,hdec,hAlpha,?_⟩
  apply Set.disjoint_left.mpr
  intro n hnP hnBeta
  exact Set.disjoint_left.mp hd hnP (hBeta n hnBeta)

/-- Literal substituted instances inherit the opaque-set result through the proved
positive and negative literal-word charts. -/
theorem exists_independent_value_of_bounds (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (hd : Disjoint (theoremSet A) (refutationSet A))
    (hAlpha : ∀ n : ℕ, ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.positive A φ).val.Evalb (M := ℕ) ![n])
    (hBeta : ∀ n : ℕ, ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.negative A φ).val.Evalb (M := ℕ) ![n]) :
    ∃ n : ℕ, NamedArithmeticFixedSubstitution.value (M := ℕ) φ n ∉ theoremSet A ∧
      NamedArithmeticFixedSubstitution.value (M := ℕ) φ n ∉ refutationSet A :=
  recursive_fiber_gap (theoremSet A) (refutationSet A) hd
    (theoremSet_enumerable A) (refutationSet_enumerable A)
    (NamedArithmeticFixedSubstitution.value (M := ℕ) φ)
    (NamedArithmeticFixedSubstitution.value_primrec φ).to_comp
    (fun n hn => positive_member A φ n (hAlpha n hn))
    (fun n hn => negative_member A φ hφ n (hBeta n hn))

/-- A formula-generic proof returns a closed named sentence. All syntax and value
computations remain on the same named presentation. -/
theorem sentence_incomplete_of_bounds (A : SyntacticPredicates.Carrier)
    (φ : NamedArithmeticSignature.Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (hd : Disjoint (theoremSet A) (refutationSet A))
    (hAlpha : ∀ n : ℕ, ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.positive A φ).val.Evalb (M := ℕ) ![n])
    (hBeta : ∀ n : ℕ, ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n] →
      (NamedArithmeticProofSearch.negative A φ).val.Evalb (M := ℕ) ![n]) :
    ∃ ψ : NamedArithmeticSignature.Formula, ψ.freeVariables = [] ∧
      ¬ D A ψ ∧ ¬ D A (.neg ψ) := by
  obtain ⟨n,hpositive,hnegative⟩ := exists_independent_value_of_bounds A φ hφ hd hAlpha hBeta
  obtain ⟨out,_,hvalue,hclosed⟩ := NamedArithmeticFixedSubstitution.standard_literal_result φ hφ n
  refine ⟨out,hclosed,?_,?_⟩
  · intro hp
    have h := SyntacticNamedHilbert.native_sentence_theorem
      functionSymbols relationSymbols bound A hp hclosed
    have hm : formulaCode out ∈ theoremSet A :=
      mem_literal_set (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A) _
        (carrier_eval_transport (theoremCarrier_variables_eq A).symm _ h)
    exact hpositive (hvalue.symm ▸ hm)
  · intro hn
    have h := SyntacticNamedHilbert.native_sentence_refutation
      functionSymbols relationSymbols bound A hn hclosed
    have hm : formulaCode out ∈ refutationSet A :=
      mem_literal_set (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A) _
        (carrier_eval_transport (refutationCarrier_variables_eq A).symm _ h)
    exact hnegative (hvalue.symm ▸ hm)

/-- Essential incompleteness for the Gamma. The model/disjointness and both bounds are
proved from the consistency and PA-extension hypotheses. -/
theorem sentence_incomplete (A : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) :
    ∃ φ : NamedArithmeticSignature.Formula, φ.freeVariables = [] ∧
      ¬ D A φ ∧ ¬ D A (.neg φ) :=
  sentence_incomplete_of_bounds A NamedArithmeticDiagonalBounds.namedAlpha
    NamedArithmeticDiagonalBounds.namedAlpha_freeVariables
    (recursively_inseparable A hPA hc).1
    (NamedArithmeticDiagonalBounds.standard_positive_of_axioms_admissible A
      (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hPA))
    (NamedArithmeticDiagonalBounds.standard_negative_of_axioms_admissible A
      (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hPA))

/-- Derivability of each original enumerated sentence is the concrete extension condition;
the Hilbert replacement induction then transports the PA axiom proofs. -/
theorem extendsPA_of_axiom_extension (A B : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ φ : NamedArithmeticSignature.Formula,
      A.val.Evalb (M := ℕ) ![formulaCode φ] → φ.freeVariables = [] → D B φ) :
    ArithmeticNamedAxiomComparison.ExtendsPA B := by
  intro φ hφ
  exact SyntacticNamedHilbert.replace_axioms functionSymbols relationSymbols bound A B
    hAB (hPA φ hφ)

/-- Every consistent c.e. sentence extension is incomplete, using the axiom-extension
comparison and the categorical result. -/
theorem extension_sentence_incomplete (A B : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ φ : NamedArithmeticSignature.Formula,
      A.val.Evalb (M := ℕ) ![formulaCode φ] → φ.freeVariables = [] → D B φ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    ∃ φ : NamedArithmeticSignature.Formula, φ.freeVariables = [] ∧
      ¬ D B φ ∧ ¬ D B (.neg φ) :=
  sentence_incomplete B (extendsPA_of_axiom_extension A B hPA hAB) hc

theorem incomplete_system (A : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) :
    Entailment.Incomplete (ArithmeticNamedProofConnectives.system A) := by
  obtain ⟨φ,_,hp,hn⟩ := sentence_incomplete A hPA hc
  exact ⟨φ,
    fun h => hp ((NamedHilbertPropositional.system_provable_iff functionSymbols
      relationSymbols bound (ArithmeticNamedProofConnectives.system A) φ).mp h),
    fun h => hn ((NamedHilbertPropositional.system_provable_iff functionSymbols
      relationSymbols bound (ArithmeticNamedProofConnectives.system A) (.neg φ)).mp h)⟩

theorem extension_incomplete_system (A B : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ φ : NamedArithmeticSignature.Formula,
      A.val.Evalb (M := ℕ) ![formulaCode φ] → φ.freeVariables = [] → D B φ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    Entailment.Incomplete (ArithmeticNamedProofConnectives.system B) :=
  incomplete_system B (extendsPA_of_axiom_extension A B hPA hAB) hc

/-- Inclusion of the c.e. sentence presentations is a concrete instance
of the preceding derivability-extension theorem. -/
theorem enumeration_extension_incomplete (A B : SyntacticPredicates.Carrier)
    (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ word : ℕ, A.val.Evalb (M := ℕ) ![word] → B.val.Evalb (M := ℕ) ![word])
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    Entailment.Incomplete (ArithmeticNamedProofConnectives.system B) := by
  apply extension_incomplete_system A B hPA ?_ hc
  intro φ hφ hclosed
  exact .axiom φ (hAB (formulaCode φ) hφ) hclosed

end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
