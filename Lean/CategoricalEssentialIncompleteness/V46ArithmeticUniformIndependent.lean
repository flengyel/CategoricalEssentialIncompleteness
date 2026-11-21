/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformPredicates
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityFibers
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumeration
public import CategoricalEssentialIncompleteness.V46ArithmeticInternalComparison

/-! # Uniform independent sentences for the indexed arithmetic family

The family provability predicate and its numeral-fiber comparison give one
sentence morphism. Independence requires consistency of the selected fiber.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformIndependent
open NamedArithmeticSignature

abbrev gamma (e : ℕ) : Carrier :=
  ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e

abbrev provability : 𝚺₁.Semisentence 2 :=
  ArithmeticIndexedProvability.printedProvability ArithmeticIndexedPAEnumeration.axiomCodes

abbrev positive : 𝚺₁.Semisentence 2 :=
  ArithmeticUniformSearch.positive provability NamedArithmeticDiagonalBounds.namedAlpha

abbrev negative : 𝚺₁.Semisentence 2 :=
  ArithmeticUniformSearch.negative provability NamedArithmeticDiagonalBounds.namedAlpha

/-- The uniform sentence morphism from the parameter object to sentences. -/
def sentence : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence :=
  ArithmeticUniformSearch.proofSentenceMorphism provability

def output (e : ℕ) : ℕ := ArithmeticUniformSearch.output ℕ positive negative e

private theorem standard_parameter_cast (P : 𝚺₁.Semisentence 2) (e z : ℕ) :
    P.val.Evalb (M := ℕ) ![e,z] ↔
      P.val.Evalb (M := ℕ) ![@Nat.cast ℕ (natCast ℕ) e,z] :=
  (Iff.of_eq (congrArg (fun w : ℕ => P.val.Evalb (M := ℕ) ![w,z]) (natCast_nat e))).symm

private theorem provability_standard_fiber (e z : ℕ) :
    provability.val.Evalb ![e,z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (gamma e)).val.Evalb ![z] :=
  (standard_parameter_cast provability e z).trans
    (ArithmeticIndexedProvability.printedProvability_numeral ℕ
      ArithmeticIndexedPAEnumeration.axiomCodes e z)

/-- Specializing the family conclusion at a numeral gives the positive
proof-search predicate for that fiber. -/
theorem positive_fiber (e x : ℕ) :
    positive.val.Evalb ![e,x] ↔
      (NamedArithmeticProofSearch.positive (gamma e)
        NamedArithmeticDiagonalBounds.namedAlpha).val.Evalb ![x] :=
  (ArithmeticUniformSearch.positive_eval ℕ provability
    NamedArithmeticDiagonalBounds.namedAlpha e x).trans
      ((provability_standard_fiber e
        (NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha x)).trans
          (NamedArithmeticProofSearch.positive_eval ℕ (gamma e)
            NamedArithmeticDiagonalBounds.namedAlpha x).symm)

theorem negative_fiber (e x : ℕ) :
    negative.val.Evalb ![e,x] ↔
      (NamedArithmeticProofSearch.negative (gamma e)
        NamedArithmeticDiagonalBounds.namedAlpha).val.Evalb ![x] :=
  (ArithmeticUniformSearch.negative_eval ℕ provability
    NamedArithmeticDiagonalBounds.namedAlpha e x).trans
      ((provability_standard_fiber e
        (NamedArithmeticProofSearch.negationWord ℕ
          (NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha x))).trans
            (NamedArithmeticProofSearch.negative_eval_word ℕ (gamma e)
              NamedArithmeticDiagonalBounds.namedAlpha
              NamedArithmeticDiagonalBounds.namedAlpha_freeVariables x).symm)

theorem fiber_disjoint (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e)))
    (x : ℕ) : ¬ (positive.val.Evalb ![e,x] ∧ negative.val.Evalb ![e,x]) := by
  rintro ⟨hp,hn⟩
  have ht := (NamedArithmeticProofSearch.positive_eval ℕ (gamma e)
    NamedArithmeticDiagonalBounds.namedAlpha x).mp ((positive_fiber e x).mp hp)
  have hr := (NamedArithmeticProofSearch.negative_eval_word ℕ (gamma e)
    NamedArithmeticDiagonalBounds.namedAlpha
    NamedArithmeticDiagonalBounds.namedAlpha_freeVariables x).mp ((negative_fiber e x).mp hn)
  exact NamedGammaEvidenceSoundness.standard_sentence_evidence_disjoint (gamma e)
    (ArithmeticIndexedPAEnumeration.fiber_extendsPA e) hc
    (NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha x)
    (NamedArithmeticFixedSubstitution.value_sentence (M := ℕ)
      NamedArithmeticDiagonalBounds.namedAlpha NamedArithmeticDiagonalBounds.namedAlpha_freeVariables x)
    ⟨ht,hr⟩

/-- The PA-axiom enumeration gives the positive diagonal bound in every fiber. -/
theorem alpha_bound (e x : ℕ) (hx : ArithmeticDiagonalCodes.alpha.val.Evalb ![x]) :
    positive.val.Evalb ![e,x] :=
  (positive_fiber e x).mpr
    (NamedArithmeticDiagonalBounds.semantic_positive ℕ (gamma e)
      (ArithmeticIndexedPAEnumeration.fiber_extendsPA e) x hx)

theorem beta_bound (e x : ℕ) (hx : ArithmeticDiagonalCodes.beta.val.Evalb ![x]) :
    negative.val.Evalb ![e,x] :=
  (negative_fiber e x).mpr
    (NamedArithmeticDiagonalBounds.semantic_negative ℕ (gamma e)
      (ArithmeticIndexedPAEnumeration.fiber_extendsPA e) x hx)

/-- The uniform source morphism avoids both predicates in every consistent fiber. -/
theorem output_avoids (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e))) :
    ¬ positive.val.Evalb ![e,output e] ∧ ¬ negative.val.Evalb ![e,output e] :=
  ArithmeticUniformSearch.output_avoids_at ℕ positive negative e
    (fiber_disjoint e hc) (alpha_bound e) (beta_bound e)

/-- The sentence morphism has value Θ applied to the uniform source output. -/
theorem sentence_value (e : ℕ) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map sentence
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val =
        NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha (output e) :=
  ArithmeticUniformSearch.proofSentenceMorphism_value provability e

/-- Equality transport is established for an opaque predicate before
specializing the large concrete family and sentence expressions. -/
private theorem avoids_word_transport (R : Carrier) (u v : ℕ) (he : u = v)
    (h : ¬ R.val.Evalb ![v]) : ¬ R.val.Evalb ![u] :=
  fun hu => h (Eq.mp (congrArg (fun w : ℕ => R.val.Evalb ![w]) he) hu)

/-- The generated theorem predicate and its negation preimage both
exclude the interpreted word of the sentence morphism. -/
theorem sentence_code_avoids (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e))) :
    let word := ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map sentence
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val
    ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb ![word] ∧
      ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb
          ![NamedArithmeticProofSearch.negationWord ℕ word] := by
  have hav := output_avoids e hc
  have hp : ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb
        ![NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha (output e)] := by
    intro h
    exact hav.1 ((positive_fiber e (output e)).mpr
      ((NamedArithmeticProofSearch.positive_eval ℕ (gamma e)
        NamedArithmeticDiagonalBounds.namedAlpha (output e)).mpr h))
  have hn : ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb
        ![NamedArithmeticProofSearch.negationWord ℕ
          (NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha (output e))] := by
    intro h
    exact hav.2 ((negative_fiber e (output e)).mpr
      ((NamedArithmeticProofSearch.negative_eval_word ℕ (gamma e)
        NamedArithmeticDiagonalBounds.namedAlpha
        NamedArithmeticDiagonalBounds.namedAlpha_freeVariables (output e)).mpr h))
  exact ⟨avoids_word_transport _ _ _ (sentence_value e) hp,
    avoids_word_transport _ _ _ (congrArg (NamedArithmeticProofSearch.negationWord ℕ)
      (sentence_value e)) hn⟩

/-- The single morphism excludes the family theorem image and
its negation preimage at each externally consistent numeral fiber. -/
theorem uniform_independent_sentence_codes :
    ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
      ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e)) →
        let word := ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val
        ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb ![word] ∧
          ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound (gamma e)).val.Evalb
              ![NamedArithmeticProofSearch.negationWord ℕ word] :=
  ⟨sentence,fun e hc => sentence_code_avoids e hc⟩

/-- Both Hilbert proof possibilities are excluded at the named numeral instance, with its
original variable names and expanded numeral. -/
theorem independent_instance (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e))) :
    let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (output e)
    φ.freeVariables = [] ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) φ ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) (.neg φ) := by
  have hav := output_avoids e hc
  have hr := NamedArithmeticDiagonalBounds.standard_instance_result ArithmeticDiagonalCodes.alpha.val (output e)
  refine ⟨hr.2,?_,?_⟩
  · intro hd
    exact hav.1 ((positive_fiber e (output e)).mpr
      (ArithmeticInternalComparison.native_instance_positive (gamma e)
        ArithmeticDiagonalCodes.alpha.val (output e) hd))
  · intro hd
    exact hav.2 ((negative_fiber e (output e)).mpr
      (ArithmeticInternalComparison.native_instance_negative (gamma e)
        ArithmeticDiagonalCodes.alpha.val (output e) hd))

/-- Theorem 8.6: one morphism `q : E ⟶ S` in `B_PA` gives an independent sentence at every
consistent fiber `Γ_e`. -/
theorem uniform_independent_sentences :
    ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
      ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e)) →
        ∃ φ : Formula, φ.freeVariables = [] ∧
          formulaCode φ =
            ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
              (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) (.neg φ) := by
  refine ⟨sentence,?_⟩
  intro e hc
  let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (output e)
  have hr := NamedArithmeticDiagonalBounds.standard_instance_result ArithmeticDiagonalCodes.alpha.val (output e)
  obtain ⟨hclosed,hpos,hneg⟩ := independent_instance e hc
  exact ⟨φ,hclosed,hr.1.symm.trans (sentence_value e).symm,hpos,hneg⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticUniformIndependent
