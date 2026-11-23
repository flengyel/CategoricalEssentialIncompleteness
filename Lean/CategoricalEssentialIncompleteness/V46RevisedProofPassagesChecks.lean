/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitution
public import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
public import CategoricalEssentialIncompleteness.V46NamedTheoryObservationsProofs
public import CategoricalEssentialIncompleteness.V46MillerCanonicalAxiomIncompleteness
public import CategoricalEssentialIncompleteness.V46MillerParameterizedDeduction

/-! # Boolean substitution, uniform independence and proofs for Miller sequences -/

@[expose] public section
noncomputable section

universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RevisedProofPassages

section BooleanSubstitution
open NullaryBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D] {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)

theorem binder_substitution {W : D} (p : W ⟶ S.substitutionParameters) (y : W ⟶ V)
    (a : W ⟶ S.substitutionCarriers.2) (ha : PairGood S d a) :
    PairGood S d (prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionPair) :=
  quantifier_pair_good S d p y a ha

theorem substitution_values :
    (S.formulaSubstitutionOption ≫ OptionSyntax.map (valuation S d) =
      OptionSyntax.mask (prod.fst ≫ valuation S d) S.formulaSubstitutionOption) ∧
    (S.formulaSubstitution ≫ valuation S d = S.admissibleInclusion ≫ prod.fst ≫ valuation S d) :=
  ⟨substitution_option_value S d, substitution_value S d⟩
end BooleanSubstitution

section UniformIndependence
open ArithmeticUniformSearch ArithmeticUniformIndependent
open PCategoryStruct FailureOfComposition.TypedProgramCategory
open PartialFunctions
local notation "F" => SyntacticModel.modelFunctor 𝗣𝗔 ℕ
local notation "Cpos" => ArithmeticUniformIndependent.positive
local notation "Cneg" => ArithmeticUniformIndependent.negative
attribute [local irreducible] ArithmeticDiagonalCodes.diagonalIndex

theorem proof_search_domains (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e))) (x : ℕ) :
    (Sum.inl x ∈ (F).map (lift Cpos Cneg) (e,x) ↔ (Cneg).val.Evalb ![e,x]) ∧
    (Sum.inr x ∈ (F).map (lift Cpos Cneg) (e,x) ↔ (Cpos).val.Evalb ![e,x]) := by
  have hd := fiber_disjoint e hc
  have hneg := negative_lift_value ℕ Cpos Cneg e hd x
  have hpos := positive_lift_value ℕ Cpos Cneg e hd x
  have hdom := (model_lift_domain ℕ Cpos Cneg e x).mp
  constructor
  · refine ⟨fun hy => ?_, hneg⟩
    rcases hdom ⟨Sum.inl x, hy⟩ with hp | hn
    · have he : (Sum.inl x : ℕ ⊕ ℕ) = Sum.inr x := Part.mem_unique hy (hpos hp)
      cases he
    · exact hn
  · refine ⟨fun hy => ?_, hpos⟩
    rcases hdom ⟨Sum.inr x, hy⟩ with hp | hn
    · exact hp
    · have he : (Sum.inl x : ℕ ⊕ ℕ) = Sum.inr x := Part.mem_unique (hneg hn) hy
      cases he

/-- The interpreted source equation identifies the partial values, including undefinedness. -/
theorem diagonal_partial_value (C C' : Predicate₂) (e n : ℕ)
    (hn : n ∈ (F).map (diagonal C C') e) :
    (F).map ArithmeticDiagonalCodes.sourceParityDiagonal n = (F).map (lift C C') (e,n) := by
  have he : diagonal C C' ≫ ArithmeticDiagonalCodes.sourceParityDiagonal =
      partialPairing (𝟙 (omegaObject 𝗣𝗔)) (diagonal C C') ≫ lift C C' := by
    simpa only [ArithmeticDiagonalCodes.sourceParityDiagonal, Category.assoc] using
      diagonal_equation C C'
  apply Part.ext
  intro y
  refine ⟨fun hy => ?_, diagonal_model_output ℕ C C' e n hn y⟩
  have hcomp : y ∈ (F).map (diagonal C C' ≫ ArithmeticDiagonalCodes.sourceParityDiagonal) e := by
    rw [(F).map_comp, mem_comp]
    exact ⟨n, hn, hy⟩
  rw [he, (F).map_comp, mem_comp] at hcomp
  obtain ⟨p, hp, hout⟩ := hcomp
  exact (Part.mem_unique hp (mem_parameter_pairing ℕ (diagonal C C') e n hn)) ▸ hout

/-- Neither summand search returns a value at the uniform output. Neither signed
numeral instance has a finite derivation in the selected fiber. -/
theorem uniform_finite_derivations (e : ℕ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e))) :
    let n := ArithmeticUniformIndependent.output e
    let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val n
    (F).map ArithmeticDiagonalCodes.sourceParityDiagonal n = (F).map (lift Cpos Cneg) (e,n) ∧
      (¬ ∃ y : ℕ ⊕ ℕ, y ∈ (F).map (lift Cpos Cneg) (e,n)) ∧
      ¬ NamedTheoryObservations.FiniteDerivation (gamma e) φ ∧
      ¬ NamedTheoryObservations.FiniteDerivation (gamma e) (.neg φ) := by
  let n := ArithmeticUniformIndependent.output e
  let φ := NamedTheoryObservations.numeralInstance n
  have hφ : φ.freeVariables = [] := NamedTheoryObservations.numeralInstance_closed n
  have hav := output_avoids e hc
  refine ⟨diagonal_partial_value Cpos Cneg e n (output_mem ℕ Cpos Cneg e),
    fun hy => ((model_lift_domain ℕ Cpos Cneg e n).mp hy).elim hav.1 hav.2, ?_⟩
  have hw : ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
      ArithmeticUniformIndependent.sentence (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val =
      NamedArithmeticSignature.formulaCode φ :=
    (sentence_value e).trans (NamedTheoryObservations.positiveWord_eq n)
  have hs := sentence_code_avoids e hc
  dsimp only at hs
  rw [hw, NamedArithmeticProofSearch.negationWord_formulaCode] at hs
  exact ⟨fun h => hs.1 ((NamedTheoryObservations.theoremSet_iff_eval (gamma e) _).mp
      ((NamedTheoryObservations.theoremSet_iff_finiteDerivation (gamma e) φ hφ).mpr h)),
    fun h => hs.2 ((NamedTheoryObservations.theoremSet_iff_eval (gamma e) _).mp
      ((NamedTheoryObservations.theoremSet_iff_finiteDerivation (gamma e) (.neg φ) hφ).mpr h))⟩
end UniformIndependence

section MillerCuts
open Miller Miller.OrderedFieldSyntax

theorem integer_cut_axioms (a : Point) (n : ℕ) (u : ℤ) (v : ℕ) (hv : 0 < v) :
    ((u : ℝ) / (v : ℝ) < (a n : ℝ) →
      formulaCode (lt (integerTerm (Rationals.integerCode u)) (mul (natural v) (c n))) ∈
        cutAxioms a) ∧
    ((a n : ℝ) < (u : ℝ) / (v : ℝ) →
      formulaCode (lt (mul (natural v) (c n)) (integerTerm (Rationals.integerCode u))) ∈
        cutAxioms a) := by
  let j := Nat.pair (Rationals.integerCode u) (v - 1)
  have hv' : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
  have hq : (Rationals.q j : ℝ) = (u : ℝ) / (v : ℝ) := by
    simp only [j, Rationals.q, Nat.unpair_pair, Rationals.signed_integerCode, hv',
      Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  constructor
  · intro h
    refine Or.inl ⟨n, j, by simpa only [hq] using h, ?_⟩
    simpa only [belowSentence, j, Nat.unpair_pair, hv'] using (formulaCode_belowSentence n j).symm
  · intro h
    refine Or.inr ⟨n, j, by simpa only [hq] using h, ?_⟩
    simpa only [aboveSentence, j, Nat.unpair_pair, hv'] using (formulaCode_aboveSentence n j).symm

private theorem integerCode_signed (k : ℕ) : Rationals.integerCode (Rationals.signed k) = k := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, k = 2 * b := ⟨k / 2, by omega⟩
    rw [Rationals.signed_even]
    rfl
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, k = 2 * b + 1 := ⟨k / 2, by omega⟩
    rw [Rationals.signed_odd]
    rfl

/-- The enumerated cut words are exactly the two strict tests, with an arbitrary
integer numerator and a positive denominator. -/
theorem cut_words_iff_integer_bounds (a : Point) (w : ℕ) :
    w ∈ cutAxioms a ↔ ∃ (n : ℕ) (u : ℤ) (v : ℕ), 0 < v ∧
      (((u : ℝ) / (v : ℝ) < (a n : ℝ) ∧
        formulaCode (lt (integerTerm (Rationals.integerCode u)) (mul (natural v) (c n))) = w) ∨
       ((a n : ℝ) < (u : ℝ) / (v : ℝ) ∧
        formulaCode (lt (mul (natural v) (c n)) (integerTerm (Rationals.integerCode u))) = w)) := by
  have hq (j : ℕ) : (Rationals.q j : ℝ) =
      (Rationals.signed (Nat.unpair j).1 : ℝ) / (((Nat.unpair j).2 + 1 : ℕ) : ℝ) := by
    simp only [Rationals.q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  constructor
  · rintro (⟨n, j, hj, rfl⟩ | ⟨n, j, hj, rfl⟩)
    · refine ⟨n, _, _, Nat.zero_lt_succ _, Or.inl ⟨by simpa only [hq] using hj, ?_⟩⟩
      rw [integerCode_signed]
      exact formulaCode_belowSentence n j
    · refine ⟨n, _, _, Nat.zero_lt_succ _, Or.inr ⟨by simpa only [hq] using hj, ?_⟩⟩
      rw [integerCode_signed]
      exact formulaCode_aboveSentence n j
  · rintro ⟨n, u, v, hv, (⟨h, rfl⟩ | ⟨h, rfl⟩)⟩
    · exact (integer_cut_axioms a n u v hv).1 h
    · exact (integer_cut_axioms a n u v hv).2 h

theorem half_cut_sentences (a : Point) (Γ : Set ℕ) (hΓ : RealClosedBounds.Extends a Γ) (n : ℕ) :
    ((a n : ℝ) < 1/2 → formulaCode (lt (mul (natural 2) (c n)) one) ∈ cutAxioms a ∧
      RealClosedBounds.Proof Γ (lt (mul (natural 2) (c n)) one)) ∧
    (1/2 < (a n : ℝ) → formulaCode (lt one (mul (natural 2) (c n))) ∈ cutAxioms a ∧
      RealClosedBounds.Proof Γ (.neg (lt (mul (natural 2) (c n)) one))) :=
  ⟨fun h => ⟨lower_cut_axiom a n h, RealClosedBounds.lower_cut_gamma_theta a Γ hΓ n h⟩,
   fun h => ⟨upper_cut_axiom a n h, RealClosedBounds.upper_cut_gamma_negtheta a Γ hΓ n h⟩⟩
end MillerCuts

section ParameterizedRules
open Miller Miller.ParameterizedDeduction
variable (a : Point) {V : Total.CanonicalTotal a} {σ π : ℕ → Total.CanonicalTotal a} {d : ℕ}
variable (S : CategoricalSyntax V σ π d) (P : Total.CanonicalTotal a)
local instance : Regular (Over P) := RegularSlices.regular P
local instance : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

theorem nullary_rule_conclusions (A : Subobject (P ⨯ S.sentenceObject)) :
    coprod.inl ≫ (rules a S P (axiomArrow a S P A)).conclusion 0 =
        (constantFamilyFunctor P).map S.logicalAxioms ∧
    coprod.inr ≫ (rules a S P (axiomArrow a S P A)).conclusion 0 =
        axiomArrow a S P A ≫ (constantFamilyFunctor P).map S.sentenceInclusion :=
  ⟨coprod.inl_desc _ _, coprod.inr_desc _ _⟩

theorem parameter_fold (A : Subobject (P ⨯ S.sentenceObject))
    (B : Endofunctor.Algebra (printedRules a S P A).inference) :
    ∃! e : (printedAlgebra a S P A).a.left ⟶ B.a.left,
      ∃ he : e ≫ B.a.hom = (printedAlgebra a S P A).a.hom,
        (printedAlgebra a S P A).str ≫ Over.homMk e he =
          (printedRules a S P A).inference.map (Over.homMk e he) ≫ B.str := by
  refine ⟨(printedFold a S P A B).f.left, ⟨printedFold_conclusion a S P A B,
    printedFold_constructor a S P A B⟩, ?_⟩
  rintro e ⟨he, hconstructor⟩
  let f : printedAlgebra a S P A ⟶ B := ⟨Over.homMk e he, hconstructor.symm⟩
  exact congrArg (fun g : printedAlgebra a S P A ⟶ B => g.f.left) (printedFold_unique a S P A B f)
end ParameterizedRules

section RecoveredAxioms
open Miller Miller.CanonicalAxiomIncompleteness
open SyntacticPredicates
variable (a : Point) {A : Total.CanonicalTotal a}
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S" => NamedSyntaxComparison.canonicalPresentedSyntax a
  (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ π d

theorem recovered_sentence_image (m : A ⟶ (S).sentenceObject) [Mono m] :
    let Γ := recoveredCodes a m
    let hΓ := recoveredCodes_enumerable a m
    ∃ u : A ≅ CanonicalPresentation.chosenAxiomObject a σ π d Γ hΓ,
      u.hom ≫ CanonicalPresentation.chosenAxioms a σ π d Γ hΓ = m ∧
      u.inv ≫ m = CanonicalPresentation.chosenAxioms a σ π d Γ hΓ ∧
      imageSubobject (sentenceConclusion a m) =
        imageSubobject (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ) ∧
      Idem.pull (S).sentenceNegation.hom (Ranges.range (sentenceConclusion a m).hom) =
        CanonicalIncompleteness.refutationIdem a Γ hΓ :=
  ⟨axiomIso a m, axiomIso_inclusion a m, axiomIso_inverse_inclusion a m,
    sentence_image_recovery a m, refutation_recovery a m⟩

/-- In the numerical sentence chart, the range for an arbitrary axiom mono and its
negation preimage test finite proofs of the two signed sentences. -/
theorem recovered_proof_domains (m : A ⟶ (S).sentenceObject) [Mono m]
    (φ : OrderedFieldSyntax.Formula) (hφ : φ.freeVariables = []) :
    (OrderedFieldSyntax.formulaCode φ ∈ CarrierIdempotents.support
      (CanonicalIncompleteness.chartIdemIso a (Ranges.range (sentenceConclusion a m).hom)) ↔
      RealClosedBounds.Proof (recoveredCodes a m) φ) ∧
    (OrderedFieldSyntax.formulaCode φ ∈ CarrierIdempotents.support
      (CanonicalIncompleteness.chartIdemIso a (Idem.pull (S).sentenceNegation.hom
        (Ranges.range (sentenceConclusion a m).hom))) ↔
      RealClosedBounds.Proof (recoveredCodes a m) (.neg φ)) := by
  change (_ ∈ CarrierIdempotents.support
    (CanonicalIncompleteness.chartIdemIso a (theoremIdem a m)) ↔ _) ∧
    (_ ∈ CarrierIdempotents.support
      (CanonicalIncompleteness.chartIdemIso a (refutationIdem a m)) ↔ _)
  rw [literal_range_conjugacy, refutation_recovery, CanonicalIncompleteness.refutation_conjugacy]
  exact ⟨(Incompleteness.theorem_word_iff a _ _ φ).trans (and_iff_left hφ),
    (Incompleteness.refutation_word_iff a _ _ φ).trans (and_iff_left hφ)⟩
end RecoveredAxioms

end CategoricalEssentialIncompleteness.V46.RevisedProofPassages

#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.binder_substitution
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.substitution_values
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.proof_search_domains
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.diagonal_partial_value
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.uniform_finite_derivations
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.integer_cut_axioms
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.cut_words_iff_integer_bounds
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.half_cut_sentences
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.nullary_rule_conclusions
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.parameter_fold
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.recovered_sentence_image
#print axioms CategoricalEssentialIncompleteness.V46.RevisedProofPassages.recovered_proof_domains
