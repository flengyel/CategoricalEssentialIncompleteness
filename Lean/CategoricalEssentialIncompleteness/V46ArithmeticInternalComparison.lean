/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticComparisonTarget
public import CategoricalEssentialIncompleteness.V46ArithmeticDomainExtension
public import CategoricalEssentialIncompleteness.V46NamedGammaEvidenceSoundness
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsPrinted
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRefutations

/-! # The printed internal arithmetic comparison for the actual Gamma

The hypotheses concern the given literal enumeration, its native PA axiom
proofs and external consistency. The target comparison supplies a total
source morphism. Its standard numerical values give actual named numeral
instances undecidable in the original native finite calculus.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory Filter
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticInternalComparison
open NamedArithmeticSignature

/-- A zero composite inverse image excludes its displayed predicate at
every actual output. The proof is given before arithmetic specialization. -/
theorem avoid_composite_pull {A B C : Pfn} (f : A ⟶ B) (theta : B ⟶ C)
    (t : Idem C) (R : B → Prop)
    (hTheta : Idem.pull theta t = setIdem {b : B | R b})
    (hzero : Idem.pull (f ≫ theta) t = ⊥)
    (a : A) (b : B) (hb : b ∈ f a) : ¬ R b := by
  have h : Idem.pull f (setIdem {b : B | R b}) = ⊥ :=
    (congrArg (Idem.pull f) hTheta).symm.trans
      ((Idem.pull_comp f theta t).symm.trans hzero)
  exact ArithmeticSetModelLaws.pull_zero_not_mem f R h a b hb

/-- Congruence is proved at an opaque target object before choosing
its arithmetic splitting-domain representation. -/
theorem join_pull_congr {X : Pfn} {t u : Idem X} {f g : X ⟶ X}
    (ht : t = u) (hf : f = g) :
    t ⊔ Idem.pull f t = u ⊔ Idem.pull g u :=
  congrArg₂ (fun (a : Idem X) (n : X ⟶ X) => a ⊔ Idem.pull n a) ht hf

/-- A native proof of an actual named numeral instance lies in the
constructed positive predicate, before the diagonal formula is specialized. -/
theorem native_instance_positive (A : Carrier) (φ : ArithmeticSemisentence 1) (n : ℕ)
    (hd : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (NamedArithmeticDiagonalBounds.instanceFormula φ n)) :
    (NamedArithmeticProofSearch.positive A
      (NamedArithmeticUnarySubstitution.namedFormula φ)).val.Evalb (M := ℕ) ![n] := by
  have hr := NamedArithmeticDiagonalBounds.standard_instance_result φ n
  have ht := SyntacticNamedHilbert.native_sentence_theorem functionSymbols relationSymbols bound A hd hr.2
  apply (NamedArithmeticProofSearch.positive_eval ℕ A
    (NamedArithmeticUnarySubstitution.namedFormula φ) n).mpr
  have hw : NamedArithmeticFixedSubstitution.value
      (NamedArithmeticUnarySubstitution.namedFormula φ) n =
      formulaCode (NamedArithmeticDiagonalBounds.instanceFormula φ n) := hr.1
  exact Eq.mpr (congrArg (fun word : ℕ =>
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]) hw) ht

/-- The corresponding native negative proof lies in the actual
refutation image of that same original sentence word. -/
theorem native_instance_negative (A : Carrier) (φ : ArithmeticSemisentence 1) (n : ℕ)
    (hd : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (.neg (NamedArithmeticDiagonalBounds.instanceFormula φ n))) :
    (NamedArithmeticProofSearch.negative A
      (NamedArithmeticUnarySubstitution.namedFormula φ)).val.Evalb (M := ℕ) ![n] := by
  have hr := NamedArithmeticDiagonalBounds.standard_instance_result φ n
  have ht := SyntacticNamedHilbert.native_sentence_refutation functionSymbols relationSymbols bound A hd hr.2
  apply (NamedArithmeticProofSearch.negative_literal_refutation ℕ A
    (NamedArithmeticUnarySubstitution.namedFormula φ)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables φ) n).mpr
  have hw : NamedArithmeticFixedSubstitution.value
      (NamedArithmeticUnarySubstitution.namedFormula φ) n =
      formulaCode (NamedArithmeticDiagonalBounds.instanceFormula φ n) := hr.1
  exact Eq.mpr (congrArg (fun word : ℕ =>
    (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]) hw) ht

variable (A : Carrier)
variable (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
variable (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A))
include hPA hc

/-- The actual categorical comparison theorem, with every evidence and
bound premise proved from the stated arithmetic Gamma hypotheses. -/
theorem standard_comparison :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g ≫
        ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
          ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (ArithmeticLiteralCoordinates.theory ℕ A) = ⊥ ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g ≫
        ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
          ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
          (ArithmeticLiteralCoordinates.theory ℕ A)) = ⊥ ∧
      ArithmeticLiteralCoordinates.theory ℕ A ⊔
        Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
          (ArithmeticLiteralCoordinates.theory ℕ A) ≠ ⊤ := by
  apply ArithmeticComparisonTarget.comparison_of_evidence_bounds A ℕ
  · intro s
    exact NamedGammaEvidenceSoundness.standard_sentence_evidence_disjoint A hPA hc s.val s.property
  · exact NamedArithmeticDiagonalBounds.semantic_positive ℕ A hPA
  · exact NamedArithmeticDiagonalBounds.semantic_negative ℕ A hPA

/-- The same categorical theorem applies to every actual arithmetic
ultrapower, including all its nonstandard sentence and proof inputs. -/
theorem ultrapower_comparison {I : Type} (U : Ultrafilter I) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map g ≫
        ArithmeticLiteralCoordinates.thetaMap (ArithmeticUltrapower.Model U)
          ArithmeticComparisonTarget.diagonalFormula ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A) = ⊥ ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map g ≫
        ArithmeticLiteralCoordinates.thetaMap (ArithmeticUltrapower.Model U)
          ArithmeticComparisonTarget.diagonalFormula ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap (ArithmeticUltrapower.Model U))
          (ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A)) = ⊥ ∧
      ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A ⊔
        Idem.pull (ArithmeticLiteralCoordinates.negationMap (ArithmeticUltrapower.Model U))
          (ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A) ≠ ⊤ := by
  apply ArithmeticComparisonTarget.comparison_of_evidence_bounds A (ArithmeticUltrapower.Model U)
  · intro s
    exact NamedGammaEvidenceSoundness.ultrapower_sentence_evidence_disjoint A hPA hc U s.val s.property
  · exact NamedArithmeticDiagonalBounds.semantic_positive (ArithmeticUltrapower.Model U) A hPA
  · exact NamedArithmeticDiagonalBounds.semantic_negative (ArithmeticUltrapower.Model U) A hPA

/-- The standard interpretation of the actual constructed sentence range
is not covered by that range together with its negated inverse image. -/
theorem standard_incomplete :
    ArithmeticLiteralCoordinates.theory ℕ A ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
        (ArithmeticLiteralCoordinates.theory ℕ A) ≠ ⊤ := by
  obtain ⟨_,_,_,_,h⟩ := standard_comparison A hPA hc
  exact h

theorem ultrapower_incomplete {I : Type} (U : Ultrafilter I) :
    ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap (ArithmeticUltrapower.Model U))
        (ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A) ≠ ⊤ := by
  obtain ⟨_,_,_,_,h⟩ := ultrapower_comparison A hPA hc U
  exact h

/-- The printed chosen-domain interpretation under N, exposed as
mapIdem of the actual source sentence range and the actual source negation. -/
theorem interpreted_standard_incomplete :
    (ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension ℕ).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤ := by
  have he := join_pull_congr
    (ArithmeticDomainExtension.interpreted_theory ℕ A)
    (ArithmeticDomainExtension.interpreted_negation ℕ)
  intro h
  exact standard_incomplete A hPA hc (he.symm.trans h)

/-- The same actual source objects are incomplete in every printed
arithmetic ultrapower interpretation. -/
theorem interpreted_ultrapower_incomplete {I : Type} (U : Ultrafilter I) :
    (ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤ := by
  have he := join_pull_congr
    (ArithmeticDomainExtension.interpreted_theory (ArithmeticUltrapower.Model U) A)
    (ArithmeticDomainExtension.interpreted_negation (ArithmeticUltrapower.Model U))
  intro h
  exact ultrapower_incomplete A hPA hc U (he.symm.trans h)

/-- The actual source sentence-theory idempotent is incomplete. This is
reflected from its proved standard canonical-domain interpretation. -/
theorem source_incomplete :
    ArithmeticDomainExtension.sentenceTheory A ⊔
      Idem.pull ArithmeticDomainExtension.sentenceNegation
        (ArithmeticDomainExtension.sentenceTheory A) ≠ ⊤ :=
  ArithmeticDomainExtension.source_noncoverage ℕ A (standard_incomplete A hPA hc)

/-- The total source morphism provided by the categorical theorem has a
standard numerical function of actual outputs. Every computed literal
named numeral instance is closed and has neither native finite proof. -/
theorem total_undecidable_family :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      ∃ gamma : ℕ → ℕ,
        (∀ n : ℕ, gamma n ∈ (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g n) ∧
        ∀ n : ℕ,
          let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (gamma n)
          ArithmeticComparisonTarget.diagonalFormula.substitute 0 (numeral (gamma n)) = some φ ∧
          φ.freeVariables = [] ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A (.neg φ) := by
  obtain ⟨g,hg,hpositive,hnegative,_⟩ := standard_comparison A hPA hc
  let f : PartialFun.of ℕ ⟶ PartialFun.of ℕ := (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g
  have hf : isTotal f := (SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).map_total g hg
  let gamma : ℕ → ℕ := ArithmeticSetModelLaws.totalValue f hf
  have hgamma (n : ℕ) : gamma n ∈ f n := ArithmeticSetModelLaws.totalValue_mem f hf n
  have hp (n : ℕ) : ¬ (NamedArithmeticProofSearch.positive A
      ArithmeticComparisonTarget.diagonalFormula).val.Evalb ![gamma n] :=
    avoid_composite_pull f
      (ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
        ArithmeticComparisonTarget.diagonalFormula_freeVariables)
      (ArithmeticLiteralCoordinates.theory ℕ A)
      (fun k : ℕ => (NamedArithmeticProofSearch.positive A
        ArithmeticComparisonTarget.diagonalFormula).val.Evalb ![k])
      (ArithmeticLiteralCoordinates.theta_theory_pull ℕ A ArithmeticComparisonTarget.diagonalFormula
        ArithmeticComparisonTarget.diagonalFormula_freeVariables)
      hpositive n (gamma n) (hgamma n)
  have hn (n : ℕ) : ¬ (NamedArithmeticProofSearch.negative A
      ArithmeticComparisonTarget.diagonalFormula).val.Evalb ![gamma n] :=
    avoid_composite_pull f
      (ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
        ArithmeticComparisonTarget.diagonalFormula_freeVariables)
      (Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ) (ArithmeticLiteralCoordinates.theory ℕ A))
      (fun k : ℕ => (NamedArithmeticProofSearch.negative A
        ArithmeticComparisonTarget.diagonalFormula).val.Evalb ![k])
      (ArithmeticLiteralCoordinates.theta_refutation_pull ℕ A ArithmeticComparisonTarget.diagonalFormula
        ArithmeticComparisonTarget.diagonalFormula_freeVariables)
      hnegative n (gamma n) (hgamma n)
  refine ⟨g,hg,gamma,hgamma,?_⟩
  intro n
  let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (gamma n)
  have hr := NamedArithmeticDiagonalBounds.standard_instance_result ArithmeticDiagonalCodes.alpha.val (gamma n)
  refine ⟨ArithmeticNamedProofTranslation.expanded_instance_substitution ArithmeticDiagonalCodes.alpha.val (gamma n),
    hr.2,?_,?_⟩
  · intro hd
    exact hp n (native_instance_positive A ArithmeticDiagonalCodes.alpha.val (gamma n) hd)
  · intro hd
    exact hn n (native_instance_negative A ArithmeticDiagonalCodes.alpha.val (gamma n) hd)

/-- The full printed Theorem 7.3: source incompleteness, both printed
interpretation scopes and the total source family of native undecidable
instances. Each conclusion comes from the categorical comparison. -/
theorem internal_comparison :
    (ArithmeticDomainExtension.sentenceTheory A ⊔
      Idem.pull ArithmeticDomainExtension.sentenceNegation
        (ArithmeticDomainExtension.sentenceTheory A) ≠ ⊤) ∧
    ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension ℕ).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤) ∧
    (∀ (I : Type) (U : Ultrafilter I),
      (ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A) ⊔
        Idem.pull ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).toFunctor.map
          ArithmeticDomainExtension.sentenceNegation)
          ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
            (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤) ∧
    (∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      ∃ gamma : ℕ → ℕ,
        (∀ n : ℕ, gamma n ∈ (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g n) ∧
        ∀ n : ℕ,
          let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (gamma n)
          ArithmeticComparisonTarget.diagonalFormula.substitute 0 (numeral (gamma n)) = some φ ∧
          φ.freeVariables = [] ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A (.neg φ)) :=
  ⟨source_incomplete A hPA hc,interpreted_standard_incomplete A hPA hc,
    (fun _ U => interpreted_ultrapower_incomplete A hPA hc U),total_undecidable_family A hPA hc⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticInternalComparison
