/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparability
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumeration

/-! # Proofs of the signed numeral instances in §8.6

The word of a closed formula belongs to the sentence theorem set precisely
when the finite rules derive its formula point. In particular this applies
to the numeral instance of the diagonal even-output formula and its negation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.NamedTheoryObservations
open NamedArithmeticSignature
attribute [local irreducible] ArithmeticDiagonalCodes.diagonalIndex

/-- The closed named instance of the even-output formula at the numeral for n. -/
abbrev numeralInstance (n : ℕ) : Formula :=
  NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val n

theorem numeralInstance_closed (n : ℕ) : (numeralInstance n).freeVariables = [] :=
  (NamedArithmeticDiagonalBounds.standard_instance_result _ n).2

abbrev positiveWord := ArithmeticSentenceInseparability.theta

def negativeWord (n : ℕ) : ℕ := NamedArithmeticProofSearch.negationWord ℕ (positiveWord n)

theorem positiveWord_eq (n : ℕ) : positiveWord n = formulaCode (numeralInstance n) :=
  (NamedArithmeticDiagonalBounds.standard_instance_result _ n).1

theorem negativeWord_eq (n : ℕ) : negativeWord n = formulaCode (.neg (numeralInstance n)) := by
  rw [negativeWord, positiveWord_eq, NamedArithmeticProofSearch.negationWord_formulaCode]

theorem negativeWord_computable : Computable negativeWord :=
  NamedArithmeticProofSearch.negationWord_primrec.to_comp.comp
    ArithmeticSentenceInseparability.theta_computable

/-- An external finite tree of the named arithmetic rules with conclusion φ. -/
abbrev FiniteDerivation (Γ : Carrier) (φ : Formula) :=
  SyntacticFiniteNamedDerivations.Derives 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound Γ ℕ
    (SyntacticNamedHilbert.formulaPoint functionSymbols relationSymbols bound φ)

/-- A standard point of the initial proof algebra with the indicated conclusion word. -/
def HasProofPoint (Γ : Carrier) (word : ℕ) : Prop :=
  ∃ p : Obj 𝗣𝗔 ℕ (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ).a.left,
    ((F 𝗣𝗔 ℕ).map (SyntacticGeneratedAxioms.conclusion 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ) p).val = word

theorem finiteDerivation_iff_proofPoint (Γ : Carrier) (φ : Formula) :
    FiniteDerivation Γ φ ↔ HasProofPoint Γ (formulaCode φ) := by
  let rules := (SyntacticSyntax.plainCategoricalSyntax 𝗣𝗔 variableSymbols
    functionSymbols relationSymbols bound).logicalRules (SyntacticAxiomPredicates.axioms
      𝗣𝗔 variableSymbols functionSymbols relationSymbols bound Γ)
  let point := SyntacticNamedHilbert.formulaPoint functionSymbols relationSymbols bound φ
  have hval : point.val = formulaCode φ :=
    SyntacticNamedHilbert.formulaPoint_value _ _ _ φ
  refine (SyntacticFiniteDerivations.standard_iff 𝗣𝗔 rules point).trans ?_
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (congrArg Subtype.val hp).trans hval⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext (hp.trans hval.symm)⟩

private theorem carrier_membership (C : Carrier) (w : ℕ) :
    w ∈ {z : ℕ | C.val.Evalb (M := ℕ) ![z]} ↔ C.val.Evalb (M := ℕ) ![w] := Iff.rfl

theorem theoremSet_iff_eval (Γ : Carrier) (w : ℕ) :
    w ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound Γ).val.Evalb (M := ℕ) ![w] :=
  carrier_membership (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound Γ) w

theorem mem_theoremSet (Γ : Carrier) (w : ℕ) :
    w ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔
      ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![w] ∧ HasProofPoint Γ w := by
  unfold ArithmeticSentenceInseparability.theoremSet ArithmeticIndexedAxioms.sentencePredicate
    NamedArithmeticLiteralTotal.literalPredicate
  refine (carrier_membership (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound Γ) w).trans ?_
  exact (SyntacticGeneratedAxioms.literalTheoremCarrier_model 𝗣𝗔 variableSymbols
    functionSymbols relationSymbols bound ℕ Γ w).trans
    (SyntacticGeneratedAxioms.theoremCarrier_model 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound ℕ Γ w)

theorem theoremSet_iff_proofPoint_of_sentence (Γ : Carrier) (w : ℕ)
    (hw : ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![w]) :
    w ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔ HasProofPoint Γ w :=
  (mem_theoremSet Γ w).trans (@and_iff_right _ (HasProofPoint Γ w) hw)

theorem theoremSet_iff_proofPoint (Γ : Carrier) (φ : Formula) (hφ : φ.freeVariables = []) :
    formulaCode φ ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔
      HasProofPoint Γ (formulaCode φ) :=
  theoremSet_iff_proofPoint_of_sentence Γ (formulaCode φ) ((ArithmeticIndexedPAEnumeration.sentence_formulaCode φ).mpr hφ)

theorem theoremSet_iff_finiteDerivation (Γ : Carrier) (φ : Formula) (hφ : φ.freeVariables = []) :
    formulaCode φ ∈ ArithmeticSentenceInseparability.theoremSet Γ ↔ FiniteDerivation Γ φ :=
  (theoremSet_iff_proofPoint Γ φ hφ).trans (finiteDerivation_iff_proofPoint Γ φ).symm

/-- A c.e. set of words gives a Σ₁ axiom predicate in the fixed language of arithmetic. -/
def axiomPredicate (A : Set ℕ) : Carrier :=
  .mkSigma (codeOfREPred (· ∈ A)) (by simp [codeOfREPred, codeOfPartrec'])

theorem axiomPredicate_eval (A : Set ℕ) (hA : REPred (· ∈ A)) (n : ℕ) :
    (axiomPredicate A).val.Evalb (M := ℕ) ![n] ↔ n ∈ A := codeOfREPred_spec hA

/-- A set of sentence words is consistent when it contains no sentence and its negation. -/
def SentenceConsistent (T : Set ℕ) : Prop :=
  ∀ φ : Formula, φ.freeVariables = [] → ¬ (formulaCode φ ∈ T ∧ formulaCode (.neg φ) ∈ T)

/-- Consistent c.e. extensions of PA are ordered by inclusion of their sentence theorem sets. -/
abbrev Theory := {T : Set ℕ // (∃ Γ : Carrier, ArithmeticNamedAxiomComparison.ExtendsPA Γ ∧
  T = ArithmeticSentenceInseparability.theoremSet Γ) ∧ SentenceConsistent T}

def ofPresentation (Γ : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) : Theory := by
  refine ⟨ArithmeticSentenceInseparability.theoremSet Γ, ⟨Γ, hPA, rfl⟩, ?_⟩
  intro φ hφ h
  apply NamedGammaEvidenceSoundness.standard_sentence_evidence_disjoint Γ hPA hc (formulaCode φ)
    ((ArithmeticIndexedPAEnumeration.sentence_formulaCode φ).mpr hφ)
  rw [NamedArithmeticProofSearch.negationWord_formulaCode]
  exact ⟨(theoremSet_iff_eval Γ (formulaCode φ)).mp h.1,
    (theoremSet_iff_eval Γ (formulaCode (.neg φ))).mp h.2⟩

theorem theoremSet_sentences (Γ : Carrier) {word : ℕ}
    (hw : word ∈ ArithmeticSentenceInseparability.theoremSet Γ) :
    ∃ φ : Formula, φ.freeVariables = [] ∧ formulaCode φ = word := by
  have hs := ((mem_theoremSet Γ word).mp hw).1
  have hh := ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔 variableSymbols
    functionSymbols relationSymbols bound ℕ word).mp hs).1
  have hcode := (SyntacticSyntax.Postfix.carrier_plain_model true termPolynomial
    formulaPolynomial word).mpr hh
  obtain ⟨φ, he⟩ := (NamedPostfixEncoding.standard_codes_surjective
    functionSymbols relationSymbols bound).2 word hcode
  change formulaCode φ = word at he
  refine ⟨φ, (ArithmeticIndexedPAEnumeration.sentence_formulaCode φ).mp ?_, he⟩
  exact (congrArg (fun z : ℕ => ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![z]) he).mpr hs

/-- Any deductively closed c.e. set of sentences containing the PA axioms can serve
as its own axiom presentation. -/
def ofEnumerableTheory (T : Set ℕ) (hT : REPred (· ∈ T))
    (hs : ∀ w ∈ T, ∃ φ : Formula, φ.freeVariables = [] ∧ formulaCode φ = w)
    (hPA : ∀ φ, ArithmeticNamedAxiomComparison.PAAxiom φ → formulaCode φ ∈ T)
    (hd : ∀ φ : Formula, φ.freeVariables = [] → FiniteDerivation (axiomPredicate T) φ → formulaCode φ ∈ T)
    (hc : SentenceConsistent T) : Theory := by
  refine ⟨T, ⟨axiomPredicate T, ?_, ?_⟩, hc⟩
  · intro φ hφ
    exact .axiom φ ((axiomPredicate_eval T hT _).mpr (hPA φ hφ)) hφ.1
  · ext w
    constructor
    · intro hw
      obtain ⟨φ, hφ, rfl⟩ := hs w hw
      apply (theoremSet_iff_eval (axiomPredicate T) (formulaCode φ)).mpr
      exact SyntacticNamedHilbert.native_sentence_theorem functionSymbols relationSymbols bound (axiomPredicate T)
        (.axiom φ ((axiomPredicate_eval T hT _).mpr hw) hφ) hφ
    · intro hw
      obtain ⟨φ, hφ, rfl⟩ := theoremSet_sentences (axiomPredicate T) hw
      exact hd φ hφ ((theoremSet_iff_finiteDerivation _ φ hφ).mp hw)

theorem theory_enumerable (T : Theory) : REPred (· ∈ T.val) := by
  obtain ⟨Γ, _, hΓ⟩ := T.property.1
  rw [hΓ]
  exact ArithmeticSentenceInseparability.theoremSet_enumerable Γ

def positive (T : Theory) : Set ℕ := positiveWord ⁻¹' T.val

def negative (T : Theory) : Set ℕ := negativeWord ⁻¹' T.val

theorem signed_derivability (T : Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) (n : ℕ) :
    (n ∈ positive T ↔ FiniteDerivation Γ (numeralInstance n)) ∧
      (n ∈ negative T ↔ FiniteDerivation Γ (.neg (numeralInstance n))) := by
  change (positiveWord n ∈ T.val ↔ _) ∧ (negativeWord n ∈ T.val ↔ _)
  rw [hΓ, positiveWord_eq, negativeWord_eq]
  exact ⟨theoremSet_iff_finiteDerivation Γ _ (numeralInstance_closed n),
    theoremSet_iff_finiteDerivation Γ _ (numeralInstance_closed n)⟩

theorem signed_proofPoints (T : Theory) (Γ : Carrier)
    (hΓ : T.val = ArithmeticSentenceInseparability.theoremSet Γ) (n : ℕ) :
    (n ∈ positive T ↔ HasProofPoint Γ (formulaCode (numeralInstance n))) ∧
      (n ∈ negative T ↔ HasProofPoint Γ (formulaCode (.neg (numeralInstance n)))) :=
  ⟨((signed_derivability T Γ hΓ n).1).trans (finiteDerivation_iff_proofPoint Γ _),
   ((signed_derivability T Γ hΓ n).2).trans (finiteDerivation_iff_proofPoint Γ _)⟩

end CategoricalEssentialIncompleteness.V46.NamedTheoryObservations
