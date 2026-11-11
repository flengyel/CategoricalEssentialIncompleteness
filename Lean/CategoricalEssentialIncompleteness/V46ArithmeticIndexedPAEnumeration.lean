/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationInduction
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxioms
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance

/-! # A chosen actual Σ₁ PA-axiom enumeration and every indexed PA extension

The chosen axioms are the closed native arithmetic/order and induction
matrices under finite universal closure. Their equivalence with the
canonical-closure generating condition is already proved by
extendsPA_iff_canonical. This construction does not enumerate all PA theorems.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

def axiomCodes : Carrier :=
  let Sent := ArithmeticIndexedAxioms.sentencePredicate
  .mkSigma “out. !Sent.val out ∧ ∃ seed, !seedCarrier.val seed ∧ !closureRelation.val out seed”

section Models
variable {M : Type} [ORingStructure M]

@[simp] theorem axiomCodes_eval (out : M) :
    axiomCodes.val.Evalb ![out] ↔
      ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![out] ∧
        ∃ seed : M, seedCarrier.val.Evalb ![seed] ∧ closureRelation.val.Evalb ![out,seed] := by
  simp [axiomCodes]

end Models

theorem sentence_formulaCode (ψ : Formula) :
    ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![formulaCode ψ] ↔ ψ.freeVariables = [] := by
  refine (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound ℕ (formulaCode ψ)).trans ?_
  have hf := (SyntacticSyntax.Postfix.carrier_plain_model true termPolynomial formulaPolynomial
    (formulaCode ψ)).mp (NamedPostfixEncoding.formulaCode_member ψ)
  constructor
  · intro h
    exact (NamedPostfixEncoding.sentence_formulaCode_iff ψ).mp h.2
  · intro h
    exact ⟨hf,(NamedPostfixEncoding.sentence_formulaCode_iff ψ).mpr h⟩

/-- The standard extension is exactly the literal native PA-axiom codes,
including all binder names and the actual substitution convention. -/
theorem axiomCodes_standard (out : ℕ) :
    axiomCodes.val.Evalb ![out] ↔ ∃ ψ : Formula, PAAxiom ψ ∧ formulaCode ψ = out := by
  rw [axiomCodes_eval]
  constructor
  · rintro ⟨hs,seed,hseed,hclosure⟩
    have hparts := (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound ℕ out).mp hs
    have hstored := (SyntacticSyntax.Postfix.carrier_plain_model true termPolynomial formulaPolynomial out).mpr hparts.1
    obtain ⟨ψ,hψ⟩ := (NamedPostfixEncoding.standard_codes_surjective
      functionSymbols relationSymbols bound).2 out hstored
    change formulaCode ψ = out at hψ
    obtain ⟨φ,hφ,hcodeφ⟩ := (seedCarrier_standard seed).mp hseed
    have hsψ : ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![formulaCode ψ] :=
      (congrArg (fun z : ℕ => ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![z]) hψ).mpr hs
    have hclosed : ψ.freeVariables = [] := (sentence_formulaCode ψ).mp hsψ
    have huc : UniversalClosure φ ψ := (closureRelation_codes φ ψ).mp (by
      simpa only [hψ,hcodeφ] using hclosure)
    exact ⟨ψ,⟨hclosed,φ,hφ,huc⟩,hψ⟩
  · rintro ⟨ψ,⟨hclosed,φ,hφ,huc⟩,rfl⟩
    exact ⟨(sentence_formulaCode ψ).mpr hclosed,formulaCode φ,
      (seedCarrier_standard _).mpr ⟨φ,hφ,rfl⟩,(closureRelation_codes φ ψ).mpr huc⟩

theorem canonicalClosure_mem (φ : Formula) (hφ : PASeed φ) :
    axiomCodes.val.Evalb ![formulaCode (canonicalClosure φ)] :=
  (axiomCodes_standard _).mpr ⟨canonicalClosure φ,
    ⟨canonicalClosure_sentence φ,φ,hφ,closure_isUniversal _ _⟩,rfl⟩

/-- Every numeral fiber contains each actual native PA axiom as an axiom.
Neither enumeration correctness nor source admissibility is an input field. -/
theorem fiber_extendsPA (e : ℕ) :
    ExtendsPA (ArithmeticIndexedAxioms.fiberAxioms axiomCodes e) := by
  intro ψ hψ
  apply SyntacticNamedHilbert.Derives.axiom ψ _ hψ.1
  apply (ArithmeticIndexedAxioms.fiberAxioms_eval ℕ axiomCodes e (formulaCode ψ)).mpr
  exact ⟨(sentence_formulaCode ψ).mpr hψ.1,
    Or.inl ((axiomCodes_standard _).mpr ⟨ψ,hψ,rfl⟩)⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
