/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationSemantics

/-! # The actual named Gamma enumeration and a consistent source theory

Only individual PA axioms need be supplied by the concrete arithmetic
comparison. Every other source axiom is the proved presentation of an
actual literal enumerated named sentence.
-/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.NamedGammaModel
open NamedArithmeticSignature
open SyntacticPredicates

/-- PA together with source presentations of precisely the given closed
Gamma words. The enumeration A is retained, with its original binder names. -/
def sourceTheory (A : Carrier) : ArithmeticTheory :=
  𝗣𝗔 ∪ {p | ∃ (φ : Formula) (hφ : φ.freeVariables = []),
    A.val.Evalb ![formulaCode φ] ∧ p = ArithmeticNamedPresentation.sentence φ hφ}

variable (A : Carrier)
local notation "S" => ArithmeticNamedProofConnectives.system A
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A

private theorem toNative {φ : Formula} (h : S ⊢ φ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff
    functionSymbols relationSymbols bound (ArithmeticNamedProofConnectives.system A) φ).mp h

private theorem fromNative {φ : Formula} (h : D φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff
    functionSymbols relationSymbols bound (ArithmeticNamedProofConnectives.system A) φ).mpr h

/-- Ordinary native consistency is exactly the absence of a derivation
of the closed arithmetic falsity, independently of the open formula used
as the propositional system's neutral falsehood. -/
theorem consistent_iff_no_falsity :
    Entailment.Consistent S ↔ ¬ D ArithmeticNamedTranslation.falsity := by
  constructor
  · intro hc hn
    apply hc.not_inconsistent
    intro ψ
    apply fromNative A
    apply NamedHilbertPropositional.local_empty functionSymbols relationSymbols bound A ψ
    exact NamedHilbertPropositional.local_explosion functionSymbols relationSymbols bound A
      ∅ ArithmeticNamedTranslation.truth ψ (.base (.reflexivity zero)) (.base hn)
  · intro hn
    exact Consistent.of_unprovable (fun h => hn (toNative A h))

/-- Actual enumerated sentences are admissible source axioms because the
roundtrip is a native proof, not an assumed equality of word presentations. -/
theorem source_axioms_admissible
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible A (sourceTheory A) := by
  intro p hp
  rcases hp with hp | ⟨φ,hφ,ha,rfl⟩
  · exact hPA p hp
  · have ha' : S ⊢ φ := fromNative A (.axiom φ ha hφ)
    have he := ArithmeticNamedPresentation.sentence_zero_roundtrip A φ hφ
    exact toNative A ((K_right he) ⨀ ha')

/-- Consistency transfers by the actual finite LK2-to-native derivation
induction. It does not follow from standard-model truth of Gamma. -/
theorem source_consistent
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (hc : Entailment.Consistent S) : Entailment.Consistent (sourceTheory A) := by
  apply consistent_iff_unprovable_bot.mpr
  intro hb
  have hn : D ArithmeticNamedTranslation.falsity :=
    ArithmeticNamedProofTranslation.sentence A (sourceTheory A)
      (source_axioms_admissible A hPA) ⊥ hb
  exact (consistent_iff_no_falsity A).mp hc hn

theorem PA_subset_source : 𝗣𝗔 ⊆ sourceTheory A := Set.subset_union_left

/-- Genuine first-order completeness supplies a semantic arithmetic
structure. The imported arithmetic completeness theorem performs the
proved equality-model comparison before using the canonical arithmetic
interpretation. -/
theorem exists_source_model (hc : Entailment.Consistent (sourceTheory A)) :
    ∃ (K : Type) (s : ORingStructure K), letI := s; K↓[ℒₒᵣ] ⊧* sourceTheory A := by
  classical
  have : 𝗣𝗔 ⪯ sourceTheory A := Axiomatized.le_of_subset (PA_subset_source A)
  have : 𝗘𝗤 ℒₒᵣ ⪯ sourceTheory A :=
    WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔) inferInstance
  by_contra h
  have hb : sourceTheory A ⊢ ⊥ := Arithmetic.complete (sourceTheory A) ⊥ (by
    intro K s hK
    exact False.elim (h ⟨K,s,hK⟩))
  exact consistent_iff_unprovable_bot.mp hc hb

/-- Every canonical arithmetic model of the source theory satisfies the
literal named Gamma sentences in the semantic structure K. -/
theorem source_model_models {K : Type} [ORingStructure K]
    [hK : K↓[ℒₒᵣ] ⊧* sourceTheory A] (ρ : ℕ → K) :
    NamedGammaSoundness.Models functionSymbols relationSymbols bound A
      ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ := by
  intro φ ha hφ
  have hp : ArithmeticNamedPresentation.sentence φ hφ ∈ sourceTheory A :=
    Or.inr ⟨φ,hφ,ha,rfl⟩
  have hv := Semantics.modelsSet_iff.mp hK hp
  exact (ArithmeticNamedPresentation.sentence_semantics φ hφ ρ).mp hv

end CategoricalEssentialIncompleteness.V46.NamedGammaModel
