/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumeration
public import CategoricalEssentialIncompleteness.SyntacticObservations
public import FailureOfComposition.ConcreteAdequacy
public import FailureOfComposition.ComputationSearchIndices
public import Mathlib.Computability.Halting

/-! # Equal standard axiom sets with inequivalent numeral presentations

Section 8.2 uses a separate numerical index for each axiom predicate. A common
standard extension does not determine the predicate up to PA-provable equivalence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Encodable Denumerable
open Nat.Partrec (Code)
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.IndexedAxiomPresentations
open ArithmeticIndexedAxioms ArithmeticIndexedPAEnumeration ArithmeticNamedAxiomComparison
open NamedArithmeticSignature

abbrev axiomPredicate (e : ℕ) := fiberAxioms axiomCodes e

def standardAxioms (e : ℕ) : Set ℕ := {w | (axiomPredicate e).val.Evalb (M := ℕ) ![w]}

def equivalenceSentence (e d : ℕ) : ArithmeticSentence :=
  let P := axiomPredicate e
  let Q := axiomPredicate d
  “∀ z, !P.val z ↔ !Q.val z”

private def equivalenceFormula (d : ℕ) : ArithmeticSemisentence 1 :=
  let A := axiomGraph axiomCodes
  let D := axiomPredicate d
  “e. ∀ z, !A.val e z ↔ !D.val z”

private theorem equivalence_models {M : Type} [ORingStructure M] (e d : ℕ) :
    M↓[ℒₒᵣ] ⊧ equivalenceSentence e d ↔ ∀ w : M,
      (axiomPredicate e).val.Evalb ![w] ↔ (axiomPredicate d).val.Evalb ![w] := by
  simp [models_iff, equivalenceSentence]

private theorem equivalence_numeral {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e d : ℕ) :
    (M↓[ℒₒᵣ] ⊧ ((equivalenceFormula d)/[(↑e : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) ↔
      M↓[ℒₒᵣ] ⊧ equivalenceSentence e d := by
  rw [ClassicalPrograms.numeralInstance_eval, equivalence_models]
  simp [equivalenceFormula, axiomPredicate, fiberAxioms]

theorem provable_equivalence_enumerable (d : ℕ) :
    REPred (fun e : ℕ => 𝗣𝗔 ⊢ equivalenceSentence e d) := by
  apply (SyntacticModel.numeral_provability_enumerable 𝗣𝗔 (equivalenceFormula d)).of_eq
  intro e
  constructor
  · intro h
    apply complete.{0} 𝗣𝗔
    intro M _ _
    exact (equivalence_numeral e d).mp (consequence_iff.mp (Theory.Proof.sound h) M inferInstance)
  · intro h
    apply complete.{0} 𝗣𝗔
    intro M _ _
    exact (equivalence_numeral e d).mpr (consequence_iff.mp (Theory.Proof.sound h) M inferInstance)

private theorem sound_equivalence {e d : ℕ} (hp : 𝗣𝗔 ⊢ equivalenceSentence e d) :
    standardAxioms e = standardAxioms d := by
  apply Set.ext
  exact (equivalence_models (M := ℕ) e d).mp
    (consequence_iff.mp (Theory.Proof.sound hp) ℕ inferInstance)

private theorem standard_fiber (e w : ℕ) :
    w ∈ standardAxioms e ↔ sentencePredicate.val.Evalb ![w] ∧
      (axiomCodes.val.Evalb ![w] ∨ (Kleene.eval e w).Dom) := by
  refine (fiberAxioms_eval ℕ axiomCodes e w).trans (and_congr_right fun _ =>
    or_congr_right ?_)
  rw [Part.dom_iff_mem]
  apply exists_congr
  intro y
  have he := canonicalPartrecGraphFormula_eval_iff_eventualGraph (M := ℕ) e w y
  simp only [numeral_eq_natCast_app] at he
  exact he.trans (eventualGraph_adequate e w y)

/-- The sentence ¬(0=0) is outside the chosen PA axioms. -/
private def falseSentence : Formula := .neg (.equal zero zero)

private theorem falseSentence_closed : falseSentence.freeVariables = [] := by
  simp [falseSentence, NamedFiniteSyntax.Formula.freeVariables]

private theorem falseSentence_not_axiom : ¬ axiomCodes.val.Evalb (M := ℕ) ![formulaCode falseSentence] := by
  intro h
  obtain ⟨ψ, hψ, hw⟩ := (axiomCodes_standard _).mp h
  have he : ψ = falseSentence := NamedPostfixEncoding.formulaCode_injective hw
  subst ψ
  obtain ⟨_, φ, hseed, hclosure⟩ := hψ
  cases hclosure
  case refl => cases hseed

/-- The program runs c at 0 for every axiom-word input. -/
private def waitIndex (c : Code) : ℕ := encode (Code.comp c Code.zero)

private theorem waitIndex_computable : Computable waitIndex :=
  (Primrec.encode.comp (Code.primrec₂_comp.comp Primrec.id (Primrec.const Code.zero))).to_comp

private theorem waitIndex_eval (c : Code) (w : ℕ) : Kleene.eval (waitIndex c) w = c.eval 0 := by
  simp only [waitIndex, Kleene.eval, ofNat_encode, Code.eval]
  exact Part.bind_some 0 c.eval

theorem emptyIndex_axioms (w : ℕ) :
    w ∈ standardAxioms Kleene.emptyIndex ↔ axiomCodes.val.Evalb ![w] := by
  rw [standard_fiber, Kleene.emptyIndex_spec]
  exact ⟨fun h => h.2.resolve_right Part.not_none_dom,
    fun h => ⟨((axiomCodes_eval w).mp h).1, Or.inl h⟩⟩

private theorem equal_standard_iff (c : Code) :
    standardAxioms (waitIndex c) = standardAxioms Kleene.emptyIndex ↔ ¬ (c.eval 0).Dom := by
  constructor
  · intro he hc
    let w := formulaCode falseSentence
    have hw : w ∈ standardAxioms (waitIndex c) := (standard_fiber _ _).mpr
      ⟨(sentence_formulaCode _).mpr falseSentence_closed, Or.inr (by rwa [waitIndex_eval])⟩
    have hb := ((standard_fiber Kleene.emptyIndex w).mp (he ▸ hw)).2
    exact hb.elim falseSentence_not_axiom (by simp [Kleene.emptyIndex_spec])
  · intro hc
    ext w
    simp only [standard_fiber, waitIndex_eval, Kleene.emptyIndex_spec, hc, Part.not_none_dom, or_false]

/-- The fixed base fiber and a second numeral index have the same sentence axioms in
ℕ. PA has no proof of the equivalence of their displayed axiom predicates. -/
theorem equal_standard_axioms_unprovable :
    ∃ e : ℕ, e ≠ Kleene.emptyIndex ∧ standardAxioms e = standardAxioms Kleene.emptyIndex ∧
      ¬ 𝗣𝗔 ⊢ equivalenceSentence e Kleene.emptyIndex := by
  classical
  have hex : ∃ c : Code, ¬ (c.eval 0).Dom ∧ ¬ 𝗣𝗔 ⊢ equivalenceSentence (waitIndex c) Kleene.emptyIndex := by
    by_contra! hall
    apply ComputablePred.halting_problem_not_re 0
    apply ((provable_equivalence_enumerable Kleene.emptyIndex).comp waitIndex_computable).of_eq
    intro c
    exact ⟨fun hp => (equal_standard_iff c).mp (sound_equivalence hp), hall c⟩
  obtain ⟨c, hc, hp⟩ := hex
  refine ⟨waitIndex c, ?_, (equal_standard_iff c).mpr hc, hp⟩
  intro he
  apply hp
  rw [he]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  exact (equivalence_models _ _).mpr fun _ => Iff.rfl

end CategoricalEssentialIncompleteness.V46.IndexedAxiomPresentations
