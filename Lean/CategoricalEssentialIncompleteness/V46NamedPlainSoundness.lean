/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainLogicalValidity
public import CategoricalEssentialIncompleteness.V46NamedPlainSentenceTruth
public import CategoricalEssentialIncompleteness.V46FirstOrderModelSoundness

/-! # Soundness of the constructed standard sentence derivations -/

@[expose] public section

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
local notation "Q" => (Valid σ π d functions relations)

def sentenceValiditySet : Set (Obj 𝗣𝗔 ℕ (S).sentenceObject) :=
  FirstOrderModelSoundness.sentenceSubset 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) ℕ Q

theorem sentenceValiditySet_eq :
    sentenceValiditySet σ π d functions relations = validSentenceSet σ π d functions relations := rfl

def sentenceValidityInclusion : (sentenceValiditySet σ π d functions relations : Type) ⟶
    Obj 𝗣𝗔 ℕ (S).sentenceObject :=
  FirstOrderModelSoundness.validityInclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) ℕ Q

instance sentenceValidityInclusion_mono : Mono (sentenceValidityInclusion σ π d functions relations) := by
  dsimp only [sentenceValidityInclusion]
  exact FirstOrderModelSoundness.validityInclusion_mono 𝗣𝗔
    (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) ℕ Q

variable {A : PredicateCategory 𝗣𝗔} (axioms : Hom 𝗣𝗔 A
  (CategoricalSyntax.sentenceObject
    (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)))
variable (haxioms : FirstOrderModelSoundness.AxiomsProperty 𝗣𝗔
  (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d)
  (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
  (A := A) axioms ℕ (Valid σ π d functions relations))

include haxioms in
/-- Rule induction uses the constructed derivation carrier and the seven
proved actual scheme validities. No soundness factor is assumed. -/
theorem valid_conclusion :
    FirstOrderModelSoundness.ConclusionProperty 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q :=
  FirstOrderModelSoundness.conclusion_property 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms Q
    (valid_logicalAxioms σ π d functions relations) haxioms
    (valid_generalization σ π d functions relations)
    (valid_modusPonens σ π d functions relations)

include haxioms in
theorem valid_sentenceConclusion :
    FirstOrderModelSoundness.SentenceProperty 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q :=
  FirstOrderModelSoundness.sentenceProperty_of_conclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q
    (valid_conclusion σ π d functions relations (A := A) axioms haxioms)

/-- Corestriction of the actual sentence conclusion map to decoded validity. -/
def soundnessFactor :
    Obj 𝗣𝗔 ℕ (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) ⟶
      (sentenceValiditySet σ π d functions relations : Type) :=
  FirstOrderModelSoundness.factor 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q
    (valid_sentenceConclusion σ π d functions relations (A := A) axioms haxioms)

theorem soundnessFactor_inclusion :
    soundnessFactor σ π d functions relations (A := A) axioms haxioms ≫
      sentenceValidityInclusion σ π d functions relations =
        (G).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) :=
  FirstOrderModelSoundness.factor_inclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q
    (valid_sentenceConclusion σ π d functions relations (A := A) axioms haxioms)

include haxioms in
/-- The unique validity factorization of the actual generated sentence
conclusions. The generic algebra/object comparison with the original
SyntacticGeneratedTheory definitions is literal equality. -/
theorem exists_unique_soundnessFactor :
    ∃! e : Obj 𝗣𝗔 ℕ (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) ⟶
      (sentenceValiditySet σ π d functions relations : Type),
      e ≫ sentenceValidityInclusion σ π d functions relations =
        (G).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) :=
  FirstOrderModelSoundness.exists_unique_factor 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q
    (valid_sentenceConclusion σ π d functions relations (A := A) axioms haxioms)

include functions relations haxioms in
/-- Consistency is derived for the actual conclusion image and sentence
negation. The semantic structure K is distinct from the code model N. -/
theorem sentenceConclusion_range_consistent [Nonempty K] :
    Disjoint (Set.range ((G).map
      (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)))
      ((FirstOrderModelSoundness.negationPoint 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) ℕ) ⁻¹'
        Set.range ((G).map
          (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms))) := by
  apply FirstOrderModelSoundness.conclusion_range_consistent 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms ℕ Q
    (valid_sentenceConclusion σ π d functions relations (A := A) axioms haxioms)
  exact sentence_validity_disjoint σ π d functions relations

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
