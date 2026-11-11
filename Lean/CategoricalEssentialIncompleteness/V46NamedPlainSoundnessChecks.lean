/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSoundness


/-! # Statement checks in `V46NamedPlainSoundnessChecks` -/

@[expose] public section
noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSoundnessChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
local notation "Q" => (Valid σ π d functions relations)
variable {A : PredicateCategory 𝗣𝗔} (axioms : Hom 𝗣𝗔 A
  (CategoricalSyntax.sentenceObject
    (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)))
variable (haxioms : FirstOrderModelSoundness.AxiomsProperty 𝗣𝗔
  (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d)
  (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
  (A := A) axioms ℕ (Valid σ π d functions relations))

example (p : Obj 𝗣𝗔 ℕ (FirstOrderModelSoundness.proofAlgebra 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms).a.left) :
    Valid σ π d functions relations
      ((G).map (FirstOrderModelSoundness.conclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) p) :=
  valid_conclusion σ π d functions relations (A := A) axioms haxioms p

example : ∃! e : Obj 𝗣𝗔 ℕ (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) ⟶
      (sentenceValiditySet σ π d functions relations : Type),
      e ≫ sentenceValidityInclusion σ π d functions relations =
        (G).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) :=
  exists_unique_soundnessFactor σ π d functions relations (A := A) axioms haxioms

example [Nonempty K] :
    Disjoint (Set.range ((G).map
      (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)))
      ((FirstOrderModelSoundness.negationPoint 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) ℕ) ⁻¹'
        Set.range ((G).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms))) :=
  sentenceConclusion_range_consistent σ π d functions relations (A := A) axioms haxioms

example : FirstOrderModelSoundness.proofAlgebra 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms =
    SyntacticGeneratedTheory.proofAlgebra 𝗣𝗔 variableCarrier σ π d (A := A) axioms :=
  FirstOrderModelSoundness.proofAlgebra_plain 𝗣𝗔 variableCarrier σ π d (A := A) axioms

end CategoricalEssentialIncompleteness.V46.NamedPlainSoundnessChecks
