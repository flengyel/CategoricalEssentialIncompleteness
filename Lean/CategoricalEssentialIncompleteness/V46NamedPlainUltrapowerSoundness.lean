/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSoundness
public import CategoricalEssentialIncompleteness.V46UltrapowerComparison

/-! # The constructed soundness factor in the actual arithmetic ultrapower -/

@[expose] public section

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding SyntacticGeneratedTheory

/-- The actual predicate presentation and chosen total-domain
interpretation agree naturally, including the program graphs. -/
def canonicalCodeComparison :
    F 𝗣𝗔 ℕ ≅ realization 𝗣𝗔 ⋙ PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ :=
  (PredicateInterpretation.predicateComparison 𝗣𝗔 ℕ).symm ≪≫
    Functor.isoWhiskerLeft (realization 𝗣𝗔) (PredicateInterpretation.totalCanonicalComparison 𝗣𝗔 ℕ)

variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ
local notation "E" => realization 𝗣𝗔
local notation "H" => PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ
local notation "η" => canonicalCodeComparison
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

def canonicalValidityInclusion : (sentenceValiditySet σ π d functions relations : Type) ⟶
    (H).obj ((E).obj (S).sentenceObject) :=
  sentenceValidityInclusion σ π d functions relations ≫ (η).hom.app (S).sentenceObject

instance canonicalValidityInclusion_mono :
    Mono (canonicalValidityInclusion σ π d functions relations) := by
  dsimp [canonicalValidityInclusion]
  infer_instance

variable {A : PredicateCategory 𝗣𝗔} (axioms : Hom 𝗣𝗔 A
  (CategoricalSyntax.sentenceObject
    (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)))
variable (haxioms : FirstOrderModelSoundness.AxiomsProperty 𝗣𝗔
  (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d)
  (plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
  (A := A) axioms ℕ (Valid σ π d functions relations))

def canonicalSoundnessFactor :
    (H).obj ((E).obj (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)) ⟶
      (sentenceValiditySet σ π d functions relations : Type) :=
  (η).inv.app (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms) ≫
    soundnessFactor σ π d functions relations (A := A) axioms haxioms

theorem canonicalSoundnessFactor_inclusion :
    canonicalSoundnessFactor σ π d functions relations (A := A) axioms haxioms ≫
      canonicalValidityInclusion σ π d functions relations =
        (H).map ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)) := by
  let P := FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms
  let c := FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms
  let e := soundnessFactor σ π d functions relations (A := A) axioms haxioms
  let v := sentenceValidityInclusion σ π d functions relations
  change ((η).inv.app P ≫ e) ≫ (v ≫ (η).hom.app (S).sentenceObject) = (H).map ((E).map c)
  calc
    _ = (η).inv.app P ≫ ((e ≫ v) ≫ (η).hom.app (S).sentenceObject) := by
      simp only [Category.assoc]
    _ = (η).inv.app P ≫ ((G).map c ≫ (η).hom.app (S).sentenceObject) := by
      rw [soundnessFactor_inclusion]
    _ = (η).inv.app P ≫ ((η).hom.app P ≫ (H).map ((E).map c)) := by
      rw [(η).hom.naturality c]
      rfl
    _ = _ := by
      have hi := congrArg (fun f => f ≫ (H).map ((E).map c)) ((η).inv_hom_id_app P)
      simpa only [Category.assoc,Category.id_comp] using hi

theorem canonicalValidity_disjoint [Nonempty K] :
    Disjoint (Set.range (canonicalValidityInclusion σ π d functions relations))
      (((H).map ((E).map (S).sentenceNegation)) ⁻¹'
        Set.range (canonicalValidityInclusion σ π d functions relations)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a,rfl⟩ ⟨b,hb⟩
  have hn := congrArg (fun f => f (sentenceValidityInclusion σ π d functions relations a))
    ((η).hom.naturality (S).sentenceNegation)
  have he := ((η).app (S).sentenceObject).toEquiv.injective (hb.trans hn.symm)
  have hb' : sentenceValidityInclusion σ π d functions relations b ∈
      validSentenceSet σ π d functions relations := b.property
  have hneg := (congrArg (fun s : Obj 𝗣𝗔 ℕ (S).sentenceObject =>
    s ∈ validSentenceSet σ π d functions relations) he).mp hb'
  exact Set.disjoint_left.mp (sentence_validity_disjoint σ π d functions relations)
    a.property hneg

/-- The standard factor is constructed above, and the arithmetic
comparison is the existing proved canonical comparison. No soundness
factor or comparison is supplied as a new hypothesis. -/
theorem canonical_ultrapower_soundness [Nonempty K] {I : Type} (U : Ultrafilter I) :
    Mono (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
      (canonicalValidityInclusion σ π d functions relations)) ∧
    Ultrapower.transportSoundness U (ArithmeticUltrapower.canonicalComparison U)
        (canonicalSoundnessFactor σ π d functions relations (A := A) axioms haxioms) ≫
      Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
        (canonicalValidityInclusion σ π d functions relations) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map
        ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)) ∧
    Disjoint (Set.range (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
      (canonicalValidityInclusion σ π d functions relations)))
      (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map
          ((E).map (S).sentenceNegation)) ⁻¹'
        Set.range (Ultrapower.transportValidity U (ArithmeticUltrapower.canonicalComparison U)
          (canonicalValidityInclusion σ π d functions relations))) :=
  ArithmeticUltrapower.canonical_soundness_transport U
    ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)) ((E).map (S).sentenceNegation)
    (canonicalValidityInclusion σ π d functions relations)
    (canonicalSoundnessFactor σ π d functions relations (A := A) axioms haxioms)
    (canonicalSoundnessFactor_inclusion σ π d functions relations (A := A) axioms haxioms)
    (canonicalValidity_disjoint σ π d functions relations)

include functions relations haxioms in
/-- Consistency of the actual realized conclusion image in the arithmetic
ultrapower, obtained from the proved standard soundness factor. -/
theorem canonical_ultrapower_conclusion_consistent [Nonempty K]
    {I : Type} (U : Ultrafilter I) :
    Disjoint
      (Set.range ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
        (ArithmeticUltrapower.Model U)).map
          ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms))))
      (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
          (ArithmeticUltrapower.Model U)).map ((E).map (S).sentenceNegation)) ⁻¹'
        Set.range ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔
          (ArithmeticUltrapower.Model U)).map
            ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms)))) :=
  Ultrapower.conclusion_range_consistent U (ArithmeticUltrapower.canonicalComparison U)
    ((E).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S) (A := A) axioms))
    ((E).map (S).sentenceNegation)
    (canonicalValidityInclusion σ π d functions relations)
    (canonicalSoundnessFactor σ π d functions relations (A := A) axioms haxioms)
    (canonicalSoundnessFactor_inclusion σ π d functions relations (A := A) axioms haxioms)
    (canonicalValidity_disjoint σ π d functions relations)

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
