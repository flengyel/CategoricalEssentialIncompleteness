/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonOperations
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageData

/-! # Chosen sentence pullbacks and arbitrary external Γ after the push -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation

section SentencePullbacks
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {V₀ : C} {V₁ : D} {σ₀ ρ₀ : ℕ → C} {σ₁ ρ₁ : ℕ → D} {d₀ d₁ : ℕ}
variable (S₀ : CategoricalSyntax V₀ σ₀ ρ₀ d₀) (S₁ : CategoricalSyntax V₁ σ₁ ρ₁ d₁)
variable (i : E.functor.obj S₀.algebra.a.2 ≅ S₁.algebra.a.2)
variable (j : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hFV : E.functor.map S₀.formulaOccurrences ≫ j.hom = i.hom ≫ S₁.formulaOccurrences)
variable (hNil : E.functor.map S₀.lists.algebra.nil ≫ j.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)

include hFV hNil in
theorem sentencePullback :
    IsPullback (E.functor.map S₀.sentenceInclusion ≫ i.hom)
      (E.functor.map (pullback.snd S₀.formulaOccurrences S₀.lists.algebra.nil) ≫
        (DecidableVariables.Transport.terminalIso E).hom)
      S₁.formulaOccurrences S₁.lists.algebra.nil := by
  apply (E.functor.map_isPullback
    (IsPullback.of_hasPullback S₀.formulaOccurrences S₀.lists.algebra.nil)).of_iso
    (Iso.refl (E.functor.obj S₀.sentenceObject)) i
    (DecidableVariables.Transport.terminalIso E) j
  · simp [CategoricalSyntax.sentenceInclusion, CategoricalSyntax.sentenceObject]
  · simp [CategoricalSyntax.sentenceObject]
  · exact hFV
  · exact hNil

theorem sentenceNegation_square
    (k : E.functor.obj S₀.sentenceObject ≅ S₁.sentenceObject)
    (hk : E.functor.map S₀.sentenceInclusion ≫ i.hom = k.hom ≫ S₁.sentenceInclusion)
    (hi : E.functor.map S₀.negationConstructor ≫ i.hom = i.hom ≫ S₁.negationConstructor) :
    E.functor.map S₀.sentenceNegation ≫ k.hom = k.hom ≫ S₁.sentenceNegation := by
  apply (cancel_mono S₁.sentenceInclusion).mp
  calc
    _ = E.functor.map S₀.sentenceNegation ≫
        (E.functor.map S₀.sentenceInclusion ≫ i.hom) := by rw [Category.assoc, hk]
    _ = E.functor.map (S₀.sentenceNegation ≫ S₀.sentenceInclusion) ≫ i.hom := by
      rw [E.functor.map_comp, Category.assoc]
    _ = E.functor.map (S₀.sentenceInclusion ≫ S₀.negationConstructor) ≫ i.hom := by
      rw [S₀.sentenceNegation_inclusion]
    _ = (E.functor.map S₀.sentenceInclusion ≫ i.hom) ≫ S₁.negationConstructor := by
      rw [E.functor.map_comp, Category.assoc, hi, Category.assoc]
    _ = _ := by simp only [hk, Category.assoc, S₁.sentenceNegation_inclusion]
end SentencePullbacks

private theorem equivalence_map_pullback
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (E : C ≌ D) {A B X Z : C}
    {s : A ⟶ B} {t : A ⟶ X} {f : B ⟶ Z} {g : X ⟶ Z}
    (h : IsPullback s t f g) :
    IsPullback (E.functor.map s) (E.functor.map t) (E.functor.map f) (E.functor.map g) :=
  E.functor.map_isPullback h


private theorem inverse_sentence_square
    {C : Type u₁} [Category.{v₁} C] {A B X Y : C}
    (i : A ≅ B) (j : X ≅ Y) (f : A ⟶ X) (g : B ⟶ Y)
    (h : f ≫ j.hom = i.hom ≫ g) : i.inv ≫ f = g ≫ j.inv := by
  apply (cancel_epi i.hom).mp
  calc
    _ = f := by simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    _ = (f ≫ j.hom) ≫ j.inv := by
      simp only [Category.assoc, j.hom_inv_id, Category.comp_id]
    _ = (i.hom ≫ g) ≫ j.inv := congrArg (fun k => k ≫ j.inv) h
    _ = _ := Category.assoc _ _ _

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d

theorem canonicalSentencePullback :
    IsPullback ((E).functor.map (S₁).sentenceInclusion ≫ (formulaIso a V σ π d).hom)
      ((E).functor.map (pullback.snd (S₁).formulaOccurrences (S₁).lists.algebra.nil) ≫
        (DecidableVariables.Transport.terminalIso (E)).hom)
      (S₂).formulaOccurrences (S₂).lists.algebra.nil :=
  sentencePullback (E) (S₁) (S₂) (formulaIso a V σ π d) (listIso a V σ π d)
    (formulaOccurrences_comparison a V σ π d) (nil_comparison a V σ π d)

def mappedSentenceIso : (E).functor.obj (S₁).sentenceObject ≅ (S₂).sentenceObject :=
  (canonicalSentencePullback a V σ π d).isoPullback

/-- The direction used to compare canonical generated subobjects. -/
def sentenceIso : (S₂).sentenceObject ≅ (E).functor.obj (S₁).sentenceObject :=
  (mappedSentenceIso a V σ π d).symm

theorem mappedSentenceIso_inclusion :
    (mappedSentenceIso a V σ π d).hom ≫ (S₂).sentenceInclusion =
      (E).functor.map (S₁).sentenceInclusion ≫ (formulaIso a V σ π d).hom :=
  (canonicalSentencePullback a V σ π d).isoPullback_hom_fst

theorem sentenceIso_inclusion :
    (sentenceIso a V σ π d).hom ≫ (E).functor.map (S₁).sentenceInclusion =
      (S₂).sentenceInclusion ≫ (formulaIso a V σ π d).inv := by
  exact inverse_sentence_square (mappedSentenceIso a V σ π d) (formulaIso a V σ π d)
    ((E).functor.map (S₁).sentenceInclusion) (S₂).sentenceInclusion
    (mappedSentenceIso_inclusion a V σ π d).symm

theorem sentenceNegation_comparison :
    (E).functor.map (S₁).sentenceNegation ≫ (mappedSentenceIso a V σ π d).hom =
      (mappedSentenceIso a V σ π d).hom ≫ (S₂).sentenceNegation :=
  sentenceNegation_square (E) (S₁) (S₂) (formulaIso a V σ π d)
    (mappedSentenceIso a V σ π d) (mappedSentenceIso_inclusion a V σ π d).symm
    (negation_comparison a V σ π d)

section Axioms
local notation "Vn" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "T₁" => NamedProofImage.syntaxData (P) σ π d
local notation "T₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (Vn) σ π d
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))

def canonicalAxiomObject : Total.CanonicalTotal a :=
  (E).functor.obj (NamedProofImage.axiomCarrier (P) σ π d Γ hΓ)

def canonicalAxioms : canonicalAxiomObject a σ π d Γ hΓ ⟶ (T₂).sentenceObject :=
  (E).functor.map (NamedProofImage.axioms (P) σ π d Γ hΓ) ≫
    (mappedSentenceIso a (Vn) σ π d).hom

instance canonicalAxioms_mono : Mono (canonicalAxioms a σ π d Γ hΓ) := by
  dsimp only [canonicalAxioms]
  infer_instance

/-- Literal formula words are reached only through the genuine formula
chart. The chosen sentence point itself is not a word coordinate. -/
def canonicalSentenceWord : (T₂).sentenceObject ⟶
    (E).functor.obj ((Syntax.predicateFunctor (P)).obj
      (NamedSyntaxComparison.sourceSyntax (Vn) σ π d).algebra.a.2) :=
  (sentenceIso a (Vn) σ π d).hom ≫ (E).functor.map (NamedProofImage.sentenceWord (P) σ π d)

theorem canonicalAxioms_word :
    canonicalAxioms a σ π d Γ hΓ ≫ canonicalSentenceWord a σ π d =
      (E).functor.map (NamedProofImage.axioms (P) σ π d Γ hΓ ≫
        NamedProofImage.sentenceWord (P) σ π d) := by
  simp only [canonicalAxioms, canonicalSentenceWord, sentenceIso,
    Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]

theorem canonicalAxiomPullback :
    IsPullback (canonicalAxioms a σ π d Γ hΓ)
      ((E).functor.map (SentenceAxiomPullbacks.wordProjection
        (NamedProofImage.sentenceWord (P) σ π d) Γ hΓ))
      (canonicalSentenceWord a σ π d)
      ((E).functor.map (AxiomSubobjects.axiomInclusion (P)
        (NamedSyntaxComparison.sourceSyntax (Vn) σ π d).algebra.a.2 Γ hΓ)) := by
  apply (equivalence_map_pullback (E) (SentenceAxiomPullbacks.axiomPullback
    (NamedProofImage.sentenceWord (P) σ π d) Γ hΓ)).of_iso
    (Iso.refl _) (mappedSentenceIso a (Vn) σ π d) (Iso.refl _) (Iso.refl _)
  · simp only [canonicalAxioms, NamedProofImage.axioms, Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [canonicalSentenceWord, sentenceIso, Iso.symm_hom, Iso.hom_inv_id_assoc,
      Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
end Axioms
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
