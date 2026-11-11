/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonConstructors

/-! # Actual sentence pullbacks under the named uniform syntax chart

Sentence objects are chosen pullbacks. Their formula coordinates are
compared through the proved occurrence diagram, without identifying
chosen pullback witnesses with literal formula words.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison

private theorem mapped_pullback_comparison
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasFiniteLimits C] [HasFiniteLimits D] (G : C ⥤ D) [PreservesFiniteLimits G]
    {A B X Z : C} {B' X' : D} (s : A ⟶ B) (t : A ⟶ X) (f : B ⟶ Z) (g : X ⟶ Z)
    (hs : IsPullback s t f g) (i : G.obj B ≅ B') (j : G.obj X ≅ X')
    (f' : B' ⟶ G.obj Z) (g' : X' ⟶ G.obj Z)
    (hf : G.map f = i.hom ≫ f') (hg : G.map g = j.hom ≫ g') :
    IsPullback (G.map s ≫ i.hom) (G.map t ≫ j.hom) f' g' := by
  apply (G.map_isPullback hs).of_iso (Iso.refl _) i j (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id] using hf
  · simpa only [Iso.refl_hom, Category.comp_id] using hg

private theorem inverse_comparison_leg {C : Type u₁} [Category.{v₁} C]
    {A B Z : C} (i : A ≅ B) (f : B ⟶ Z) (g : A ⟶ Z) (h : i.hom ≫ f = g) :
    f = i.inv ≫ g := by
  calc
    _ = (i.inv ≫ i.hom) ≫ f := by rw [i.inv_hom_id, Category.id_comp]
    _ = i.inv ≫ (i.hom ≫ f) := Category.assoc _ _ _
    _ = _ := congrArg (fun k => i.inv ≫ k) h

theorem inverse_comparison_square {C : Type u₁} [Category.{v₁} C]
    {A B X Y : C} (i : A ≅ B) (j : X ≅ Y) (f : A ⟶ X) (g : B ⟶ Y)
    (h : f ≫ j.hom = i.hom ≫ g) : i.inv ≫ f = g ≫ j.inv := by
  apply (cancel_epi i.hom).mp
  calc
    _ = f := by simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    _ = (f ≫ j.hom) ≫ j.inv := by
      simp only [Category.assoc, j.hom_inv_id, Category.comp_id]
    _ = (i.hom ≫ g) ≫ j.inv := congrArg (fun k => k ≫ j.inv) h
    _ = _ := Category.assoc _ _ _

private theorem restriction_natural {C : Type u₁} [Category.{v₁} C]
    {A B X Y : C} (s : B ⟶ A) (t : Y ⟶ X) (i : A ⟶ X) [Mono i] (j : B ⟶ Y)
    (a : A ⟶ A) (b : B ⟶ B) (x : X ⟶ X) (y : Y ⟶ Y)
    (hi : s ≫ i = j ≫ t) (ht : t ≫ x = y ≫ t)
    (ha : a ≫ i = i ≫ x) (hb : b ≫ j = j ≫ y) : s ≫ a = b ≫ s := by
  apply (cancel_mono i).mp
  calc
    _ = s ≫ (a ≫ i) := Category.assoc _ _ _
    _ = s ≫ (i ≫ x) := congrArg (fun k => s ≫ k) ha
    _ = (s ≫ i) ≫ x := (Category.assoc _ _ _).symm
    _ = (j ≫ t) ≫ x := congrArg (fun k => k ≫ x) hi
    _ = j ≫ (t ≫ x) := Category.assoc _ _ _
    _ = j ≫ (y ≫ t) := congrArg (fun k => j ≫ k) ht
    _ = (b ≫ j) ≫ t := by rw [hb, Category.assoc]
    _ = b ≫ (j ≫ t) := Category.assoc _ _ _
    _ = b ≫ (s ≫ i) := congrArg (fun k => b ≫ k) hi.symm
    _ = _ := (Category.assoc _ _ _).symm

variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d

private theorem sentence_occurrences_comparison :
    (F).map (S₀).formulaOccurrences =
      (formulaIso P V σ π d).inv ≫ (S₁).formulaOccurrences := by
  have h := formulaOccurrences_comparison P V σ π d
  change (formulaIso P V σ π d).hom ≫ (F).map (S₀).formulaOccurrences =
    (S₁).formulaOccurrences at h
  exact inverse_comparison_leg (formulaIso P V σ π d)
    ((F).map (S₀).formulaOccurrences) (S₁).formulaOccurrences h

private theorem sentence_nil_comparison :
    (F).map (S₀).lists.algebra.nil = terminalComparison (F) ≫ (S₁).lists.algebra.nil := by
  change (F).map (S₀).lists.algebra.nil =
    terminalComparison (F) ≫ (inv (terminalComparison (F)) ≫ (F).map (S₀).lists.algebra.nil)
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

theorem sentenceComparisonPullback :
    IsPullback
      ((F).map (S₀).sentenceInclusion ≫ (formulaIso P V σ π d).inv)
      ((F).map (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil) ≫ terminalComparison (F))
      (S₁).formulaOccurrences (S₁).lists.algebra.nil := by
  have hs : IsPullback (S₀).sentenceInclusion
      (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil)
      (S₀).formulaOccurrences (S₀).lists.algebra.nil :=
    IsPullback.of_hasPullback (S₀).formulaOccurrences (S₀).lists.algebra.nil
  exact mapped_pullback_comparison (F) (S₀).sentenceInclusion
    (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil)
    (S₀).formulaOccurrences (S₀).lists.algebra.nil hs
    (formulaIso P V σ π d).symm (asIso (terminalComparison (F)))
    (S₁).formulaOccurrences (S₁).lists.algebra.nil
    (sentence_occurrences_comparison P V σ π d) (sentence_nil_comparison P V σ π d)

def mappedSentenceIso : (F).obj (S₀).sentenceObject ≅ (S₁).sentenceObject :=
  (sentenceComparisonPullback P V σ π d).isoPullback

def sentenceIso : (S₁).sentenceObject ≅ (F).obj (S₀).sentenceObject :=
  (mappedSentenceIso P V σ π d).symm

@[reassoc] theorem mappedSentenceIso_inclusion :
    (mappedSentenceIso P V σ π d).hom ≫ (S₁).sentenceInclusion=
      (F).map (S₀).sentenceInclusion ≫ (formulaIso P V σ π d).inv :=
  (sentenceComparisonPullback P V σ π d).isoPullback_hom_fst

@[reassoc] theorem sentenceIso_inclusion :
    (sentenceIso P V σ π d).hom ≫ (F).map (S₀).sentenceInclusion=
      (S₁).sentenceInclusion ≫ (formulaIso P V σ π d).hom := by
  exact inverse_comparison_square (mappedSentenceIso P V σ π d) (formulaIso P V σ π d).symm
    ((F).map (S₀).sentenceInclusion) (S₁).sentenceInclusion
    (mappedSentenceIso_inclusion P V σ π d).symm

@[reassoc] theorem sentenceIso_inverse_inclusion :
    (sentenceIso P V σ π d).inv ≫ (S₁).sentenceInclusion=
      (F).map (S₀).sentenceInclusion ≫ (formulaIso P V σ π d).inv :=
  mappedSentenceIso_inclusion P V σ π d

theorem formula_negation_comparison :
    (formulaIso P V σ π d).hom ≫ (F).map (S₀).negationConstructor=
      (S₁).negationConstructor ≫ (formulaIso P V σ π d).hom := by
  exact inverse_comparison_square (formulaIso P V σ π d).symm (formulaIso P V σ π d).symm
    ((F).map (S₀).negationConstructor) (S₁).negationConstructor
    (negation_constructor P V σ π d)

@[reassoc] theorem sentence_negation_comparison :
    (sentenceIso P V σ π d).hom ≫ (F).map (S₀).sentenceNegation=
      (S₁).sentenceNegation ≫ (sentenceIso P V σ π d).hom := by
  have hs := congrArg
    (fun u : (S₀).sentenceObject ⟶ (S₀).algebra.a.2 => (F).map u)
    (CategoricalSyntax.sentenceNegation_inclusion (S₀))
  change (F).map ((S₀).sentenceNegation ≫ (S₀).sentenceInclusion) =
    (F).map ((S₀).sentenceInclusion ≫ (S₀).negationConstructor) at hs
  simp only [Functor.map_comp] at hs
  exact restriction_natural (sentenceIso P V σ π d).hom (formulaIso P V σ π d).hom
    ((F).map (S₀).sentenceInclusion) (S₁).sentenceInclusion
    ((F).map (S₀).sentenceNegation) (S₁).sentenceNegation
    ((F).map (S₀).negationConstructor) (S₁).negationConstructor
    (sentenceIso_inclusion P V σ π d) (formula_negation_comparison P V σ π d)
    hs (CategoricalSyntax.sentenceNegation_inclusion (S₁))

/-- The input is a point code of the chosen sentence pullback. Its output
is a formula word, obtained through the actual inclusion and formula chart. -/
theorem sentenceInclusion_graph (point word : ℕ) :
    word ∈ Total.val ((S₁).sentenceInclusion ≫ (formulaIso P V σ π d).hom).hom point ↔
      ∃ q : PredicateInterpretation.Obj ℕ (S₀).sentenceObject,
        q.val ∈ Total.val (sentenceIso P V σ π d).hom.hom point ∧
          ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (S₀).sentenceInclusion q).val = word := by
  have hc :
      word ∈ Total.val ((S₁).sentenceInclusion ≫ (formulaIso P V σ π d).hom).hom point ↔
        ∃ n, n ∈ Total.val (sentenceIso P V σ π d).hom.hom point ∧
          word ∈ Total.val ((F).map (S₀).sentenceInclusion).hom n :=
    (Iff.of_eq (congrArg
      (fun u : (S₁).sentenceObject ⟶ (F).obj (S₀).algebra.a.2 =>
        word ∈ Total.val u.hom point)
      (sentenceIso_inclusion P V σ π d).symm)).trans
      (Total.mem_val_comp (sentenceIso P V σ π d).hom.hom
        ((F).map (S₀).sentenceInclusion).hom point word)
  refine hc.trans ?_
  constructor
  · rintro ⟨n,hn,hw⟩
    obtain ⟨q,hq,hword⟩ := (Syntax.predicateFunctor_graph P (S₀).sentenceInclusion n word).mp hw
    exact ⟨q,hq.symm ▸ hn,hword⟩
  · rintro ⟨q,hq,hword⟩
    exact ⟨q.val,hq,(Syntax.predicateFunctor_graph P (S₀).sentenceInclusion q.val word).mpr
      ⟨q,rfl,hword⟩⟩

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
