/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderGeneration

/-! # Consistent signed pairs and their first-order theory functors -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SignedFirstOrder

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

structure Pair (F : NullaryPresentations V) where
  carrier : D
  positive : Subobject carrier
  negative : Subobject carrier
  disjoint : positive ⊓ negative = ⊥
  consistent : (F.presentation carrier).Consistent (theory F positive negative).val

namespace Pair

variable {F : NullaryPresentations V}

structure Hom (A B : Pair F) where
  arrow : A.carrier ⟶ B.carrier
  positive : A.positive ≤ (Subobject.pullback arrow).obj B.positive
  negative : A.negative ≤ (Subobject.pullback arrow).obj B.negative

namespace Hom

@[ext] theorem ext {A B : Pair F} {f g : Hom A B} (h : f.arrow = g.arrow) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : Pair F) : Hom A A where
  arrow := 𝟙 _
  positive := by rw [Subobject.pullback_id]
  negative := by rw [Subobject.pullback_id]

def comp {A B C : Pair F} (f : Hom A B) (g : Hom B C) : Hom A C where
  arrow := f.arrow ≫ g.arrow
  positive := by
    rw [Subobject.pullback_comp]
    exact f.positive.trans (leOfHom ((Subobject.pullback f.arrow).map (homOfLE g.positive)))
  negative := by
    rw [Subobject.pullback_comp]
    exact f.negative.trans (leOfHom ((Subobject.pullback f.arrow).map (homOfLE g.negative)))

end Hom

instance : Category.{v} (Pair F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext; exact Category.id_comp f.arrow
  comp_id f := by apply Hom.ext; exact Category.comp_id f.arrow
  assoc f g h := by apply Hom.ext; exact Category.assoc f.arrow g.arrow h.arrow

end Pair

variable (F : NullaryPresentations V)

abbrev Theories := FirstOrderPresentation.ConsistentTheoryCategory (D := D) (V := V)

def generatedObject (A : Pair F) : Theories (D := D) (V := V) :=
  ⟨⟨⟨F.presentation A.carrier, (theory F A.positive A.negative).val⟩,
    (theory F A.positive A.negative).property⟩, A.consistent⟩

def extractionObject (A : Theories (D := D) (V := V)) : Pair F where
  carrier := A.presentation.syntaxData.sentenceObject
  positive := A.theory.val
  negative := (Subobject.pullback A.presentation.syntaxData.sentenceNegation).obj A.theory.val
  disjoint := A.consistent
  consistent := evaluation_consistent F A.presentation A.theory A.consistent

def generationMap {A B : Pair F} (f : A ⟶ B) : generatedObject F A ⟶ generatedObject F B := by
  refine ObjectProperty.homMk (ObjectProperty.homMk ⟨F.map f.arrow, ?_⟩)
  apply (interpretation_theory_bound F (F.presentation B.carrier)
    (f.arrow ≫ NullaryInterpretation.atomSentence (F.syntaxData B.carrier))
      A.positive A.negative (theory F B.positive B.negative)).mpr
  have h := atomic_bounds F B.positive B.negative
  simp only [Subobject.pullback_comp]
  exact ⟨f.positive.trans (leOfHom ((Subobject.pullback f.arrow).map (homOfLE h.1))),
    f.negative.trans (leOfHom ((Subobject.pullback f.arrow).map (homOfLE h.2)))⟩

def generation : Pair F ⥤ Theories (D := D) (V := V) where
  obj := generatedObject F
  map := generationMap F
  map_id A := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply FirstOrderPresentation.Axioms.Hom.ext
    exact F.map_id A.carrier
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply FirstOrderPresentation.Axioms.Hom.ext
    exact F.map_comp f.arrow g.arrow

def extractionMap {A B : Theories (D := D) (V := V)} (f : A ⟶ B) :
    extractionObject F A ⟶ extractionObject F B := by
  let σ := f.hom.hom.translation
  have hp : A.theory.val ≤ (Subobject.pullback σ.sentence).obj B.theory.val :=
    (Subobject.existsPullbackAdj σ.sentence).gc _ _ |>.mp f.hom.hom.bound
  refine ⟨σ.sentence, hp, ?_⟩
  have hn := leOfHom ((Subobject.pullback A.presentation.syntaxData.sentenceNegation).map
    (homOfLE hp))
  have he : A.presentation.syntaxData.sentenceNegation ≫ σ.sentence =
      σ.sentence ≫ B.presentation.syntaxData.sentenceNegation := σ.sentence_negation
  rw [← Subobject.pullback_comp, he, Subobject.pullback_comp] at hn
  exact hn

def extraction : Theories (D := D) (V := V) ⥤ Pair F where
  obj := extractionObject F
  map := extractionMap F
  map_id _ := by apply Pair.Hom.ext; rfl
  map_comp _ _ := by apply Pair.Hom.ext; rfl

end CategoricalEssentialIncompleteness.V46.SignedFirstOrder
