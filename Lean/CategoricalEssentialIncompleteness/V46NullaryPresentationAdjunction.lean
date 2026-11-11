/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalInterpretation
public import CategoricalEssentialIncompleteness.V46ConsistentFirstOrderTheories

/-! # The adjunction between nullary-predicate presentations and sentence objects -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

structure NullaryPresentations (V : D) where
  syntaxData (X : D) : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0
  proofs (X : D) (A : Subobject (syntaxData X).sentenceObject) :
    Endofunctor.Algebra ((syntaxData X).logicalRules A.arrow).inference
  initial (X : D) (A : Subobject (syntaxData X).sentenceObject) : IsInitial (proofs X A)

namespace NullaryPresentations

variable {V : D} (F : NullaryPresentations V)

def presentation (X : D) : FirstOrderPresentation V :=
  NullaryInterpretation.presentation (F.syntaxData X) (F.proofs X) (F.initial X)

def interpretation {X : D} (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    FirstOrderPresentation.Translation (F.presentation X) R :=
  NullaryInterpretation.translation (F.syntaxData X) (F.proofs X) (F.initial X) R a

@[reassoc (attr := simp)] theorem interpretation_atom {X : D}
    (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    NullaryInterpretation.atomSentence (F.syntaxData X) ≫ (F.interpretation R a).sentence = a :=
  NullaryInterpretation.translation_atom (F.syntaxData X) (F.proofs X) (F.initial X) R a

theorem interpretation_unique {X : D} (R : FirstOrderPresentation V)
    (a : X ⟶ R.syntaxData.sentenceObject) (τ : (F.presentation X).Translation R)
    (ha : NullaryInterpretation.atomSentence (F.syntaxData X) ≫ τ.sentence = a) :
    τ = F.interpretation R a :=
  NullaryInterpretation.translation_unique (F.syntaxData X) (F.proofs X) (F.initial X) R a τ ha

def map {X Y : D} (f : X ⟶ Y) : (F.presentation X).Translation (F.presentation Y) :=
  F.interpretation (F.presentation Y) (f ≫ NullaryInterpretation.atomSentence (F.syntaxData Y))

theorem map_id (X : D) : F.map (𝟙 X) = FirstOrderPresentation.Translation.id (F.presentation X) := by
  apply (F.interpretation_unique (F.presentation X)
    (𝟙 X ≫ NullaryInterpretation.atomSentence (F.syntaxData X))
      (FirstOrderPresentation.Translation.id (F.presentation X)) ?_).symm
  simp only [FirstOrderPresentation.Translation.id, Category.id_comp]
  exact Category.comp_id _

theorem map_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = FirstOrderPresentation.Translation.comp (F.map f) (F.map g) := by
  apply (F.interpretation_unique (F.presentation Z)
    ((f ≫ g) ≫ NullaryInterpretation.atomSentence (F.syntaxData Z))
      (FirstOrderPresentation.Translation.comp (F.map f) (F.map g)) ?_).symm
  change NullaryInterpretation.atomSentence (F.syntaxData X) ≫
      ((F.map f).sentence ≫ (F.map g).sentence) = _
  simp only [map, Category.assoc, interpretation_atom_assoc, interpretation_atom]

def functor : D ⥤ FirstOrderPresentation V where
  obj := F.presentation
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

def homEquiv (X : D) (R : FirstOrderPresentation V) :
    (F.functor.obj X ⟶ R) ≃ (X ⟶ R.syntaxData.sentenceObject) where
  toFun τ := NullaryInterpretation.atomSentence (F.syntaxData X) ≫ τ.sentence
  invFun a := F.interpretation R a
  left_inv τ := (F.interpretation_unique R _ τ rfl).symm
  right_inv a := F.interpretation_atom R a

def adjunction : F.functor ⊣ FirstOrderPresentation.sentenceFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := F.homEquiv
    homEquiv_naturality_left_symm := by
      intro X Y R f a
      symm
      change FirstOrderPresentation.Translation.comp (F.map f) (F.interpretation R a) =
        F.interpretation R (f ≫ a)
      apply F.interpretation_unique
      change NullaryInterpretation.atomSentence (F.syntaxData X) ≫
        ((F.map f).sentence ≫ (F.interpretation R a).sentence) = _
      simp only [map, Category.assoc, interpretation_atom_assoc, interpretation_atom]
    homEquiv_naturality_right := by
      intro X R T a τ
      change NullaryInterpretation.atomSentence (F.syntaxData X) ≫ (a.sentence ≫ τ.sentence) =
        (NullaryInterpretation.atomSentence (F.syntaxData X) ≫ a.sentence) ≫ τ.sentence
      exact (Category.assoc _ _ _).symm }

end NullaryPresentations

end CategoricalEssentialIncompleteness.V46
