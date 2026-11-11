/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSentenceAxiomPullbacks


/-! # Statement checks in `V46MillerSentenceAxiomPullbacksChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

variable {P : Uniform.Family}

example {X Y : Total.TotalCategory P} (f : X ⟶ Y) [Mono f] (w x : ℕ) :
    x ∈ Total.val (PartialSpans.inverse f) w ↔ w ∈ Total.val f.hom x :=
  SentenceAxiomPullbacks.partialInverse_graph f w x

variable {Fm : PredicateCategory 𝗣𝗔} {S : Total.TotalCategory P}
variable (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))

example : Uniform.Enumerable P (fun x => ∃ w,w ∈ Total.val s.hom x ∧ w ∈ Γ) :=
  SentenceAxiomPullbacks.pulledSupport_enumerable s Γ hΓ

example (x : ℕ) :
    x ∈ (SentenceAxiomPullbacks.axCarrier s Γ hΓ).obj.support ↔
      ∃ w,w ∈ Total.val s.hom x ∧ w ∈ Γ :=
  SentenceAxiomPullbacks.axCarrier_support s Γ hΓ x

example (x y : ℕ) :
    y ∈ Total.val (SentenceAxiomPullbacks.inclusion s Γ hΓ).hom x ↔
      x ∈ (SentenceAxiomPullbacks.axCarrier s Γ hΓ).obj.support ∧ y=x :=
  SentenceAxiomPullbacks.inclusion_graph s Γ hΓ x y

example : AxiomSubobjects.imageCodes (SentenceAxiomPullbacks.inclusion s Γ hΓ ≫ s)=
    Γ ∩ AxiomSubobjects.imageCodes s :=
  SentenceAxiomPullbacks.imageCodes_inclusion s Γ hΓ

example (hΓS : Γ ⊆ AxiomSubobjects.imageCodes s) :
    AxiomSubobjects.imageCodes (SentenceAxiomPullbacks.inclusion s Γ hΓ ≫ s)=Γ :=
  SentenceAxiomPullbacks.imageCodes_of_sentence_codes s Γ hΓ hΓS

example : IsPullback (SentenceAxiomPullbacks.inclusion s Γ hΓ)
    (SentenceAxiomPullbacks.wordProjection s Γ hΓ) s (AxiomSubobjects.axiomInclusion P Fm Γ hΓ) :=
  SentenceAxiomPullbacks.axiomPullback s Γ hΓ

example (x w : ℕ) :
    w ∈ Total.val (SentenceAxiomPullbacks.wordProjection s Γ hΓ).hom x ↔
      x ∈ (SentenceAxiomPullbacks.axCarrier s Γ hΓ).obj.support ∧ w ∈ Total.val s.hom x :=
  SentenceAxiomPullbacks.wordProjection_graph s Γ hΓ x w

example (L : List ℕ) (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,∃ x,w ∈ Total.val s.hom x)
    (w x : ℕ) :
    x ∈ Total.val (SentenceAxiomPullbacks.finiteLift s Γ hΓ L hLΓ hLS).hom w ↔
      w ∈ L ∧ w ∈ Total.val s.hom x :=
  SentenceAxiomPullbacks.finiteLift_graph s Γ hΓ L hLΓ hLS w x

example (L : List ℕ) (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,∃ x,w ∈ Total.val s.hom x) :
    SentenceAxiomPullbacks.finiteLift s Γ hΓ L hLΓ hLS ≫
      SentenceAxiomPullbacks.inclusion s Γ hΓ ≫ s=
        SentenceAxiomPullbacks.finiteFormulaInclusion s L hLS :=
  SentenceAxiomPullbacks.finiteLift_formula s Γ hΓ L hLΓ hLS

example (L : List ℕ) (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,∃ x,w ∈ Total.val s.hom x) :
    SentenceAxiomPullbacks.finiteLift s Γ hΓ L hLΓ hLS ≫
      SentenceAxiomPullbacks.wordProjection s Γ hΓ=
        AxiomSubobjects.finiteIntoAxioms P Fm Γ hΓ L hLΓ
          (fun w hw => AxiomSubobjects.imageCodes_sentence s w (hLS w hw)) :=
  SentenceAxiomPullbacks.finiteLift_wordProjection s Γ hΓ L hLΓ hLS

example (L : List ℕ) (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,∃ x,w ∈ Total.val s.hom x) :
    Subobject.mk (SentenceAxiomPullbacks.finiteToSentence s L hLS) ≤
      Subobject.mk (SentenceAxiomPullbacks.inclusion s Γ hΓ) :=
  SentenceAxiomPullbacks.finiteSubobject_le s Γ hΓ L hLΓ hLS

example (L : List ℕ) (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,∃ x,w ∈ Total.val s.hom x) :
    Subobject.mk (SentenceAxiomPullbacks.finiteFormulaInclusion s L hLS) ≤
      Subobject.mk (SentenceAxiomPullbacks.inclusion s Γ hΓ ≫ s) :=
  SentenceAxiomPullbacks.finiteWordSubobject_le s Γ hΓ L hLΓ hLS

variable {B : Total.TotalCategory P} (a : B ⟶ S) [Mono a]

example : Uniform.Enumerable P (fun w => ∃ b,w ∈ Total.val (a ≫ s).hom b) :=
  SentenceAxiomPullbacks.givenCodes_enumerable s a

example : AxiomSubobjects.imageCodes
    (SentenceAxiomPullbacks.inclusion s (AxiomSubobjects.imageCodes (a ≫ s))
      (AxiomSubobjects.imageCodes_enumerable (a ≫ s)) ≫ s)=AxiomSubobjects.imageCodes (a ≫ s) :=
  SentenceAxiomPullbacks.givenCodes_recovered s a

example (x : ℕ) :
    x ∈ (SentenceAxiomPullbacks.axCarrier s (AxiomSubobjects.imageCodes (a ≫ s))
      (AxiomSubobjects.imageCodes_enumerable (a ≫ s))).obj.support ↔
      x ∈ Total.support (Ranges.range a.hom) :=
  SentenceAxiomPullbacks.pulled_given_support s a x

example : B ≅ SentenceAxiomPullbacks.axCarrier s (AxiomSubobjects.imageCodes (a ≫ s))
    (AxiomSubobjects.imageCodes_enumerable (a ≫ s)) :=
  SentenceAxiomPullbacks.givenPresentation s a

example : (SentenceAxiomPullbacks.givenPresentation s a).hom ≫
    SentenceAxiomPullbacks.inclusion s (AxiomSubobjects.imageCodes (a ≫ s))
      (AxiomSubobjects.imageCodes_enumerable (a ≫ s))=a :=
  SentenceAxiomPullbacks.givenPresentation_inclusion s a

example (b x : ℕ) :
    x ∈ Total.val (SentenceAxiomPullbacks.givenPresentation s a).hom.hom b ↔ x ∈ Total.val a.hom b :=
  SentenceAxiomPullbacks.givenPresentation_graph s a b x

example (x b : ℕ) :
    b ∈ Total.val (SentenceAxiomPullbacks.givenPresentation s a).inv.hom x ↔
      x ∈ (SentenceAxiomPullbacks.axCarrier s (AxiomSubobjects.imageCodes (a ≫ s))
        (AxiomSubobjects.imageCodes_enumerable (a ≫ s))).obj.support ∧ x ∈ Total.val a.hom b :=
  SentenceAxiomPullbacks.givenPresentation_inverse_graph s a x b

example : Subobject.mk a=Subobject.mk (SentenceAxiomPullbacks.inclusion s
    (AxiomSubobjects.imageCodes (a ≫ s)) (AxiomSubobjects.imageCodes_enumerable (a ≫ s))) :=
  SentenceAxiomPullbacks.given_subobject_eq s a

example : Total.imageObject a ≅ SentenceAxiomPullbacks.axCarrier s (AxiomSubobjects.imageCodes (a ≫ s))
    (AxiomSubobjects.imageCodes_enumerable (a ≫ s)) :=
  SentenceAxiomPullbacks.imagePresentation s a

example : (SentenceAxiomPullbacks.imagePresentation s a).hom ≫
    SentenceAxiomPullbacks.inclusion s (AxiomSubobjects.imageCodes (a ≫ s))
      (AxiomSubobjects.imageCodes_enumerable (a ≫ s))=Total.imageInclusion a :=
  SentenceAxiomPullbacks.imagePresentation_inclusion s a
