/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerAxiomSubobjects


/-! # Statement checks in `V46MillerAxiomSubobjectsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

variable (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (A : Set ℕ)
variable (hA : Uniform.Enumerable P (· ∈ A))

example (n : ℕ) : n ∈ ((Syntax.predicateFunctor P).obj (finiteCarrier [n])).obj.support :=
  (AxiomSubobjects.mapped_finite_support P [n] n).mpr (by simp)

example : Uniform.Enumerable P (· ∈ AxiomSubobjects.axiomSupport P S A) :=
  AxiomSubobjects.axiomSupport_enumerable P S A hA

example (n : ℕ) :
    n ∈ (AxiomSubobjects.axCarrier P S A hA).obj.support ↔
      n ∈ A ∧ S.val.Evalb (M := ℕ) ![n] :=
  AxiomSubobjects.axCarrier_support P S A hA n

example (n m : ℕ) :
    m ∈ Total.val (AxiomSubobjects.axiomInclusion P S A hA).hom n ↔
      n ∈ A ∧ S.val.Evalb (M := ℕ) ![n] ∧ m=n :=
  AxiomSubobjects.axiomInclusion_graph P S A hA n m

example : Mono (AxiomSubobjects.axiomInclusion P S A hA) := inferInstance

example (L : List ℕ) (hLA : ∀ n ∈ L,n ∈ A)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) (n m : ℕ) :
    m ∈ Total.val (AxiomSubobjects.finiteIntoAxioms P S A hA L hLA hLS).hom n ↔
      n ∈ L ∧ m=n :=
  AxiomSubobjects.finiteIntoAxioms_graph P S A hA L hLA hLS n m

example (L : List ℕ) (hLA : ∀ n ∈ L,n ∈ A)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    AxiomSubobjects.finiteIntoAxioms P S A hA L hLA hLS ≫
      AxiomSubobjects.axiomInclusion P S A hA = AxiomSubobjects.finiteIntoSentence P S L hLS :=
  AxiomSubobjects.finiteIntoAxioms_fac P S A hA L hLA hLS

example (L : List ℕ) (hLA : ∀ n ∈ L,n ∈ A)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    Subobject.mk (AxiomSubobjects.finiteIntoSentence P S L hLS) ≤
      AxiomSubobjects.axiomSubobject P S A hA :=
  AxiomSubobjects.finiteSubobject_le P S A hA L hLA hLS

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    Uniform.Enumerable P (fun n => ∃ x,n ∈ Total.val a.hom x) :=
  AxiomSubobjects.imageCodes_enumerable a

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    AxiomSubobjects.axCarrier P S (AxiomSubobjects.imageCodes a)
      (AxiomSubobjects.imageCodes_enumerable a) ≅ Total.imageObject a :=
  AxiomSubobjects.imageCarrierIso a

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) (n m : ℕ) :
    m ∈ Total.val (AxiomSubobjects.imageCarrierIso a).hom.hom n ↔
      (∃ x,n ∈ Total.val a.hom x) ∧ m=n :=
  AxiomSubobjects.imageCarrierIso_graph a n m

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    (AxiomSubobjects.imageCarrierIso a).hom ≫ Total.imageInclusion a =
      AxiomSubobjects.axiomInclusion P S (AxiomSubobjects.imageCodes a)
        (AxiomSubobjects.imageCodes_enumerable a) :=
  AxiomSubobjects.imageCarrierIso_inclusion a

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    X ≅ AxiomSubobjects.axCarrier P S (AxiomSubobjects.imageCodes a)
      (AxiomSubobjects.imageCodes_enumerable a) :=
  AxiomSubobjects.monoPresentation a

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    (AxiomSubobjects.monoPresentation a).hom ≫
      AxiomSubobjects.axiomInclusion P S (AxiomSubobjects.imageCodes a)
        (AxiomSubobjects.imageCodes_enumerable a) = a :=
  AxiomSubobjects.monoPresentation_inclusion a

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] (n m : ℕ) :
    m ∈ Total.val (AxiomSubobjects.monoPresentation a).hom.hom n ↔ m ∈ Total.val a.hom n :=
  AxiomSubobjects.monoPresentation_graph a n m

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] (n m : ℕ) :
    n ∈ Total.val (AxiomSubobjects.monoPresentation a).inv.hom m ↔ m ∈ Total.val a.hom n :=
  AxiomSubobjects.monoPresentation_inverse_graph a n m

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    Subobject.mk a = AxiomSubobjects.axiomSubobject P S (AxiomSubobjects.imageCodes a)
      (AxiomSubobjects.imageCodes_enumerable a) :=
  AxiomSubobjects.mono_subobject_eq a

example (X Y : Total.TotalCategory P) (hXY : X.obj.support ⊆ Y.obj.support) (n m : ℕ) :
    m ∈ Total.val (AxiomSubobjects.supportInclusion X Y hXY).hom n ↔ n ∈ X.obj.support ∧ m=n :=
  AxiomSubobjects.supportInclusion_graph X Y hXY n m

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a]
    (L : List ℕ) (hL : ∀ n ∈ L,∃ x,n ∈ Total.val a.hom x) :
    AxiomSubobjects.finiteIntoGivenMono a L hL ≫ a =
      AxiomSubobjects.finiteIntoSentence P S L
        (fun n hn => AxiomSubobjects.imageCodes_sentence a n (hL n hn)) :=
  AxiomSubobjects.finiteIntoGivenMono_fac a L hL

example {X : Total.TotalCategory P} (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a]
    (L : List ℕ) (hL : ∀ n ∈ L,∃ x,n ∈ Total.val a.hom x) :
    Subobject.mk (AxiomSubobjects.finiteIntoSentence P S L
      (fun n hn => AxiomSubobjects.imageCodes_sentence a n (hL n hn))) ≤ Subobject.mk a :=
  AxiomSubobjects.finiteSubobject_le_givenMono a L hL
