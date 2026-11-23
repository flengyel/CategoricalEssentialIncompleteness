/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TuringObjectRecognition
public import CategoricalEssentialIncompleteness.V46SummandBounds
public import CategoricalEssentialIncompleteness.V46SliceUnitFactorization
public import CategoricalEssentialIncompleteness.V46PropositionalRuleClosure
public import CategoricalEssentialIncompleteness.V46StrictPresentationFunctors

/-! # Turing parameters, domains, slice units and theorem images -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
universe u v
section Turing
open PCategoryStruct RecursionCategory
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
example (U : C) : (∀ A B : C, ∃ e : nearProd U A ⟶ B, IsTuringMorphism e) ↔
    (∃ e : nearProd U U ⟶ U, IsTuringMorphism e) ∧
      ∀ X : C, ∃ (m : X ⟶ U) (r : U ⟶ X), isTotal m ∧ m ≫ r = 𝟙 X := turingObject_iff U
end Turing

section Domains
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
open CategoryTheory.Idempotents
example {P Q : Karoubi C} (f : P ⟶ Q) : P.p ≫ rst f.f = P.p ↔ isTotal f :=
  (LocalConnectedness.V46.KaroubiRestriction.total_iff f).symm
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]
variable [HasZeroMorphisms C] [RestrictionZero C]
example (A B : C) : PairComplementary (summand0 A B) (summand1 A B) := summands_pairComplementary A B
end Domains

section Slice
open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U) [Mono i] (invMono : MonoInverses C)
example (q : PartialMaps.Par (Over U)) :
    (∃ k : q.obj.left ⟶ T, k ≫ i = q.obj.hom) ↔
      isTotal ((PartialSliceChangeBase.rightAdjunction i invMono).unit.app q) :=
  (PartialSliceChangeBase.right_unit_total_iff i invMono q).symm
end Slice

section Rules
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {S A : D} (ν : S ⟶ S) (μ : S ⨯ S ⟶ S) (a : A ⟶ S)
open PropositionalRules
example {Q : D} (m : Q ⟶ S) :
    ClosedUnder (rules ν μ a).inference m ↔
      (∃ h, h ≫ m = axioms ν μ a) ∧
      ∃ k, k ≫ m = pullback.fst (prod.lift prod.fst μ) (prod.map m m) ≫ prod.snd :=
  closed_iff ν μ a m
example (P : Endofunctor.Algebra (rules ν μ a).inference) (hP : IsInitial P) :
    ClosedUnder (rules ν μ a).inference (image.ι P.a.hom) ∧
      ∀ {Q : D} (m : Q ⟶ S) [Mono m], ClosedUnder (rules ν μ a).inference m →
        ∃ k, k ≫ m = image.ι P.a.hom := least_theorems ν μ a P hP
end Rules

section Totals
variable {D : Type u} [Category.{v} D] [HasPullbacks D]
open PartialMaps
example : toTotal (D := D) ⋙ fromTotal = 𝟭 D := (totalIsomorphism (D := D)).unit_eq.symm
example : fromTotal (D := D) ⋙ toTotal = 𝟭 (PartialMaps.Tot D) := (totalIsomorphism (D := D)).counit_eq
end Totals

open FFL.FirstOrder.Arithmetic TrueArithmetic
example : interpretation ⋙ interpretationIsomorphism.inverse = 𝟭 _ :=
  interpretationIsomorphism.unit_eq.symm
example : interpretationIsomorphism.inverse ⋙ interpretation = 𝟭 _ :=
  interpretationIsomorphism.counit_eq
