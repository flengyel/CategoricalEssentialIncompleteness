/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDomainSplitting
public import CategoricalEssentialIncompleteness.V46ArithmeticLiteralCoordinates
public import CategoricalEssentialIncompleteness.SyntacticPreservation

/-! # The explicit chosen-domain extension used in the arithmetic comparison

The extension splits each interpreted idempotent through its actual fixed
points. On total morphisms it is the existing canonical domain functor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension


open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def canonicalExtension : RangeFunctor (SplitObject (CodedProgramCategory 𝗣𝗔)) Pfn :=
  extension (SyntacticModel.rangeFunctor 𝗣𝗔 M)

theorem canonical_map_total {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (canonicalExtension M).toFunctor.map f.hom =
      (fun x => Part.some ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map f x)) := by
  apply PFun.ext
  intro x y
  exact (mem_extension (SyntacticModel.rangeFunctor 𝗣𝗔 M) f.hom x y).trans
    ((SyntacticModel.mem_arrow 𝗣𝗔 M f.hom.hom x.val y.val).trans
      ((PredicateInterpretation.canonicalDomainFunctor_graph 𝗣𝗔 M f x y).symm.trans
        (eq_comm.trans Part.mem_some_iff.symm)))

open ArithmeticLiteralModel

def sentenceTheory (Γ : Carrier) : Idem NamedArithmeticLiteralTotal.literalSentence.obj :=
  Ranges.range ((realization 𝗣𝗔).map (conclusion Γ)).hom

def sentenceNegation : NamedArithmeticLiteralTotal.literalSentence.obj ⟶
    NamedArithmeticLiteralTotal.literalSentence.obj :=
  ((realization 𝗣𝗔).map negation).hom

theorem interpreted_theory (Γ : Carrier) :
    (canonicalExtension M).mapIdem (sentenceTheory Γ) =
      ArithmeticLiteralCoordinates.theory M Γ := by
  apply Idem.ext
  change (canonicalExtension M).toFunctor.map
    (Ranges.range ((realization 𝗣𝗔).map (conclusion Γ)).hom).hom = _
  exact ((canonicalExtension M).map_range ((realization 𝗣𝗔).map (conclusion Γ)).hom).trans
    (congrArg (fun g => (Ranges.range g).hom)
      (canonical_map_total M ((realization 𝗣𝗔).map (conclusion Γ))))

theorem interpreted_negation :
    (canonicalExtension M).toFunctor.map sentenceNegation =
      ArithmeticLiteralCoordinates.negationMap M :=
  canonical_map_total M ((realization 𝗣𝗔).map negation)

theorem source_noncoverage (Γ : Carrier)
    (h : ArithmeticLiteralCoordinates.theory M Γ ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap M)
        (ArithmeticLiteralCoordinates.theory M Γ) ≠ ⊤) :
    sentenceTheory Γ ⊔ Idem.pull sentenceNegation (sentenceTheory Γ) ≠ ⊤ := by
  apply source_noncoverage_of_interpretation (canonicalExtension M)
    (sentenceTheory Γ) sentenceNegation
  have he := congrArg₂ (fun a f => a ⊔ Idem.pull f a)
    (interpreted_theory M Γ) (interpreted_negation M)
  exact fun hc => h (he.symm.trans hc)

end CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension
