/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderPresentationAdjunction
public import CategoricalEssentialIncompleteness.V46FirstOrderReflection
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheoryTotal

/-! # Generation adjunctions in the total restriction splitting

The initial derivation algebras used here are the constructed algebras for
arbitrary nonlogical axiom presentations. The resulting reflectors require
no initiality premise from the caller.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "S" => SyntacticSyntax.plainTotalCategoricalSyntax T V σ π d
local notation "P" => SyntacticGeneratedTheoryTotal.proofAlgebra T V σ π d
local notation "hP" => SyntacticGeneratedTheoryTotal.proofInitial T V σ π d

abbrev ClosedTheories := FirstOrderPresentations.TheoryCategory (P)

def inclusion : ClosedTheories T V σ π d ⥤ Over (S).sentenceObject :=
  FirstOrderPresentations.inclusion (P)

instance inclusion_full : (inclusion T V σ π d).Full :=
  inferInstanceAs ((FirstOrderPresentations.inclusion (P)).Full)

instance inclusion_faithful : (inclusion T V σ π d).Faithful :=
  inferInstanceAs ((FirstOrderPresentations.inclusion (P)).Faithful)

def generation : Over (S).sentenceObject ⥤ ClosedTheories T V σ π d :=
  FirstOrderPresentations.generation (P) (hP)

def adjunction : generation T V σ π d ⊣ inclusion T V σ π d :=
  FirstOrderPresentations.adjunction (P) (hP)

theorem closed_iff (B : Over (S).sentenceObject) :
    FirstOrderPresentations.Closed (P) B ↔
      Mono B.hom ∧ SyntacticGeneratedTheoryTotal.IsSentenceTheory T V σ π d B.hom :=
  Iff.rfl

theorem generation_image (A : Over (S).sentenceObject) :
    ((generation T V σ π d).obj A).obj.hom =
      image.ι (SyntacticGeneratedTheoryTotal.sentenceConclusion T V σ π d A.hom) := rfl

abbrev ClosedSubobjects := FirstOrderGeneration.ClosedTheory (P)

def subobjectInclusion : ClosedSubobjects T V σ π d ⥤ Subobject (S).sentenceObject :=
  FirstOrderGeneration.inclusion (P)

def subobjectGeneration : Subobject (S).sentenceObject ⥤ ClosedSubobjects T V σ π d :=
  FirstOrderGeneration.generation (P) (hP)

def subobjectAdjunction : subobjectGeneration T V σ π d ⊣ subobjectInclusion T V σ π d :=
  FirstOrderGeneration.adjunction (P) (hP)

theorem generated_sentence_subobject (A : Subobject (S).sentenceObject) :
    ((subobjectGeneration T V σ π d).obj A).val =
      SyntacticGeneratedTheoryTotal.sentenceTheory T V σ π d A.arrow := rfl

abbrev SentenceTheories := FirstOrderReflection.Theory
  (fun A : Subobject (S).sentenceObject => (P) A.arrow)

def sentenceInclusion : SentenceTheories T V σ π d ⥤ Subobject (S).sentenceObject :=
  FirstOrderReflection.inclusion (fun A => (P) A.arrow)

def sentenceGeneration : Subobject (S).sentenceObject ⥤ SentenceTheories T V σ π d :=
  FirstOrderReflection.generation (fun A => (P) A.arrow) (fun A => (hP) A.arrow)

def sentenceAdjunction : sentenceGeneration T V σ π d ⊣ sentenceInclusion T V σ π d :=
  FirstOrderReflection.adjunction (fun A => (P) A.arrow) (fun A => (hP) A.arrow)

def axiomInclusion : SentenceTheories T V σ π d ⥤ Over (S).sentenceObject :=
  FirstOrderReflection.presentationInclusion (fun A => (P) A.arrow)

def axiomGeneration : Over (S).sentenceObject ⥤ SentenceTheories T V σ π d :=
  FirstOrderReflection.presentationGeneration (fun A => (P) A.arrow) (fun A => (hP) A.arrow)

def axiomAdjunction : axiomGeneration T V σ π d ⊣ axiomInclusion T V σ π d :=
  FirstOrderReflection.presentationAdjunction (fun A => (P) A.arrow) (fun A => (hP) A.arrow)

theorem axiomGeneration_image (A : Over (S).sentenceObject) :
    ((axiomGeneration T V σ π d).obj A).val =
      SyntacticGeneratedTheoryTotal.sentenceTheory T V σ π d
        (imageSubobject A.hom).arrow := rfl

theorem axiomGeneration_original (A : Over (S).sentenceObject) :
    ((axiomGeneration T V σ π d).obj A).val =
      SyntacticGeneratedTheoryTotal.sentenceTheory T V σ π d A.hom :=
  (FirstOrderReflection.presentation_generated_comparison (P) (hP) A.hom).symm

end CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction
