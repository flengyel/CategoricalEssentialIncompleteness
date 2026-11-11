/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlainTotal
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTotal
public import CategoricalEssentialIncompleteness.V46FirstOrderTheory
public import CategoricalEssentialIncompleteness.V46SentenceTheoryClosure
public import CategoricalEssentialIncompleteness.V46TotalSentenceImages

/-! # The generated first-order theory in the actual total split category -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticGeneratedTheoryTotal
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "S" => SyntacticSyntax.plainTotalCategoricalSyntax T V σ π d

/-- The actual finite-rule algebra for the seven logical schemes,
generalization, modus ponens and the given nonlogical axioms. -/
def proofAlgebra {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    Endofunctor.Algebra ((S).logicalRules axioms).inference :=
  SyntacticDerivation.totalDerivationAlgebra T ((S).logicalRules axioms)

def proofInitial {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    IsInitial (proofAlgebra T V σ π d axioms) :=
  SyntacticDerivation.totalDerivationInitial T ((S).logicalRules axioms)

def conclusion {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    (proofAlgebra T V σ π d axioms).a.left ⟶ (S).algebra.a.2 :=
  (proofAlgebra T V σ π d axioms).a.hom

def formulaTheory {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    Subobject (S).algebra.a.2 := imageSubobject (conclusion T V σ π d axioms)

def sentenceProofObject {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    TotalSplit T := pullback (conclusion T V σ π d axioms) (S).sentenceInclusion

def sentenceConclusion {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    sentenceProofObject T V σ π d axioms ⟶ (S).sentenceObject :=
  pullback.snd (conclusion T V σ π d axioms) (S).sentenceInclusion

def sentenceTheory {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    Subobject (S).sentenceObject := imageSubobject (sentenceConclusion T V σ π d axioms)

/-- Formula closure and leastness use the constructed derivation algebra;
no existence or initiality hypothesis is supplied to this theorem. -/
theorem generated_theory {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    ClosedUnder ((S).logicalRules axioms).inference
        (image.ι (conclusion T V σ π d axioms)) ∧
      (∀ {U : TotalSplit T} (m : U ⟶ (S).algebra.a.2) [Mono m],
        ClosedUnder ((S).logicalRules axioms).inference m →
          ∃ w : image (conclusion T V σ π d axioms) ⟶ U,
            w ≫ m = image.ι (conclusion T V σ π d axioms)) ∧
      (∃ a : (S).logicalParameters ⨿ A ⟶ image (conclusion T V σ π d axioms),
        a ≫ image.ι (conclusion T V σ π d axioms) =
          coprod.desc (S).logicalAxioms (axioms ≫ (S).sentenceInclusion)) ∧
      sentenceTheory T V σ π d axioms =
        (Subobject.pullback (S).sentenceInclusion).obj (formulaTheory T V σ π d axioms) :=
  (S).generated_firstOrder_theory axioms (proofAlgebra T V σ π d axioms)
    (proofInitial T V σ π d axioms)

theorem sentence_theory_pullback {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    sentenceTheory T V σ π d axioms =
      (Subobject.pullback (S).sentenceInclusion).obj (formulaTheory T V σ π d axioms) :=
  (generated_theory T V σ π d axioms).2.2.2

/-- Nonlogical axioms factor through the actual image of the
sentence-conclusion map, rather than merely through the formula image. -/
theorem sentence_axioms_factor {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    ∃ a : A ⟶ image (sentenceConclusion T V σ π d axioms),
      a ≫ image.ι (sentenceConclusion T V σ π d axioms) = axioms := by
  obtain ⟨g, hg⟩ := (generated_theory T V σ π d axioms).2.2.1
  let c := conclusion T V σ π d axioms
  let j := (S).sentenceInclusion
  let u : A ⟶ image c := coprod.inr ≫ g
  have hu : u ≫ image.ι c = axioms ≫ j := by
    rw [Category.assoc, hg, coprod.inr_desc]
  refine ⟨pullback.lift u axioms hu ≫ (sentenceImageIso c j).hom, ?_⟩
  change (pullback.lift u axioms hu ≫ (sentenceImageIso c j).hom) ≫
    image.ι (pullback.snd c j) = axioms
  rw [Category.assoc, sentenceImageIso_hom_ι, pullback.lift_snd]

/-- A sentence subobject is a theory when conclusions of its own finite
proofs factor through it. This is the sentence-theory definition of
Appendix A, with the derivation algebra constructed rather than assumed. -/
def IsSentenceTheory {U : TotalSplit T} (m : U ⟶ (S).sentenceObject) : Prop :=
  ∃ w : sentenceProofObject T V σ π d m ⟶ U,
    w ≫ m = sentenceConclusion T V σ π d m

/-- The sentence image of a generated theory is closed under derivability
from that sentence image itself. -/
theorem sentence_theory_closed {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    IsSentenceTheory T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)) :=
  firstOrder_generated_sentence_closed (S).logicalAxioms (S).sentenceInclusion axioms
    (S).quantifierConstructor (S).implicationConstructor
    (proofAlgebra T V σ π d axioms) (proofInitial T V σ π d axioms)
    (proofAlgebra T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)))
    (proofInitial T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)))

/-- Every sentence theory containing the nonlogical axioms contains
the generated sentence image. -/
theorem sentence_theory_least {A U : TotalSplit T}
    (axioms : A ⟶ (S).sentenceObject) (m : U ⟶ (S).sentenceObject) [Mono m]
    (hm : IsSentenceTheory T V σ π d m) (k : A ⟶ U) (hk : k ≫ m = axioms) :
    sentenceTheory T V σ π d axioms ≤ Subobject.mk m := by
  obtain ⟨w, hw⟩ := hm
  exact firstOrder_generated_sentence_least (S).logicalAxioms (S).sentenceInclusion axioms
    (S).quantifierConstructor (S).implicationConstructor
    (proofAlgebra T V σ π d axioms) (proofInitial T V σ π d axioms) m
    (proofAlgebra T V σ π d m) k hk w hw

/-- Generating from the generated sentence subobject is idempotent. -/
theorem sentence_theory_idempotent {A : TotalSplit T}
    (axioms : A ⟶ (S).sentenceObject) :
    sentenceTheory T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)) =
      sentenceTheory T V σ π d axioms := by
  let m := image.ι (sentenceConclusion T V σ π d axioms)
  obtain ⟨w, hw⟩ := sentence_theory_closed T V σ π d axioms
  obtain ⟨a, ha⟩ := sentence_axioms_factor T V σ π d m
  apply le_antisymm
  · exact imageSubobject_le_mk m (sentenceConclusion T V σ π d m) w hw
  · exact Subobject.mk_le_mk_of_comm a ha

/-- Inclusion of nonlogical axioms induces inclusion of the actual
generated sentence theories. -/
theorem sentence_theory_monotone {A A' : TotalSplit T}
    (axioms : A ⟶ (S).sentenceObject) (axioms' : A' ⟶ (S).sentenceObject)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms) :
    sentenceTheory T V σ π d axioms ≤ sentenceTheory T V σ π d axioms' :=
  firstOrder_sentence_image_monotone (S).logicalAxioms (S).sentenceInclusion axioms axioms'
    (S).quantifierConstructor (S).implicationConstructor k hk
    (proofAlgebra T V σ π d axioms) (proofInitial T V σ π d axioms)
    (proofAlgebra T V σ π d axioms')

/-- The actual sentence-conclusion range splits through its regular
image using the constructed partial inverse of the total image mono. -/
theorem sentence_range_regular_image {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    ∃ r : (S).sentenceObject.obj ⟶ (image (sentenceConclusion T V σ π d axioms)).obj,
      (image.ι (sentenceConclusion T V σ π d axioms)).hom ≫ r = 𝟙 _ ∧
      r ≫ (image.ι (sentenceConclusion T V σ π d axioms)).hom = rst r ∧
      (Ranges.range (sentenceConclusion T V σ π d axioms).hom).hom =
        r ≫ (image.ι (sentenceConclusion T V σ π d axioms)).hom := by
  let c := sentenceConclusion T V σ π d axioms
  obtain ⟨r, hmr, hrm⟩ := totalSplit_mono_partial_inverse T (image.ι c)
  refine ⟨r, hmr, hrm, ?_⟩
  have h := LocalConnectedness.V46.range_regularImage
    (factorThruImage c) (image.ι c) r hmr hrm
  have hfac : (factorThruImage c).hom ≫ (image.ι c).hom = c.hom :=
    congrArg (fun f : sentenceProofObject T V σ π d axioms ⟶ (S).sentenceObject => f.hom)
      (image.fac c)
  simpa only [hfac] using h

/-- The literal source predicate Sent(z) ∧ ∃p G_e(p,z), in the actual
inverse equivalence chart, presents the sentence image. -/
def sentenceSourceCarrier {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) : Carrier :=
  TotalSentenceImages.sentencePredicate T (conclusion T V σ π d axioms) (S).sentenceInclusion

def sentenceSourceIdem {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    Idem (omegaObject T) := predicateIdem T (sentenceSourceCarrier T V σ π d axioms)

def sentenceSourceIso {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    interpretedObject T (sentenceSourceCarrier T V σ π d axioms) ≅
      image (sentenceConclusion T V σ π d axioms) :=
  TotalSentenceImages.sentenceSplittingIso T (conclusion T V σ π d axioms) (S).sentenceInclusion

/-- The representation also gives the sentence subobject, by composing
its actual isomorphism with the actual image inclusion. -/
def sentenceSourceInclusion {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    interpretedObject T (sentenceSourceCarrier T V σ π d axioms) ⟶ (S).sentenceObject :=
  (sentenceSourceIso T V σ π d axioms).hom ≫ image.ι (sentenceConclusion T V σ π d axioms)

instance sentenceSourceInclusion_mono {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    Mono (sentenceSourceInclusion T V σ π d axioms) := by
  dsimp [sentenceSourceInclusion]
  infer_instance

end CategoricalEssentialIncompleteness.V46.SyntacticGeneratedTheoryTotal
