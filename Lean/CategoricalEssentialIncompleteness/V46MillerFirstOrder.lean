/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerDerivationTotal
import CategoricalEssentialIncompleteness.V46MillerTotalPartialMaps
import CategoricalEssentialIncompleteness.V46FirstOrderTheory
import CategoricalEssentialIncompleteness.V46SentenceTheoryClosure

/-! # Actual generated first-order theories in the Miller total splitting

The syntax is the constructed parameter-stable named syntax in
Tot(Split(E_z)). The actual seven logical schemes and the ordered unary
and binary inference rules are instantiated with every supplied axiom
subobject. Initiality is supplied by the constructed arbitrary-rule
algebra, not by an additional assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.FirstOrder
variable (z : Point) (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ)
local notation "S" => Syntax.canonicalCategoricalSyntax z V σ π d

/-- Exactly the seven-scheme nullary data, generalization and ordered MP. -/
abbrev rules {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    RulePresentation (S).algebra.a.2 2 := (S).logicalRules axioms

/-- The actual finite-rule algebra for the seven logical schemes,
generalization, modus ponens and the given nonlogical axioms. -/
def proofAlgebra {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Endofunctor.Algebra ((S).logicalRules axioms).inference :=
  Derivation.Canonical.derivationAlgebra z ((S).logicalRules axioms)

def proofInitial {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    IsInitial (proofAlgebra z V σ π d axioms) :=
  Derivation.Canonical.derivationInitial z ((S).logicalRules axioms)

def conclusion {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    (proofAlgebra z V σ π d axioms).a.left ⟶ (S).algebra.a.2 :=
  (proofAlgebra z V σ π d axioms).a.hom

def formulaTheory {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Subobject (S).algebra.a.2 := imageSubobject (conclusion z V σ π d axioms)

def sentenceProofObject {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Total.CanonicalTotal z := pullback (conclusion z V σ π d axioms) (S).sentenceInclusion

def sentenceConclusion {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    sentenceProofObject z V σ π d axioms ⟶ (S).sentenceObject :=
  pullback.snd (conclusion z V σ π d axioms) (S).sentenceInclusion

def sentenceTheory {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Subobject (S).sentenceObject := imageSubobject (sentenceConclusion z V σ π d axioms)

theorem sentence_isPullback {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    IsPullback (pullback.fst (conclusion z V σ π d axioms) (S).sentenceInclusion)
      (sentenceConclusion z V σ π d axioms) (conclusion z V σ π d axioms) (S).sentenceInclusion :=
  IsPullback.of_hasPullback _ _

def proofFold {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject)
    (B : Endofunctor.Algebra (rules z V σ π d axioms).inference) :
    proofAlgebra z V σ π d axioms ⟶ B := (proofInitial z V σ π d axioms).to B

theorem proofFold_conclusion {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject)
    (B : Endofunctor.Algebra (rules z V σ π d axioms).inference) :
    (proofFold z V σ π d axioms B).f.left ≫ B.a.hom=conclusion z V σ π d axioms := Over.w _

theorem proofFold_constructor {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject)
    (B : Endofunctor.Algebra (rules z V σ π d axioms).inference) :
    (proofAlgebra z V σ π d axioms).str ≫ (proofFold z V σ π d axioms B).f=
      (rules z V σ π d axioms).inference.map (proofFold z V σ π d axioms B).f ≫ B.str :=
  (proofFold z V σ π d axioms B).h.symm

theorem proofFold_unique {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject)
    (B : Endofunctor.Algebra (rules z V σ π d axioms).inference)
    (f : proofAlgebra z V σ π d axioms ⟶ B) : f=proofFold z V σ π d axioms B :=
  (proofInitial z V σ π d axioms).hom_ext _ _

/-- Formula closure and leastness use the constructed derivation algebra;
no existence or initiality hypothesis is supplied to this theorem. -/
theorem generated_theory {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    ClosedUnder ((S).logicalRules axioms).inference
        (image.ι (conclusion z V σ π d axioms)) ∧
      (∀ {U : Total.CanonicalTotal z} (m : U ⟶ (S).algebra.a.2) [Mono m],
        ClosedUnder ((S).logicalRules axioms).inference m →
          ∃ w : image (conclusion z V σ π d axioms) ⟶ U,
            w ≫ m = image.ι (conclusion z V σ π d axioms)) ∧
      (∃ a : (S).logicalParameters ⨿ A ⟶ image (conclusion z V σ π d axioms),
        a ≫ image.ι (conclusion z V σ π d axioms) =
          coprod.desc (S).logicalAxioms (axioms ≫ (S).sentenceInclusion)) ∧
      sentenceTheory z V σ π d axioms =
        (Subobject.pullback (S).sentenceInclusion).obj (formulaTheory z V σ π d axioms) :=
  (S).generated_firstOrder_theory axioms (proofAlgebra z V σ π d axioms)
    (proofInitial z V σ π d axioms)

theorem sentence_theory_pullback {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    sentenceTheory z V σ π d axioms =
      (Subobject.pullback (S).sentenceInclusion).obj (formulaTheory z V σ π d axioms) :=
  (generated_theory z V σ π d axioms).2.2.2

/-- Nonlogical axioms factor through the actual image of the
sentence-conclusion map, rather than merely through the formula image. -/
theorem sentence_axioms_factor {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    ∃ a : A ⟶ image (sentenceConclusion z V σ π d axioms),
      a ≫ image.ι (sentenceConclusion z V σ π d axioms) = axioms := by
  obtain ⟨g, hg⟩ := (generated_theory z V σ π d axioms).2.2.1
  let c := conclusion z V σ π d axioms
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
def IsSentenceTheory {U : Total.CanonicalTotal z} (m : U ⟶ (S).sentenceObject) : Prop :=
  ∃ w : sentenceProofObject z V σ π d m ⟶ U,
    w ≫ m = sentenceConclusion z V σ π d m

/-- The sentence image of a generated theory is closed under derivability
from that sentence image itself. -/
theorem sentence_theory_closed {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    IsSentenceTheory z V σ π d (image.ι (sentenceConclusion z V σ π d axioms)) :=
  firstOrder_generated_sentence_closed (S).logicalAxioms (S).sentenceInclusion axioms
    (S).quantifierConstructor (S).implicationConstructor
    (proofAlgebra z V σ π d axioms) (proofInitial z V σ π d axioms)
    (proofAlgebra z V σ π d (image.ι (sentenceConclusion z V σ π d axioms)))
    (proofInitial z V σ π d (image.ι (sentenceConclusion z V σ π d axioms)))

/-- Every sentence theory containing the nonlogical axioms contains
the generated sentence image. -/
theorem sentence_theory_least {A U : Total.CanonicalTotal z}
    (axioms : A ⟶ (S).sentenceObject) (m : U ⟶ (S).sentenceObject) [Mono m]
    (hm : IsSentenceTheory z V σ π d m) (k : A ⟶ U) (hk : k ≫ m = axioms) :
    sentenceTheory z V σ π d axioms ≤ Subobject.mk m := by
  obtain ⟨w, hw⟩ := hm
  exact firstOrder_generated_sentence_least (S).logicalAxioms (S).sentenceInclusion axioms
    (S).quantifierConstructor (S).implicationConstructor
    (proofAlgebra z V σ π d axioms) (proofInitial z V σ π d axioms) m
    (proofAlgebra z V σ π d m) k hk w hw

/-- Generating from the generated sentence subobject is idempotent. -/
theorem sentence_theory_idempotent {A : Total.CanonicalTotal z}
    (axioms : A ⟶ (S).sentenceObject) :
    sentenceTheory z V σ π d (image.ι (sentenceConclusion z V σ π d axioms)) =
      sentenceTheory z V σ π d axioms := by
  let m := image.ι (sentenceConclusion z V σ π d axioms)
  obtain ⟨w, hw⟩ := sentence_theory_closed z V σ π d axioms
  obtain ⟨a, ha⟩ := sentence_axioms_factor z V σ π d m
  apply le_antisymm
  · exact imageSubobject_le_mk m (sentenceConclusion z V σ π d m) w hw
  · exact Subobject.mk_le_mk_of_comm a ha

/-- Inclusion of nonlogical axioms induces inclusion of the actual
generated sentence theories. -/
theorem sentence_theory_monotone {A A' : Total.CanonicalTotal z}
    (axioms : A ⟶ (S).sentenceObject) (axioms' : A' ⟶ (S).sentenceObject)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms) :
    sentenceTheory z V σ π d axioms ≤ sentenceTheory z V σ π d axioms' :=
  firstOrder_sentence_image_monotone (S).logicalAxioms (S).sentenceInclusion axioms axioms'
    (S).quantifierConstructor (S).implicationConstructor k hk
    (proofAlgebra z V σ π d axioms) (proofInitial z V σ π d axioms)
    (proofAlgebra z V σ π d axioms')

/-- The actual sentence-conclusion range splits through its regular
image using the constructed partial inverse of the total image mono. -/
theorem sentence_range_regular_image {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    ∃ r : (S).sentenceObject.obj ⟶ (image (sentenceConclusion z V σ π d axioms)).obj,
      (image.ι (sentenceConclusion z V σ π d axioms)).hom ≫ r = 𝟙 _ ∧
      r ≫ (image.ι (sentenceConclusion z V σ π d axioms)).hom = rst r ∧
      (Ranges.range (sentenceConclusion z V σ π d axioms).hom).hom =
        r ≫ (image.ι (sentenceConclusion z V σ π d axioms)).hom := by
  let c := sentenceConclusion z V σ π d axioms
  obtain ⟨r, hmr, hrm⟩ := Total.mono_has_partial_inverse z (image.ι c)
  refine ⟨r, hmr, hrm, ?_⟩
  have h := LocalConnectedness.V46.range_regularImage
    (factorThruImage c) (image.ι c) r hmr hrm
  have hfac : (factorThruImage c).hom ≫ (image.ι c).hom = c.hom :=
    congrArg (fun f : sentenceProofObject z V σ π d axioms ⟶ (S).sentenceObject => f.hom)
      (image.fac c)
  simpa only [hfac] using h

/-- The representing restriction idempotent lies on the actual formula
object of the total splitting, not on an unrelated numerical carrier. -/
def formulaIdem {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Idem (S).algebra.a.2.obj := Ranges.range (conclusion z V σ π d axioms).hom

def sentenceIdem {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    Idem (S).sentenceObject.obj := Ranges.range (sentenceConclusion z V σ π d axioms).hom

theorem formula_range_regular_image {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    ∃ r : (S).algebra.a.2.obj ⟶ (image (conclusion z V σ π d axioms)).obj,
      (image.ι (conclusion z V σ π d axioms)).hom ≫ r=𝟙 _ ∧
      r ≫ (image.ι (conclusion z V σ π d axioms)).hom=rst r ∧
      (formulaIdem z V σ π d axioms).hom=r ≫ (image.ι (conclusion z V σ π d axioms)).hom := by
  let c := conclusion z V σ π d axioms
  obtain ⟨r,hmr,hrm⟩ := Total.mono_has_partial_inverse z (image.ι c)
  refine ⟨r,hmr,hrm,?_⟩
  have h := LocalConnectedness.V46.range_regularImage (factorThruImage c) (image.ι c) r hmr hrm
  have hfac : (factorThruImage c).hom ≫ (image.ι c).hom=c.hom :=
    congrArg (fun f : (proofAlgebra z V σ π d axioms).a.left ⟶ (S).algebra.a.2 => f.hom) (image.fac c)
  rw [hfac] at h
  exact h

theorem sentence_idempotent_represents {A : Total.CanonicalTotal z} (axioms : A ⟶ (S).sentenceObject) :
    ∃ r : (S).sentenceObject.obj ⟶ (image (sentenceConclusion z V σ π d axioms)).obj,
      (image.ι (sentenceConclusion z V σ π d axioms)).hom ≫ r=𝟙 _ ∧
      r ≫ (image.ι (sentenceConclusion z V σ π d axioms)).hom=rst r ∧
      (sentenceIdem z V σ π d axioms).hom=r ≫ (image.ι (sentenceConclusion z V σ π d axioms)).hom :=
  sentence_range_regular_image z V σ π d axioms

/-- The construction is defined on every actual sentence axiom subobject. -/
def generatedSentence (A : Subobject (S).sentenceObject) : Subobject (S).sentenceObject :=
  sentenceTheory z V σ π d A.arrow

theorem axioms_le_generated (A : Subobject (S).sentenceObject) :
    A≤generatedSentence z V σ π d A := by
  obtain ⟨a,ha⟩ := sentence_axioms_factor z V σ π d A.arrow
  simpa only [Subobject.mk_arrow,generatedSentence,sentenceTheory] using Subobject.mk_le_mk_of_comm a ha

theorem generatedSentence_closed (A : Subobject (S).sentenceObject) :
    IsSentenceTheory z V σ π d (generatedSentence z V σ π d A).arrow := by
  let c := sentenceConclusion z V σ π d A.arrow
  let m := (generatedSentence z V σ π d A).arrow
  have hi : (imageSubobjectIso c).hom ≫ image.ι c=m := imageSubobject_arrow c
  have hle := sentence_theory_monotone z V σ π d m (image.ι c) (imageSubobjectIso c).hom hi
  rw [sentence_theory_idempotent] at hle
  have hm : sentenceTheory z V σ π d m≤Subobject.mk m := by
    simpa only [m,Subobject.mk_arrow,generatedSentence] using hle
  let c' := sentenceConclusion z V σ π d m
  let e := Subobject.ofMkLEMk (image.ι c') m hm
  refine ⟨factorThruImage c' ≫ e,?_⟩
  rw [Category.assoc,Subobject.ofMkLEMk_comp,image.fac]

theorem generatedSentence_least (A B : Subobject (S).sentenceObject)
    (hB : IsSentenceTheory z V σ π d B.arrow) (hAB : A≤B) :
    generatedSentence z V σ π d A≤B := by
  have h := sentence_theory_least z V σ π d A.arrow B.arrow hB
    (Subobject.ofLE A B hAB) (Subobject.ofLE_arrow hAB)
  simpa only [Subobject.mk_arrow,generatedSentence] using h

theorem generatedSentence_idempotent (A : Subobject (S).sentenceObject) :
    generatedSentence z V σ π d (generatedSentence z V σ π d A)=generatedSentence z V σ π d A :=
  le_antisymm
    (generatedSentence_least z V σ π d _ _ (generatedSentence_closed z V σ π d A) le_rfl)
    (axioms_le_generated z V σ π d (generatedSentence z V σ π d A))

theorem generatedSentence_monotone : Monotone (generatedSentence z V σ π d) := by
  intro A B hAB
  exact sentence_theory_monotone z V σ π d A.arrow B.arrow
    (Subobject.ofLE A B hAB) (Subobject.ofLE_arrow hAB)

end CategoricalEssentialIncompleteness.V46.Miller.FirstOrder
