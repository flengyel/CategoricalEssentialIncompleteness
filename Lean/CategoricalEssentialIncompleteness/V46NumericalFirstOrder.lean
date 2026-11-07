/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalSyntax
import CategoricalEssentialIncompleteness.V46NumericalDerivation
import CategoricalEssentialIncompleteness.V46FirstOrderTheory

/-! # Generated numerical first-order theories for arbitrary axiom subobjects -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalFirstOrder
variable {V : NumericalTuples.Object} {σ π : ℕ → NumericalTuples.Object} {d : ℕ}
variable (S : CategoricalSyntax V σ π d)
variable {A : NumericalTuples.Object} (axioms : A ⟶ S.sentenceObject)

/-- The seven schemes, generalization and ordered modus ponens are the
constructed logical rules, with the given axiom object as nullary labels. -/
def proofAlgebra : Endofunctor.Algebra (S.logicalRules axioms).inference :=
  NumericalDerivation.derivationAlgebra (S.logicalRules axioms)

def proofInitial : IsInitial (proofAlgebra S axioms) :=
  NumericalDerivation.derivationInitial (S.logicalRules axioms)

def conclusion : (proofAlgebra S axioms).a.left ⟶ S.algebra.a.2 :=
  (proofAlgebra S axioms).a.hom

def sentenceProof : NumericalTuples.Object :=
  pullback (conclusion S axioms) S.sentenceInclusion

def sentenceConclusion : sentenceProof S axioms ⟶ S.sentenceObject :=
  pullback.snd _ _

theorem sentence_isPullback :
    IsPullback (pullback.fst (conclusion S axioms) S.sentenceInclusion)
      (sentenceConclusion S axioms) (conclusion S axioms) S.sentenceInclusion :=
  IsPullback.of_hasPullback _ _

/-- No decidability of the axiom carrier or initiality premise is required. -/
theorem generated_theory :
    ClosedUnder (S.logicalRules axioms).inference
      (image.ι (conclusion S axioms)) ∧
      (∀ {T : NumericalTuples.Object} (m : T ⟶ S.algebra.a.2) [Mono m],
        ClosedUnder (S.logicalRules axioms).inference m →
          ∃ w : image (conclusion S axioms) ⟶ T,
            w ≫ m = image.ι (conclusion S axioms)) ∧
      (∃ a : S.logicalParameters ⨿ A ⟶ image (conclusion S axioms),
        a ≫ image.ι (conclusion S axioms) = coprod.desc S.logicalAxioms
          (axioms ≫ S.sentenceInclusion)) ∧
      imageSubobject (sentenceConclusion S axioms) =
        (Subobject.pullback S.sentenceInclusion).obj
          (imageSubobject (conclusion S axioms)) :=
  S.generated_firstOrder_theory axioms (proofAlgebra S axioms)
    (proofInitial S axioms)

end CategoricalEssentialIncompleteness.V46.NumericalFirstOrder
