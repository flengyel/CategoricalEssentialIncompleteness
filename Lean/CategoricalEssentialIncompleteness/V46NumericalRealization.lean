/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSyntax
public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation
public import CategoricalEssentialIncompleteness.V46FirstOrderTheory

/-! # Numerical logical realization on finite derivation-word carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalRealization
variable {V : NumericalTuples.Object} {σ π : ℕ → NumericalTuples.Object} {d : ℕ}
variable (S : CategoricalSyntax V σ π d)
variable {A : NumericalTuples.Object} (axioms : A ⟶ S.sentenceObject)

/-- The carrier consists of original finite rule-labelled words, with
membership and computation witnesses kept existential. -/
def proofAlgebra : Endofunctor.Algebra (S.logicalRules axioms).inference :=
  NumericalDerivation.codeAlgebra (S.logicalRules axioms)

def proofInitial : IsInitial (proofAlgebra S axioms) :=
  NumericalDerivation.codeInitial (S.logicalRules axioms)

theorem proof_dimension : (proofAlgebra S axioms).a.left.dimension = 1 := rfl

def conclusion : (proofAlgebra S axioms).a.left ⟶ S.algebra.a.2 :=
  (proofAlgebra S axioms).a.hom

def sentenceProof : NumericalTuples.Object := pullback (conclusion S axioms) S.sentenceInclusion

def sentenceConclusion : sentenceProof S axioms ⟶ S.sentenceObject := pullback.snd _ _

theorem generated_theory :
    ClosedUnder (S.logicalRules axioms).inference (image.ι (conclusion S axioms)) ∧
      (∀ {T : NumericalTuples.Object} (m : T ⟶ S.algebra.a.2) [Mono m],
        ClosedUnder (S.logicalRules axioms).inference m →
          ∃ w : image (conclusion S axioms) ⟶ T, w ≫ m = image.ι (conclusion S axioms)) ∧
      (∃ a : S.logicalParameters ⨿ A ⟶ image (conclusion S axioms),
        a ≫ image.ι (conclusion S axioms) = coprod.desc S.logicalAxioms
          (axioms ≫ S.sentenceInclusion)) ∧
      imageSubobject (sentenceConclusion S axioms) =
        (Subobject.pullback S.sentenceInclusion).obj (imageSubobject (conclusion S axioms)) :=
  S.generated_firstOrder_theory axioms (proofAlgebra S axioms) (proofInitial S axioms)

/-- The syntax and every axiom instance are constructed. No universal
property or proof-presentation premise is supplied to this theorem. -/
theorem firstOrder_realization (V : NumericalTuples.Object)
    (σ π : ℕ → NumericalTuples.Object) (d : ℕ) :
    ∃ S : CategoricalSyntax V σ π d,
      ∀ (A : NumericalTuples.Object) (axioms : A ⟶ S.sentenceObject),
        ∃ P : Endofunctor.Algebra (S.logicalRules axioms).inference,
          Nonempty (IsInitial P) ∧ P.a.left.dimension = 1 ∧
            imageSubobject (pullback.snd P.a.hom S.sentenceInclusion) =
              (Subobject.pullback S.sentenceInclusion).obj (imageSubobject P.a.hom) := by
  refine ⟨NumericalNamed.literalCategoricalSyntax V σ π d, ?_⟩
  intro A axioms
  exact ⟨proofAlgebra _ axioms, ⟨proofInitial _ axioms⟩, proof_dimension _ axioms,
    (generated_theory _ axioms).2.2.2⟩

end CategoricalEssentialIncompleteness.V46.NumericalRealization
