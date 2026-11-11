/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalRealization


/-! # Statement checks in `V46NumericalRealizationChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ) :
    ∃ S : CategoricalSyntax V σ π d,
      ∀ (A : NumericalTuples.Object) (axioms : A ⟶ S.sentenceObject),
        ∃ P : Endofunctor.Algebra (S.logicalRules axioms).inference,
          Nonempty (IsInitial P) ∧ P.a.left.dimension = 1 ∧
            imageSubobject (pullback.snd P.a.hom S.sentenceInclusion) =
              (Subobject.pullback S.sentenceInclusion).obj (imageSubobject P.a.hom) :=
  NumericalRealization.firstOrder_realization V σ π d

example {V : NumericalTuples.Object} {σ π : ℕ → NumericalTuples.Object} {d : ℕ}
    (S : CategoricalSyntax V σ π d) (A : NumericalTuples.Object) (axioms : A ⟶ S.sentenceObject) :
    ClosedUnder (S.logicalRules axioms).inference
      (image.ι (NumericalRealization.conclusion S axioms)) :=
  (NumericalRealization.generated_theory S axioms).1
