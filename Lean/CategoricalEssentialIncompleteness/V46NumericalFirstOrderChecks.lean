/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalFirstOrder


/-! # Generated numerical first-order theories for arbitrary axiom subobjects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace NumericalFirstOrderChecks
variable {V : NumericalTuples.Object} {σ π : ℕ → NumericalTuples.Object} {d : ℕ}
variable (S : CategoricalSyntax V σ π d)
variable {A : NumericalTuples.Object} (axioms : A ⟶ S.sentenceObject)

example : IsInitial (NumericalFirstOrder.proofAlgebra S axioms) :=
  NumericalFirstOrder.proofInitial S axioms

example : ClosedUnder (S.logicalRules axioms).inference
    (image.ι (NumericalFirstOrder.conclusion S axioms)) :=
  (NumericalFirstOrder.generated_theory S axioms).1

example (T : NumericalTuples.Object) (m : T ⟶ S.algebra.a.2) [Mono m]
    (hm : ClosedUnder (S.logicalRules axioms).inference m) :
    ∃ w : image (NumericalFirstOrder.conclusion S axioms) ⟶ T,
      w ≫ m = image.ι (NumericalFirstOrder.conclusion S axioms) :=
  (NumericalFirstOrder.generated_theory S axioms).2.1 m hm

example : imageSubobject (NumericalFirstOrder.sentenceConclusion S axioms) =
    (Subobject.pullback S.sentenceInclusion).obj
      (imageSubobject (NumericalFirstOrder.conclusion S axioms)) :=
  (NumericalFirstOrder.generated_theory S axioms).2.2.2

end NumericalFirstOrderChecks
