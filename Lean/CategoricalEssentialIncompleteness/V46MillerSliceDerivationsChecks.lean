/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerSliceDerivations

/-! # Independent Miller slice-initiality and uniqueness statements -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46 Miller

section Uniform
variable {Ω : Uniform.Family} {P : Total.TotalCategory Ω}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- The coefficient family and target operations are uniform morphisms,
without supplying an ordinary recursive extension or a chosen representation. -/
example : IsInitial (Derivation.Parameterized.uniformAlgebra R) :=
  Derivation.Parameterized.uniformInitial R

example (B : Endofunctor.Algebra R.inference) :
    ∃! _f : Derivation.Parameterized.uniformAlgebra R ⟶ B, True := by
  exact ⟨(Derivation.Parameterized.uniformInitial R).to B, trivial,
    fun f _ => (Derivation.Parameterized.uniformInitial R).hom_ext f _⟩
end Uniform

section Canonical
variable (z : Point) {P : Total.CanonicalTotal z}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

example : IsInitial (Derivation.Parameterized.algebra z R) :=
  Derivation.Parameterized.initial z R

example (B : Endofunctor.Algebra R.inference) :
    (Derivation.Parameterized.fold z R B).f.left ≫ B.a.hom =
      (Derivation.Parameterized.algebra z R).a.hom :=
  Derivation.Parameterized.fold_conclusion z R B

example (B : Endofunctor.Algebra R.inference) :
    (Derivation.Parameterized.algebra z R).str ≫ (Derivation.Parameterized.fold z R B).f =
      R.inference.map (Derivation.Parameterized.fold z R B).f ≫ B.str :=
  Derivation.Parameterized.fold_constructor z R B

example (B : Endofunctor.Algebra R.inference)
    (f : (Derivation.Parameterized.algebra z R).a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom = (Derivation.Parameterized.algebra z R).a.hom)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str =
      (Derivation.Parameterized.algebra z R).str ≫ Over.homMk f hf) :
    f = (Derivation.Parameterized.fold z R B).f.left :=
  Derivation.Parameterized.fold_underlying_unique z R B f hf hc
end Canonical

#print axioms Derivation.Parameterized.uniformAlgebra
#print axioms Derivation.Parameterized.uniformInitial
#print axioms Derivation.Parameterized.algebra
#print axioms Derivation.Parameterized.initial
#print axioms Derivation.Parameterized.fold_conclusion
#print axioms Derivation.Parameterized.fold_constructor
#print axioms Derivation.Parameterized.fold_underlying_unique
