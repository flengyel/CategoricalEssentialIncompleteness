/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceInference
public import CategoricalEssentialIncompleteness.V46MillerDerivationInitial
public import CategoricalEssentialIncompleteness.V46MillerDerivationTotal

/-! # Initial finite derivations in every Miller parameter slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.Parameterized

section Uniform
variable {Ω : Uniform.Family} {P : Total.TotalCategory Ω}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- All coefficients are arbitrary uniform families. The complete rule
comparison retains the parameter, rule label and ordered child conclusions. -/
def uniformAlgebra : Endofunctor.Algebra R.inference :=
  SliceInference.algebra R (Derivation.derivationAlgebra (SliceRuleObjects.rules R))

def uniformInitial : IsInitial (uniformAlgebra R) :=
  SliceInference.initial R _ (Derivation.derivationInitial (SliceRuleObjects.rules R))

end Uniform

variable (z : Point) {P : Total.CanonicalTotal z}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- This algebra lies over an arbitrary formula family in the Tot(Split(E_z)); neither the
family nor the target algebra is assumed constant. -/
def algebra : Endofunctor.Algebra R.inference :=
  SliceInference.algebra R (Canonical.derivationAlgebra z (SliceRuleObjects.rules R))

def initial : IsInitial (algebra z R) :=
  SliceInference.initial R _ (Canonical.derivationInitial z (SliceRuleObjects.rules R))

def fold (B : Endofunctor.Algebra R.inference) : algebra z R ⟶ B := (initial z R).to B

theorem fold_conclusion (B : Endofunctor.Algebra R.inference) :
    (fold z R B).f.left ≫ B.a.hom = (algebra z R).a.hom := Over.w _

theorem fold_constructor (B : Endofunctor.Algebra R.inference) :
    (algebra z R).str ≫ (fold z R B).f = R.inference.map (fold z R B).f ≫ B.str :=
  (fold z R B).h.symm

theorem fold_unique (B : Endofunctor.Algebra R.inference) (f : algebra z R ⟶ B) :
    f = fold z R B := (initial z R).hom_ext _ _

/-- Uniqueness holds for every underlying morphism with the original
parameter, conclusion and constructor equations. -/
theorem fold_underlying_unique (B : Endofunctor.Algebra R.inference)
    (f : (algebra z R).a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom = (algebra z R).a.hom)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str =
      (algebra z R).str ≫ Over.homMk f hf) : f = (fold z R B).f.left :=
  congrArg (fun h : algebra z R ⟶ B => h.f.left)
    ((initial z R).hom_ext (⟨Over.homMk f hf, hc⟩ : algebra z R ⟶ B) (fold z R B))

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.Parameterized
