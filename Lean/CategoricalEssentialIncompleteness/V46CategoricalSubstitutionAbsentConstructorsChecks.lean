/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentConstructors

/-! Every arity and coefficient carrier participates in the invariant. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P V T Z U Y : D} (A : Over P × Over P)
variable (L : StableListAlgebra V) (E : DecidableVariables V) (name : P ⟶ V)
variable (FVargs : (T,Z) ⟶ (L.algebra.carrier,L.algebra.carrier))
variable (FVout : U ⟶ L.algebra.carrier) (embed : U ⟶ Y)
variable (f g : A ⟶ (constantFamily P T,constantFamily P Z))
variable (good : ∀ {X : D} (k : X ⟶ A.1.left),
  prod.lift (k ≫ A.1.hom ≫ name) (k ≫ f.1.left ≫ prod.snd ≫ FVargs.1) ≫ L.membership E =
    Two.constant X false → k ≫ g.1.left ≫ prod.snd = k ≫ f.1.left ≫ prod.snd)

example (σ : ℕ → D) (n : ℕ) (h : (SyntaxPolynomial.constructors σ n).eval.obj (T,Z) ⟶ U)
    (hFV : h ≫ FVout = (SyntaxPolynomial.constructors σ n).eval.map FVargs ≫
      L.constructorOccurrences σ n) :
    AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors σ n) h embed ≫
        AbsentFamilies.mask L E name FVout embed =
      AbsentConstructors.pairConstructor A f g (SyntaxPolynomial.constructors σ n) h embed ≫
        AbsentFamilies.result :=
  AbsentConstructors.constructors_invariant A L E name FVargs FVout embed f g good σ n h hFV
