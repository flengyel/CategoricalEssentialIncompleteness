/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TranslationGalois

/-! # Statement checks for Theorem 4.5 -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {P Q R : FirstOrderPresentation V}

example (σ : Translation P Q) (T : Q.Theories) :
    FirstOrderReflection.generated P.proofs ((Subobject.pullback σ.sentence).obj T.val) =
      (Subobject.pullback σ.sentence).obj T.val := σ.inverse_closed T

example (σ : Translation P Q) : σ.pushforward ⊣ σ.inverseImage := σ.adjunction

example (σ : Translation P Q) (T : P.Theories) (U : Q.Theories) :
    (σ.pushforward.obj T).val ≤ U.val ↔ T.val ≤ (σ.inverseImage.obj U).val :=
  σ.pushforward_le_iff T U

example (σ : Translation P Q) :
    Subobject.«exists» σ.sentence ⋙ FirstOrderReflection.generation Q.proofs Q.initial =
      FirstOrderReflection.generation P.proofs P.initial ⋙ σ.pushforward :=
  σ.generation_functor_identity

example (σ : Translation P Q) (τ : Translation Q R) :
    (σ.comp τ).pushforward = σ.pushforward ⋙ τ.pushforward := σ.pushforward_comp τ

example (σ : Translation P Q) (τ : Translation Q R) :
    (σ.comp τ).inverseImage = τ.inverseImage ⋙ σ.inverseImage := σ.inverseImage_comp τ

example (P : FirstOrderPresentation V) : (Translation.id P).pushforward = 𝟭 P.Theories :=
  Translation.pushforward_id P

example (P : FirstOrderPresentation V) : (Translation.id P).inverseImage = 𝟭 P.Theories :=
  Translation.inverseImage_id P

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.map_generated_le
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.inverse_closed
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.generation_functor_identity
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.pushforward_comp
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.inverseImage_comp
