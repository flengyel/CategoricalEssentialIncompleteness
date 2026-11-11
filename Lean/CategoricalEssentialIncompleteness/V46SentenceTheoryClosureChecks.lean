/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SentenceTheoryClosure

/-! # Closure and leastness of generated sentence theories -/

@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S A : D}

example (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P)
    (P' : Endofunctor.Algebra
      (firstOrderRules logical sentence (image.ι (pullback.snd P.a.hom sentence))
        all imp).inference) (hP' : IsInitial P') :
    ∃ w : pullback P'.a.hom sentence ⟶ image (pullback.snd P.a.hom sentence),
      w ≫ image.ι (pullback.snd P.a.hom sentence) = pullback.snd P'.a.hom sentence :=
  firstOrder_generated_sentence_closed logical sentence axioms all imp P hP P' hP'

example (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P) {U : D} (m : U ⟶ S) [Mono m]
    (P' : Endofunctor.Algebra (firstOrderRules logical sentence m all imp).inference)
    (k : A ⟶ U) (hk : k ≫ m = axioms)
    (w : pullback P'.a.hom sentence ⟶ U)
    (hw : w ≫ m = pullback.snd P'.a.hom sentence) :
    imageSubobject (pullback.snd P.a.hom sentence) ≤ Subobject.mk m :=
  firstOrder_generated_sentence_least logical sentence axioms all imp P hP m P' k hk w hw
