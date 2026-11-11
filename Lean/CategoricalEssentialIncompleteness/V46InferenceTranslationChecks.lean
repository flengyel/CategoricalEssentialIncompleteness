/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # Statement checks for translations of finite derivations -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.RulePresentation

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {F G H : D} {N : ℕ}
variable {R : RulePresentation F N} {R' : RulePresentation G N}
variable {R'' : RulePresentation H N}
variable (τ : Translation R R') (σ : Translation R' R'')
variable (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
variable (Q : Endofunctor.Algebra R'.inference) (hQ : IsInitial Q)
variable (Q' : Endofunctor.Algebra R''.inference)

example {B : D} (m : B ⟶ G) (hm : ClosedUnder R'.inference m) :
    ClosedUnder R.inference (pullback.snd m τ.formula) := τ.closed_pullback m hm

example : τ.fold P hP Q ≫ Q.a.hom = P.a.hom ≫ τ.formula :=
  τ.fold_conclusion P hP Q

example : P.str.left ≫ τ.fold P hP Q =
    Limits.Sigma.map (τ.mapRule (τ.fold P hP Q) (τ.fold_conclusion P hP Q)) ≫
      Q.str.left := τ.fold_constructor P hP Q

example (f : P.a.left ⟶ Q.a.left) (hf : f ≫ Q.a.hom = P.a.hom ≫ τ.formula)
    (hc : P.str.left ≫ f = Limits.Sigma.map (τ.mapRule f hf) ≫ Q.str.left) :
    f = τ.fold P hP Q := τ.fold_unique P hP Q f hf hc

example : (τ.comp σ).fold P hP Q' = τ.fold P hP Q ≫ σ.fold Q hQ Q' :=
  τ.fold_comp σ P hP Q hQ Q'

example : (Translation.id R).fold P hP P = 𝟙 P.a.left :=
  Translation.fold_id P hP

example {S S' : D} (sentence : S ⟶ F) (sentence' : S' ⟶ G)
    (s : S ⟶ S') (hs : sentence ≫ τ.formula = s ≫ sentence') :
    imageSubobject (pullback.snd P.a.hom sentence ≫ s) ≤
      imageSubobject (pullback.snd Q.a.hom sentence') :=
  τ.sentenceImage_le sentence sentence' s hs P hP Q

#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.reindexAlgebra
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.closed_pullback
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.fold_conclusion
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.fold_constructor
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.fold_unique
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.fold_comp
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.fold_id
#print axioms CategoricalEssentialIncompleteness.V46.RulePresentation.Translation.sentenceImage_le
