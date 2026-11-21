/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderTheory

/-! Theorem A.6 uses the scheme morphisms, not an unspecified logical map. -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
    {A : D} (axioms : A ⟶ S.sentenceObject)
    (P : Endofunctor.Algebra (S.logicalRules axioms).inference) (hP : IsInitial P) :
    ClosedUnder (S.logicalRules axioms).inference (image.ι P.a.hom) ∧
      (∀ {T : D} (m : T ⟶ S.algebra.a.2) [Mono m],
        ClosedUnder (S.logicalRules axioms).inference m →
          ∃ w : image P.a.hom ⟶ T, w ≫ m = image.ι P.a.hom) ∧
      (∃ a : S.logicalParameters ⨿ A ⟶ image P.a.hom,
        a ≫ image.ι P.a.hom = coprod.desc S.logicalAxioms
          (axioms ≫ S.sentenceInclusion)) ∧
      imageSubobject (pullback.snd P.a.hom S.sentenceInclusion) =
        (Subobject.pullback S.sentenceInclusion).obj (imageSubobject P.a.hom) :=
  S.generated_firstOrder_theory axioms P hP
