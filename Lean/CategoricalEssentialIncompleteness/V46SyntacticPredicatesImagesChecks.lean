/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesImages

/-! # Explicit predicate comparison statement checks -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates.ImagesChecks

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example {C D : PredicateCategory T} (f : GraphMorphism T C D) :
    StrongEpiMonoFactorisation (representedArrow T f) := f.imageFactorisation

example {C D : PredicateCategory T} (f : GraphMorphism T C D) :
    ImageFactorisation (representedArrow T f) := representedImage T f

example : HasStrongEpiMonoFactorisations (PredicateCategory T) := inferInstance

example {C D : PredicateCategory T} (m : C ⟶ D) [Mono m] :
    ∃ (P : Carrier) (h : T ⊢ inclusionSentence P D) (i : C ≅ (P : PredicateCategory T)),
      i.hom ≫ representedArrow T (GraphMorphism.inclusion h) = m :=
  subobject_is_predicate_inclusion T m

example {X Y : TotalSplit T} (m : X ⟶ Y) [Mono m] :
    ∃ r : Y.obj ⟶ X.obj, m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r :=
  totalSplit_mono_partial_inverse T m

example {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : T ⊢ surjectiveSentence D f.graph) : IsSplitEpi (representedArrow T f) :=
  f.isSplitEpi_of_surjective h

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates.ImagesChecks
