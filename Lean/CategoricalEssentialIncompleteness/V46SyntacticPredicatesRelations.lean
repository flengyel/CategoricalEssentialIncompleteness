/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesImages

/-! # All-model semantics of provably total predicate graphs -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedNearProduct
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- All-model semantics of a quotient graph, through its realized program. -/
def relation {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) : Prop :=
  SyntacticModel.programRelation T M ((realization T).map f).hom.hom.val x y

@[simp] theorem relation_class {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    relation T (representedArrow T f) M x y ↔ f.graph.val.Evalb ![x, y] :=
  f.programClass_model M x y

@[simp] theorem relation_comp {A B C : PredicateCategory T} (f : A ⟶ B) (g : B ⟶ C)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x z : M) :
    relation T (f ≫ g) M x z ↔ ∃ y, relation T f M x y ∧ relation T g M y z := by
  unfold relation
  rw [Functor.map_comp]
  exact SyntacticModel.programRelation_mul T M _ _ x z

@[simp] theorem relation_id (C : PredicateCategory T)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    relation T (𝟙 C) M x y ↔ C.val.Evalb ![x] ∧ y = x := by
  exact (relation_class T (GraphMorphism.identity T C) M x y).trans
    (GraphMorphism.identityGraph_eval C x y)

theorem relation_support {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M)
    (h : relation T f M x y) : C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  exact g.support_model M x y ((relation_class T g M x y).mp h)

theorem relation_total {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) (hx : C.val.Evalb ![x]) :
    ∃! y, relation T f M x y := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  change ∃! y, relation T (representedArrow T g) M x y
  simpa only [relation_class] using g.total_model M x hx

theorem relation_functional {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y z : M)
    (hy : relation T f M x y) (hz : relation T f M x z) : y = z :=
  SyntacticModel.programRelation_functional T M _ x y z hy hz

theorem hom_ext {C D : PredicateCategory T} (f g : C ⟶ D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M),
      relation T f M x y ↔ relation T g M x y) : f = g := by
  apply (realization T).map_injective
  apply WideSubcategory.hom_ext
  apply SplitObject.Hom.ext
  apply CodedHom.ext
  exact programClass_ext T _ _ h

def chosenGraph {C D : PredicateCategory T} (f : C ⟶ D) : GraphMorphism T C D :=
  Quotient.out f

@[simp] theorem chosenGraph_class {C D : PredicateCategory T} (f : C ⟶ D) :
    representedArrow T (chosenGraph T f) = f := Quotient.out_eq f

@[simp] theorem chosenGraph_eval {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    (chosenGraph T f).graph.val.Evalb ![x, y] ↔ relation T f M x y := by
  rw [← relation_class T, chosenGraph_class]

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates
