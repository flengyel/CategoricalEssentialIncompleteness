/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicates

/-! # Interpretation of predicate graphs in arbitrary arithmetic models -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

/-- Every element of the whole arithmetic model satisfying the carrier
predicate belongs to its interpretation. -/
abbrev Obj (M : Type) [ORingStructure M] (C : Carrier) : Type :=
  {x : M // C.val.Evalb ![x]}

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

omit [𝗣𝗔 ⪯ T] in
/-- Provable unique totality supplies the value, and support places it
in the target carrier. -/
def value {C D : Carrier} (f : GraphMorphism T C D) (x : Obj M C) : Obj M D :=
  ⟨Classical.choose (f.total_model M x.val x.property),
    (f.support_model M x.val _ (Classical.choose_spec
      (f.total_model M x.val x.property)).1).2⟩

omit [𝗣𝗔 ⪯ T] in
theorem value_graph {C D : Carrier} (f : GraphMorphism T C D) (x : Obj M C) :
    f.graph.val.Evalb ![x.val, (value T M f x).val] :=
  (Classical.choose_spec (f.total_model M x.val x.property)).1

omit [𝗣𝗔 ⪯ T] in
/-- The function is characterized by its interpreted graph, independently
of the choice used to obtain its value. -/
theorem value_eq_iff {C D : Carrier} (f : GraphMorphism T C D)
    (x : Obj M C) (y : Obj M D) :
    value T M f x = y ↔ f.graph.val.Evalb ![x.val, y.val] := by
  constructor
  · rintro rfl
    exact value_graph T M f x
  · intro hy
    apply Subtype.ext
    exact (f.total_model M x.val x.property).unique (value_graph T M f x) hy

omit [𝗣𝗔 ⪯ T] in
theorem value_congr {C D : Carrier} (f g : GraphMorphism T C D)
    (h : Uniform T f.graph g.graph) : value T M f = value T M g := by
  funext x
  exact ((value_eq_iff T M g x (value T M f x)).mpr
    ((SyntacticModel.uniform_model T M h x.val _).mp (value_graph T M f x))).symm

/-- Interpretation descends through provable uniform graph equality. -/
def map {C D : PredicateCategory T} (f : C ⟶ D) : Obj M C → Obj M D :=
  Quotient.lift (value T M) (value_congr T M) f

@[simp] theorem map_class {C D : PredicateCategory T} (f : GraphMorphism T C D) :
    map T M (classOfGraph T f) = value T M f := rfl

/-- The covariant model functor on the arbitrary Sigma-one predicate category. No
enumeration or standardness of the model is assumed. -/
def functor : PredicateCategory T ⥤ Type where
  obj C := Obj M C
  map f := ↾(map T M f)
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (GraphMorphism.identityGraph_eval C x.val _).mp
      (value_graph T M (GraphMorphism.identity T C) x) |>.2
  map_comp f g := by
    induction f, g using Quotient.inductionOn₂ with
    | _ f g =>
      apply ConcreteCategory.hom_ext
      intro x
      apply (value_eq_iff T M (f.composition g) x _).mpr
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
      let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      change (comp g.graph f.graph).val.Evalb ![x.val, _]
      exact (comp_eval g.graph f.graph _).mpr
        ⟨(value T M f x).val, value_graph T M f x, value_graph T M g (value T M f x)⟩

@[simp] theorem map_class_eq_iff {C D : PredicateCategory T}
    (f : GraphMorphism T C D) (x : Obj M C) (y : Obj M D) :
    (functor T M).map (classOfGraph T f) x = y ↔ f.graph.val.Evalb ![x.val, y.val] :=
  value_eq_iff T M f x y

/-- Predicate interpretation agrees with the existing program interpretation
on every represented functional graph, in every model of the theory. -/
theorem map_program_graph {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (x : Obj M C) (y : Obj M D) :
    (functor T M).map (classOfGraph T f) x = y ↔
      SyntacticModel.programRelation T M f.programClass x.val y.val :=
  (map_class_eq_iff T M f x y).trans (f.programClass_model M x.val y.val).symm

/-- The total interpretation on the total restriction splitting, transported along the
proved predicate-presentation equivalence. -/
def totalFunctor : TotalSplit T ⥤ Type :=
  (predicateEquivalence T).inverse ⋙ functor T M

/-- The comparison is natural for every quotient graph, including graphs
between different carrier predicates. -/
def predicateComparison : realization T ⋙ totalFunctor T M ≅ functor T M :=
  NatIso.ofComponents
    (fun C => (functor T M).mapIso ((predicateEquivalence T).unitIso.app C).symm)
    (by
      intro C D f
      have h := congrArg (functor T M).map
        ((predicateEquivalence T).unitIso.inv.naturality f)
      change (functor T M).map
          ((predicateEquivalence T).inverse.map ((realization T).map f)) ≫
          (functor T M).map ((predicateEquivalence T).unitIso.inv.app D) =
        (functor T M).map ((predicateEquivalence T).unitIso.inv.app C) ≫
          (functor T M).map f
      simpa only [predicateEquivalence, Functor.asEquivalence_functor, Functor.map_comp,
        Functor.comp_map, Functor.id_map] using h)

theorem predicateComparison_naturality {C D : PredicateCategory T} (f : C ⟶ D) :
    (totalFunctor T M).map ((realization T).map f) ≫
        (predicateComparison T M).hom.app D =
      (predicateComparison T M).hom.app C ≫ (functor T M).map f :=
  (predicateComparison T M).hom.naturality f

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] in
/-- The interpretations over all models jointly reflect graph equality. -/
theorem jointly_faithful {C D : PredicateCategory T} (f g : C ⟶ D)
    (h : ∀ (N : Type) [ORingStructure N] [N↓[ℒₒᵣ] ⊧* T],
      (functor T N).map f = (functor T N).map g) : f = g := by
  induction f, g using Quotient.inductionOn₂ with
  | _ f g =>
    apply Quotient.sound
    apply complete.{0} T
    intro N _ _
    rw [models_iff, uniformSentence_eval]
    intro x y
    constructor
    · intro hxy
      obtain ⟨hc, hd⟩ := f.support_model N x y hxy
      have hf := (map_class_eq_iff T N f ⟨x, hc⟩ ⟨y, hd⟩).mpr hxy
      have he := ConcreteCategory.congr_hom (h N) ⟨x, hc⟩
      exact (map_class_eq_iff T N g ⟨x, hc⟩ ⟨y, hd⟩).mp (he.symm.trans hf)
    · intro hxy
      obtain ⟨hc, hd⟩ := g.support_model N x y hxy
      have hg := (map_class_eq_iff T N g ⟨x, hc⟩ ⟨y, hd⟩).mpr hxy
      have he := ConcreteCategory.congr_hom (h N) ⟨x, hc⟩
      exact (map_class_eq_iff T N f ⟨x, hc⟩ ⟨y, hd⟩).mp (he.trans hg)

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
