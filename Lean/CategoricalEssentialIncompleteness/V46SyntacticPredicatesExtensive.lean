/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Extensivity of the arithmetic predicate category and total splitting -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The converse of a Sigma-one graph remains Sigma-one. -/
def converseGraph (F : Graph) : Graph := .mkSigma “x y. !F.val y x”

@[simp] theorem converseGraph_eval (F : Graph)
    {M : Type} [ORingStructure M] (x y : M) :
    (converseGraph F).val.Evalb ![x, y] ↔ F.val.Evalb ![y, x] := by
  simp [converseGraph]

/-- Semantic bijectivity supplies the two first-order proofs required to
make the actual converse graph a total predicate-category morphism. -/
def converseOfModelsBijective {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) :
    GraphMorphism T D C where
  graph := converseGraph f.graph
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro y x hyx
    have hs := f.support_model M x y ((converseGraph_eval _ _ _).mp hyx)
    exact ⟨hs.2, hs.1⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro y hy
    let sy : Obj M D := ⟨y, hy⟩
    obtain ⟨sx, hsx⟩ := (h M).2 sy
    have hf : f.graph.val.Evalb ![sx.val, y] :=
      (map_class_eq_iff T M f sx sy).mp hsx
    refine ⟨sx.val, (converseGraph_eval _ _ _).mpr hf, ?_⟩
    intro x hx
    have hfx := (converseGraph_eval _ _ _).mp hx
    let x' : Obj M C := ⟨x, (f.support_model M x y hfx).1⟩
    have hx' : (functor T M).map (representedArrow T f) x' = sy :=
      (map_class_eq_iff T M f x' sy).mpr hfx
    exact congrArg Subtype.val ((h M).1 (hx'.trans hsx.symm))

@[simp] theorem converseOfModelsBijective_eval {C D : PredicateCategory T}
    (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f)))
    (M : Type) [ORingStructure M] (x y : M) :
    (converseOfModelsBijective T f h).graph.val.Evalb ![x, y] ↔
      f.graph.val.Evalb ![y, x] := converseGraph_eval _ _ _

theorem forward_converse {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) :
    representedArrow T f ≫ representedArrow T (converseOfModelsBijective T f h) = 𝟙 C := by
  apply hom_ext T
  intro M _ _ x z
  rw [relation_comp, relation_id]
  simp only [relation_class, converseOfModelsBijective_eval]
  constructor
  · rintro ⟨y, hxy, hzy⟩
    have hc := (f.support_model M x y hxy).1
    have hd := (f.support_model M x y hxy).2
    have hyx : (converseOfModelsBijective T f h).graph.val.Evalb ![y, x] :=
      (converseOfModelsBijective_eval T f h M y x).mpr hxy
    have hyz : (converseOfModelsBijective T f h).graph.val.Evalb ![y, z] :=
      (converseOfModelsBijective_eval T f h M y z).mpr hzy
    exact ⟨hc, ((converseOfModelsBijective T f h).total_model M y hd).unique hyz hyx⟩
  · rintro ⟨hc, hzx⟩
    subst z
    obtain ⟨y, hxy, _⟩ := f.total_model M x hc
    exact ⟨y, hxy, hxy⟩

theorem converse_forward {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) :
    representedArrow T (converseOfModelsBijective T f h) ≫ representedArrow T f = 𝟙 D := by
  apply hom_ext T
  intro M _ _ x z
  rw [relation_comp, relation_id]
  simp only [relation_class, converseOfModelsBijective_eval]
  constructor
  · rintro ⟨y, hyx, hyz⟩
    have hs := f.support_model M y x hyx
    exact ⟨hs.2, (f.total_model M y hs.1).unique hyz hyx⟩
  · rintro ⟨hd, hzx⟩
    subst z
    obtain ⟨y, hy, _⟩ := (converseOfModelsBijective T f h).total_model M x hd
    have hyx := (converseOfModelsBijective_eval T f h M x y).mp hy
    exact ⟨y, hyx, hyx⟩

/-- Isomorphism reflection is a proved syntactic consequence of all-model
bijectivity; the inverse is the represented converse Sigma-one graph. -/
def isoOfModelsBijective {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) : C ≅ D where
  hom := representedArrow T f
  inv := representedArrow T (converseOfModelsBijective T f h)
  hom_inv_id := forward_converse T f h
  inv_hom_id := converse_forward T f h

theorem isIso_of_models_bijective {C D : PredicateCategory T} (f : C ⟶ D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map f)) : IsIso f := by
  let g := chosenGraph T f
  have hg : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T g)) := by
    intro M _ _
    simpa only [g, chosenGraph_class] using h M
  have hi := (isoOfModelsBijective T g hg).isIso_hom
  simpa only [isoOfModelsBijective, g, chosenGraph_class] using hi

/-- The index includes every Type-zero arithmetic model used by the
completeness theorem. This is a genuine model bundle, with no preservation
or categorical conclusion stored as a field. -/
structure ArithmeticModel (T : ArithmeticTheory) where
  carrier : Type
  arithmetic : ORingStructure carrier
  models : letI := arithmetic; carrier↓[ℒₒᵣ] ⊧* T

instance (m : ArithmeticModel T) : ORingStructure m.carrier := m.arithmetic

instance (m : ArithmeticModel T) : m.carrier↓[ℒₒᵣ] ⊧* T := m.models

/-- Package all of the actual model functors into one functor to a
functor category, where finite constructions are evaluated pointwise. -/
def allModels : PredicateCategory T ⥤ (Discrete (ArithmeticModel T) ⥤ Type) where
  obj C := Discrete.functor (fun m => Obj m.carrier C)
  map f := Discrete.natTrans (fun m => (functor T m.as.carrier).map f)
  map_id C := by
    apply NatTrans.ext
    funext m
    exact (functor T m.as.carrier).map_id C
  map_comp f g := by
    apply NatTrans.ext
    funext m
    exact (functor T m.as.carrier).map_comp f g

theorem allModels_evaluation (m : ArithmeticModel T) :
    allModels T ⋙ (evaluation (Discrete (ArithmeticModel T)) Type).obj ⟨m⟩ =
      functor T m.carrier := rfl

instance allModels_reflectsIsomorphisms : (allModels T).ReflectsIsomorphisms where
  reflects f _ := by
    apply isIso_of_models_bijective T f
    intro M _ _
    let m : ArithmeticModel T := ⟨M, inferInstance, inferInstance⟩
    let ev := (evaluation (Discrete (ArithmeticModel T)) Type).obj ⟨m⟩
    have hi : IsIso (ev.map ((allModels T).map f)) := inferInstance
    exact (isIso_iff_bijective _).mp hi

instance allModels_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (allModels T) :=
  preservesLimitsOfShape_of_evaluation _ _ (by
    rintro ⟨m⟩
    rw [allModels_evaluation]
    infer_instance)

instance allModels_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (allModels T) :=
  preservesColimitsOfShape_of_evaluation _ _ (by
    rintro ⟨m⟩
    rw [allModels_evaluation]
    infer_instance)

/-- Mathlib's criterion transfers extensivity from the conservative
all-model interpretation, using its proved pullback and sum preservation. -/
instance predicateFinitaryExtensive : FinitaryExtensive (PredicateCategory T) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (allModels T)

instance totalSplitHasFiniteCoproducts : HasFiniteCoproducts (TotalSplit T) where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence (predicateEquivalence T).inverse

/-- Extensivity transports to the actual category of total split program maps. -/
instance totalSplitFinitaryExtensive : FinitaryExtensive (TotalSplit T) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (predicateEquivalence T).inverse

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
