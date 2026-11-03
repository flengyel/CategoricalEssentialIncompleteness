/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PredicateInterpretation
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRelations
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! # Predicate coproducts and their interpretation as disjoint unions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem map_eq_iff_relation {C D : PredicateCategory T} (f : C ⟶ D)
    (x : Obj M C) (y : Obj M D) :
    (functor T M).map f x = y ↔ relation T f M x.val y.val := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  exact (map_class_eq_iff T M g x y).trans (relation_class T g M x.val y.val).symm

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
def emptyCarrier : Carrier := .mkSigma “x. x ≠ x”

@[simp] theorem emptyCarrier_eval (x : M) : ¬ emptyCarrier.val.Evalb ![x] := by
  simp [emptyCarrier]

def emptyMap (C : PredicateCategory T) : GraphMorphism T emptyCarrier C where
  graph := .mkSigma “x y. x ≠ x”
  support := by
    apply complete.{0} T
    intro N _ _
    simp [models_iff, supportSentence_eval]
  total := by
    apply complete.{0} T
    intro N _ _
    simp [models_iff, totalSentence_eval, emptyCarrier]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem emptyMap_eval (C : PredicateCategory T) (x y : M) :
    ¬ (emptyMap T C).graph.val.Evalb ![x, y] := by
  simp [emptyMap]

def emptyIsInitial : IsInitial (C := PredicateCategory T) emptyCarrier :=
  IsInitial.ofUniqueHom (fun C => representedArrow T (emptyMap T C)) (by
    intro C f
    apply hom_ext T
    intro N _ _ x y
    rw [relation_class]
    exact iff_of_false
      (fun h => emptyCarrier_eval N x (relation_support T f N x y h).1)
      (emptyMap_eval T N C x y))

instance predicateHasInitial : HasInitial (PredicateCategory T) :=
  (emptyIsInitial T).hasInitial

/-- Pair coding gives disjoint tags even in nonstandard arithmetic models. -/
def sumCarrier (C D : Carrier) : Carrier :=
  .mkSigma “z. (∃ x, !natPairFormula.val z x 0 ∧ !C.val x) ∨
    (∃ y, !natPairFormula.val z y 1 ∧ !D.val y)”

@[simp] theorem sumCarrier_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (C D : Carrier) (z : M) :
    (sumCarrier C D).val.Evalb ![z] ↔
      (∃ x, z = Arithmetic.pair x 0 ∧ C.val.Evalb ![x]) ∨
      (∃ y, z = Arithmetic.pair y 1 ∧ D.val.Evalb ![y]) := by
  simp [sumCarrier]

def sumInlGraph (C : Carrier) : Graph :=
  .mkSigma “x z. !C.val x ∧ !natPairFormula.val z x 0”

def sumInrGraph (D : Carrier) : Graph :=
  .mkSigma “y z. !D.val y ∧ !natPairFormula.val z y 1”

@[simp] theorem sumInlGraph_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (C : Carrier) (x z : M) :
    (sumInlGraph C).val.Evalb ![x, z] ↔ C.val.Evalb ![x] ∧ z = Arithmetic.pair x 0 := by
  simp [sumInlGraph]

@[simp] theorem sumInrGraph_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (D : Carrier) (y z : M) :
    (sumInrGraph D).val.Evalb ![y, z] ↔ D.val.Evalb ![y] ∧ z = Arithmetic.pair y 1 := by
  simp [sumInrGraph]

def sumInl (C D : PredicateCategory T) : GraphMorphism T C (sumCarrier C D) where
  graph := sumInlGraph C
  support := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x z h
    obtain ⟨hc, he⟩ := (sumInlGraph_eval N C x z).mp h
    exact ⟨hc, (sumCarrier_eval N C D z).mpr (Or.inl ⟨x, he, hc⟩)⟩
  total := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro x hx
    refine ⟨Arithmetic.pair x 0, (sumInlGraph_eval N C _ _).mpr ⟨hx, rfl⟩, ?_⟩
    intro z hz
    exact ((sumInlGraph_eval N C x z).mp hz).2

def sumInr (C D : PredicateCategory T) : GraphMorphism T D (sumCarrier C D) where
  graph := sumInrGraph D
  support := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro y z h
    obtain ⟨hd, he⟩ := (sumInrGraph_eval N D y z).mp h
    exact ⟨hd, (sumCarrier_eval N C D z).mpr (Or.inr ⟨y, he, hd⟩)⟩
  total := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro y hy
    refine ⟨Arithmetic.pair y 1, (sumInrGraph_eval N D _ _).mpr ⟨hy, rfl⟩, ?_⟩
    intro z hz
    exact ((sumInrGraph_eval N D y z).mp hz).2

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem sumInl_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (C D : PredicateCategory T) (x z : M) :
    (sumInl T C D).graph.val.Evalb ![x, z] ↔ C.val.Evalb ![x] ∧ z = Arithmetic.pair x 0 :=
  sumInlGraph_eval M C x z

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem sumInr_eval [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (C D : PredicateCategory T) (y z : M) :
    (sumInr T C D).graph.val.Evalb ![y, z] ↔ D.val.Evalb ![y] ∧ z = Arithmetic.pair y 1 :=
  sumInrGraph_eval M D y z

/-- The arithmetic carrier is identified with the full tagged disjoint union. -/
def sumCoding (C D : Carrier) : Obj M C ⊕ Obj M D → Obj M (sumCarrier C D) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact Sum.elim
    (fun x => ⟨Arithmetic.pair x.val 0, (sumCarrier_eval M C D _).mpr
      (Or.inl ⟨x.val, rfl, x.property⟩)⟩)
    (fun y => ⟨Arithmetic.pair y.val 1, (sumCarrier_eval M C D _).mpr
      (Or.inr ⟨y.val, rfl, y.property⟩)⟩)

theorem sumCoding_bijective (C D : Carrier) : Function.Bijective (sumCoding T M C D) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext ((pair_eq_pair_iff _ _ _ _).mp he).1)
      | inr y => exact False.elim (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp he).2)
    | inr x =>
      cases y with
      | inl y => exact False.elim (Arithmetic.one_ne_zero ((pair_eq_pair_iff _ _ _ _).mp he).2)
      | inr y => exact congrArg Sum.inr (Subtype.ext ((pair_eq_pair_iff _ _ _ _).mp he).1)
  · intro z
    rcases (sumCarrier_eval M C D z.val).mp z.property with ⟨x, hx, hc⟩ | ⟨y, hy, hd⟩
    · exact ⟨Sum.inl ⟨x, hc⟩, Subtype.ext hx.symm⟩
    · exact ⟨Sum.inr ⟨y, hd⟩, Subtype.ext hy.symm⟩

def sumEquiv (C D : Carrier) : Obj M C ⊕ Obj M D ≃ Obj M (sumCarrier C D) :=
  Equiv.ofBijective (sumCoding T M C D) (sumCoding_bijective T M C D)

def sumCopairGraph {C D E : PredicateCategory T} (f : C ⟶ E) (g : D ⟶ E) : Graph :=
  .mkSigma “z w. (∃ x, !natPairFormula.val z x 0 ∧ !(chosenGraph T f).graph.val x w) ∨
    (∃ y, !natPairFormula.val z y 1 ∧ !(chosenGraph T g).graph.val y w)”

@[simp] theorem sumCopairGraph_eval {C D E : PredicateCategory T}
    (f : C ⟶ E) (g : D ⟶ E) [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z w : M) :
    (sumCopairGraph T f g).val.Evalb ![z, w] ↔
      (∃ x, z = Arithmetic.pair x 0 ∧ relation T f M x w) ∨
      (∃ y, z = Arithmetic.pair y 1 ∧ relation T g M y w) := by
  simp [sumCopairGraph]

/-- Both branches are genuinely represented total graphs. -/
def sumCopair {C D E : PredicateCategory T} (f : C ⟶ E) (g : D ⟶ E) :
    GraphMorphism T (sumCarrier C D) E where
  graph := sumCopairGraph T f g
  support := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z w h
    rcases (sumCopairGraph_eval T N f g z w).mp h with ⟨x, he, hf⟩ | ⟨y, he, hg⟩
    · have hs := relation_support T f N x w hf
      exact ⟨(sumCarrier_eval N C D z).mpr (Or.inl ⟨x, he, hs.1⟩), hs.2⟩
    · have hs := relation_support T g N y w hg
      exact ⟨(sumCarrier_eval N C D z).mpr (Or.inr ⟨y, he, hs.1⟩), hs.2⟩
  total := by
    apply complete.{0} T
    intro N _ _
    let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    rcases (sumCarrier_eval N C D z).mp hz with ⟨x, he, hc⟩ | ⟨y, he, hd⟩
    · obtain ⟨w, hf, hfu⟩ := relation_total T f N x hc
      refine ⟨w, (sumCopairGraph_eval T N f g z w).mpr (Or.inl ⟨x, he, hf⟩), ?_⟩
      intro w' hw'
      rcases (sumCopairGraph_eval T N f g z w').mp hw' with
        ⟨x', he', hf'⟩ | ⟨y', he', hg'⟩
      · have hxx := ((pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)).1
        exact hfu w' (by simpa only [hxx] using hf')
      · exact False.elim (zero_ne_one
          ((pair_eq_pair_iff _ _ _ _).mp (he.symm.trans he')).2)
    · obtain ⟨w, hg, hgu⟩ := relation_total T g N y hd
      refine ⟨w, (sumCopairGraph_eval T N f g z w).mpr (Or.inr ⟨y, he, hg⟩), ?_⟩
      intro w' hw'
      rcases (sumCopairGraph_eval T N f g z w').mp hw' with
        ⟨x', he', hf'⟩ | ⟨y', he', hg'⟩
      · exact False.elim (zero_ne_one
          ((pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)).2)
      · have hyy := ((pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)).1
        exact hgu w' (by simpa only [hyy] using hg')

@[simp] theorem sumCopair_eval {C D E : PredicateCategory T}
    (f : C ⟶ E) (g : D ⟶ E) [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z w : M) :
    (sumCopair T f g).graph.val.Evalb ![z, w] ↔
      (∃ x, z = Arithmetic.pair x 0 ∧ relation T f M x w) ∨
      (∃ y, z = Arithmetic.pair y 1 ∧ relation T g M y w) :=
  sumCopairGraph_eval T M f g z w

theorem sum_inl_desc {C D E : PredicateCategory T} (f : C ⟶ E) (g : D ⟶ E) :
    representedArrow T (sumInl T C D) ≫ representedArrow T (sumCopair T f g) = f := by
  apply hom_ext T
  intro N _ _ x w
  let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simp only [relation_comp, relation_class, sumInl_eval, sumCopair_eval]
  constructor
  · rintro ⟨z, ⟨_, he⟩, h⟩
    subst z
    rcases h with ⟨x', he', hf⟩ | ⟨y', he', hg⟩
    · have hxx := ((pair_eq_pair_iff _ _ _ _).mp he').1
      simpa only [← hxx] using hf
    · exact False.elim (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp he').2)
  · intro hf
    exact ⟨Arithmetic.pair x 0, ⟨(relation_support T f N x w hf).1, rfl⟩,
      Or.inl ⟨x, rfl, hf⟩⟩

theorem sum_inr_desc {C D E : PredicateCategory T} (f : C ⟶ E) (g : D ⟶ E) :
    representedArrow T (sumInr T C D) ≫ representedArrow T (sumCopair T f g) = g := by
  apply hom_ext T
  intro N _ _ y w
  let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simp only [relation_comp, relation_class, sumInr_eval, sumCopair_eval]
  constructor
  · rintro ⟨z, ⟨_, he⟩, h⟩
    subst z
    rcases h with ⟨x', he', hf⟩ | ⟨y', he', hg⟩
    · exact False.elim (Arithmetic.one_ne_zero ((pair_eq_pair_iff _ _ _ _).mp he').2)
    · have hyy := ((pair_eq_pair_iff _ _ _ _).mp he').1
      simpa only [← hyy] using hg
  · intro hg
    exact ⟨Arithmetic.pair y 1, ⟨(relation_support T g N y w hg).1, rfl⟩,
      Or.inr ⟨y, rfl, hg⟩⟩

def sumIsColimit (C D : PredicateCategory T) :
    IsColimit (BinaryCofan.mk (representedArrow T (sumInl T C D))
      (representedArrow T (sumInr T C D))) := by
  refine BinaryCofan.IsColimit.mk _ (fun f g => representedArrow T (sumCopair T f g))
    (fun f g => sum_inl_desc T f g) (fun f g => sum_inr_desc T f g) ?_
  intro E f g m hmf hmg
  apply hom_ext T
  intro N _ _ z w
  let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [relation_class, sumCopair_eval]
  constructor
  · intro hm
    rcases (sumCarrier_eval N C D z).mp (relation_support T m N z w hm).1 with
      ⟨x, he, hc⟩ | ⟨y, he, hd⟩
    · refine Or.inl ⟨x, he, ?_⟩
      rw [← hmf, relation_comp]
      exact ⟨z, (relation_class T _ N x z).mpr
        ((sumInl_eval T N C D x z).mpr ⟨hc, he⟩), hm⟩
    · refine Or.inr ⟨y, he, ?_⟩
      rw [← hmg, relation_comp]
      exact ⟨z, (relation_class T _ N y z).mpr
        ((sumInr_eval T N C D y z).mpr ⟨hd, he⟩), hm⟩
  · rintro (⟨x, he, hf⟩ | ⟨y, he, hg⟩)
    · rw [← hmf, relation_comp] at hf
      obtain ⟨z', hi, hm⟩ := hf
      have he' := ((sumInl_eval T N C D x z').mp
        ((relation_class T _ N x z').mp hi)).2
      simpa only [he'.trans he.symm] using hm
    · rw [← hmg, relation_comp] at hg
      obtain ⟨z', hi, hm⟩ := hg
      have he' := ((sumInr_eval T N C D y z').mp
        ((relation_class T _ N y z').mp hi)).2
      simpa only [he'.trans he.symm] using hm

instance predicateHasBinaryCoproducts : HasBinaryCoproducts (PredicateCategory T) := by
  let : ∀ {C D : PredicateCategory T}, HasColimit (CategoryTheory.Limits.pair C D) :=
    fun {C D} => ⟨⟨⟨_, sumIsColimit T C D⟩⟩⟩
  exact hasBinaryCoproducts_of_hasColimit_pair (PredicateCategory T)

instance predicateHasFiniteCoproducts : HasFiniteCoproducts (PredicateCategory T) :=
  hasFiniteCoproducts_of_has_binary_and_initial

@[simp] theorem map_sumInl (C D : PredicateCategory T) (x : Obj M C) :
    (functor T M).map (representedArrow T (sumInl T C D)) x =
      sumCoding T M C D (Sum.inl x) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply (map_class_eq_iff T M _ _ _).mpr
  exact (sumInl_eval T M C D _ _).mpr ⟨x.property, rfl⟩

@[simp] theorem map_sumInr (C D : PredicateCategory T) (y : Obj M D) :
    (functor T M).map (representedArrow T (sumInr T C D)) y =
      sumCoding T M C D (Sum.inr y) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply (map_class_eq_iff T M _ _ _).mpr
  exact (sumInr_eval T M C D _ _).mpr ⟨y.property, rfl⟩

/-- The chosen predicate coproduct is interpreted as the tagged set coproduct. -/
def mappedSumIsColimit (C D : PredicateCategory T) :
    IsColimit ((functor T M).mapCocone (BinaryCofan.mk
      (representedArrow T (sumInl T C D)) (representedArrow T (sumInr T C D)))) := by
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm ?_
  refine BinaryCofan.IsColimit.mk _
    (fun f g => ↾fun z => Sum.elim f g ((sumEquiv T M C D).symm z)) ?_ ?_ ?_
  · intro E f g
    apply ConcreteCategory.hom_ext
    intro x
    change Sum.elim f g ((sumEquiv T M C D).symm
      ((functor T M).map (representedArrow T (sumInl T C D)) x)) = f x
    rw [map_sumInl]
    exact congrArg (Sum.elim f g) ((sumEquiv T M C D).symm_apply_apply (Sum.inl x))
  · intro E f g
    apply ConcreteCategory.hom_ext
    intro y
    change Sum.elim f g ((sumEquiv T M C D).symm
      ((functor T M).map (representedArrow T (sumInr T C D)) y)) = g y
    rw [map_sumInr]
    exact congrArg (Sum.elim f g) ((sumEquiv T M C D).symm_apply_apply (Sum.inr y))
  · intro E f g m hmf hmg
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨x, rfl⟩ := sumCoding_bijective T M C D |>.surjective z
    cases x with
    | inl x =>
      have h := ConcreteCategory.congr_hom hmf x
      change m ((functor T M).map (representedArrow T (sumInl T C D)) x) = f x at h
      rw [map_sumInl] at h
      change m (sumCoding T M C D (Sum.inl x)) =
        Sum.elim f g ((sumEquiv T M C D).symm ((sumEquiv T M C D) (Sum.inl x)))
      rw [(sumEquiv T M C D).symm_apply_apply]
      exact h
    | inr y =>
      have h := ConcreteCategory.congr_hom hmg y
      change m ((functor T M).map (representedArrow T (sumInr T C D)) y) = g y at h
      rw [map_sumInr] at h
      change m (sumCoding T M C D (Sum.inr y)) =
        Sum.elim f g ((sumEquiv T M C D).symm ((sumEquiv T M C D) (Sum.inr y)))
      rw [(sumEquiv T M C D).symm_apply_apply]
      exact h

instance preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (functor T M) where
  preservesColimit {K} := by
    have : PreservesColimit (CategoryTheory.Limits.pair (K.obj ⟨WalkingPair.left⟩)
        (K.obj ⟨WalkingPair.right⟩)) (functor T M) :=
      preservesColimit_of_preserves_colimit_cocone (sumIsColimit T _ _)
        (mappedSumIsColimit T M _ _)
    exact preservesColimit_of_iso_diagram (functor T M) (diagramIsoPair K).symm

/-- The false carrier stays empty in every model, including nonstandard ones. -/
def mappedEmptyIsInitial : IsInitial ((functor T M).obj emptyCarrier) :=
  IsInitial.ofUniqueHom (fun X => ↾fun x => False.elim (emptyCarrier_eval M x.val x.property))
    (by
      intro X f
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim (emptyCarrier_eval M x.val x.property))

instance preservesInitial :
    PreservesColimit (Functor.empty.{0} (PredicateCategory T)) (functor T M) :=
  preservesColimit_of_preserves_colimit_cocone (emptyIsInitial T)
    ((isColimitMapCoconeEmptyCoconeEquiv (functor T M) emptyCarrier).symm
      (mappedEmptyIsInitial T M))

instance preservesFiniteCoproducts : PreservesFiniteCoproducts (functor T M) where
  preserves n := by
    let := preservesColimitsOfShape_pempty_of_preservesInitial (functor T M)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (functor T M) (Fin n)

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
