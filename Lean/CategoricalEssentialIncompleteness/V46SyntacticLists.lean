/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListEvaluation
import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular
import CategoricalEssentialIncompleteness.V46CategoricalLists
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Canonical predicate-category list constructors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists

abbrev listCarrier := SyntacticListEvaluation.listCarrier

def listObject (T : ArithmeticTheory) (V : PredicateCategory T) : PredicateCategory T :=
  listCarrier V

/-- Nil is the same numerical zero for every coefficient predicate. -/
def nilGraph (C : Carrier) : Graph := .mkSigma “x y. !C.val x ∧ y = 0”

@[simp] theorem nilGraph_eval {M : Type} [ORingStructure M] (C : Carrier) (x y : M) :
    (nilGraph C).val.Evalb ![x, y] ↔ C.val.Evalb ![x] ∧ y = 0 := by
  simp [nilGraph]

/-- Cons uses exactly the canonical adjoin graph, with source carrier
conditions on the entry and tail, and with no membership witnesses in the code. -/
def consGraph (V : Carrier) : Graph :=
  let L := listCarrier V
  .mkSigma “z y. ∃ v a, !pairDef.val z v a ∧ !V.val v ∧ !L.val a ∧ !adjoinDef.val y v a”

section ArithmeticModels

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem listCarrier_eval (V : Carrier) (a : M) :
    (listCarrier V).val.Evalb ![a] ↔ ∀ i < len a, V.val.Evalb ![nth a i] := by
  rw [listCarrier, SyntacticListEvaluation.listCarrier,
    ← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval]

theorem listCarrier_nil (V : Carrier) : (listCarrier V).val.Evalb (M := M) ![0] := by
  rw [listCarrier_eval]
  simp

theorem listCarrier_cons (V : Carrier) (v a : M) :
    (listCarrier V).val.Evalb ![adjoin v a] ↔
      V.val.Evalb ![v] ∧ (listCarrier V).val.Evalb ![a] := by
  simp only [listCarrier_eval]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    intro i hi
    simpa using h (i + 1) (by simpa using hi)
  · rintro ⟨hv, ha⟩ i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using hv
    · have hj : j < len a := by simpa using hi
      simpa using ha j hj

@[simp] theorem consGraph_eval (V : Carrier) (z y : M) :
    (consGraph V).val.Evalb ![z, y] ↔
      ∃ v a : M, z = ⟪v, a⟫ ∧ V.val.Evalb ![v] ∧
        (listCarrier V).val.Evalb ![a] ∧ y = adjoin v a := by
  simp [consGraph]

end ArithmeticModels

abbrev Obj (T : ArithmeticTheory) (M : Type) [ORingStructure M]
    (C : PredicateCategory T) := PredicateInterpretation.Obj M C

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def nilMorphism (C V : PredicateCategory T) : GraphMorphism T C (listObject T V) where
  graph := nilGraph C
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x y h
    obtain ⟨hc, he⟩ := (nilGraph_eval C x y).mp h
    subst y
    exact ⟨hc, listCarrier_nil V⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro x hx
    refine ⟨0, (nilGraph_eval C x 0).mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact ((nilGraph_eval C x y).mp hy).2

def consMorphism (V : PredicateCategory T) :
    GraphMorphism T (productCarrier V (listObject T V)) (listObject T V) where
  graph := consGraph V
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z y h
    obtain ⟨v, a, he, hv, ha, hy⟩ := (consGraph_eval V z y).mp h
    subst y
    exact ⟨(productCarrier_eval V (listCarrier V) z).mpr ⟨v, a, he, hv, ha⟩,
      (listCarrier_cons V v a).mpr ⟨hv, ha⟩⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    obtain ⟨v, a, he, hv, ha⟩ := (productCarrier_eval V (listCarrier V) z).mp hz
    refine ⟨adjoin v a, (consGraph_eval V z _).mpr ⟨v, a, he, hv, ha, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨v', a', he', _, _, hy'⟩ := (consGraph_eval V z y).mp hy
    obtain ⟨hvv, haa⟩ := (pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)
    simpa only [hvv, haa] using hy'

/-- The map from the chosen categorical product to its literal arithmetic
pair presentation is constructed from the two categorical projections. -/
def toRawProduct (C D : PredicateCategory T) :
    @Quiver.Hom (PredicateCategory T) inferInstance (C ⨯ D) (productCarrier C D) :=
  representedArrow T (productLift T prod.fst prod.snd)

def fromRawProduct (C D : PredicateCategory T) :
    @Quiver.Hom (PredicateCategory T) inferInstance (productCarrier C D) (C ⨯ D) :=
  prod.lift (representedArrow T (productFst T C D))
    (representedArrow T (productSnd T C D))

@[simp] theorem toRaw_fromRaw (C D : PredicateCategory T) :
    toRawProduct T C D ≫ fromRawProduct T C D = 𝟙 (C ⨯ D) := by
  apply prod.hom_ext
  · simp only [Category.assoc, fromRawProduct, prod.lift_fst, Category.id_comp]
    exact productLift_fst T _ _
  · simp only [Category.assoc, fromRawProduct, prod.lift_snd, Category.id_comp]
    exact productLift_snd T _ _

@[simp] theorem fromRaw_toRaw (C D : PredicateCategory T) :
    fromRawProduct T C D ≫ toRawProduct T C D =
      𝟙 _ := by
  apply BinaryFan.IsLimit.hom_ext (productIsLimit T C D)
  · change (fromRawProduct T C D ≫ toRawProduct T C D) ≫
      representedArrow T (productFst T C D) = 𝟙 _ ≫ _
    rw [Category.assoc, show toRawProduct T C D ≫
      representedArrow T (productFst T C D) = prod.fst from productLift_fst T _ _]
    simp only [fromRawProduct, prod.lift_fst, Category.id_comp]
    rfl
  · change (fromRawProduct T C D ≫ toRawProduct T C D) ≫
      representedArrow T (productSnd T C D) = 𝟙 _ ≫ _
    rw [Category.assoc, show toRawProduct T C D ≫
      representedArrow T (productSnd T C D) = prod.snd from productLift_snd T _ _]
    simp only [fromRawProduct, prod.lift_snd, Category.id_comp]
    rfl

/-- The actual list algebra for an arbitrary Sigma-one coefficient object. -/
def algebra (V : PredicateCategory T) : ListAlgebra (D := PredicateCategory T) V where
  carrier := listObject T V
  nil := representedArrow T (nilMorphism T (⊤_ (PredicateCategory T)) V)
  cons := toRawProduct T V (listObject T V) ≫ representedArrow T (consMorphism T V)

section Models

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

abbrev F := PredicateInterpretation.functor T M

/-- A quotient arrow and its represented graph have the same model values. -/
theorem map_eq_iff_relation {C D : PredicateCategory T} (f : C ⟶ D)
    (x : Obj T M C) (y : Obj T M D) :
    (F T M).map f x = y ↔ relation T f M x.val y.val := by
  rw [← chosenGraph_class T f]
  exact (PredicateInterpretation.map_class_eq_iff T M (chosenGraph T f) x y).trans
    (relation_class T (chosenGraph T f) M x.val y.val).symm

theorem chosenGraph_map_iff {C D : PredicateCategory T} (f : C ⟶ D)
    (x : Obj T M C) (y : Obj T M D) :
    (chosenGraph T f).graph.val.Evalb ![x.val, y.val] ↔ (F T M).map f x = y :=
  (chosenGraph_eval T f M x.val y.val).trans (map_eq_iff_relation T M f x y).symm

theorem over_value {P : PredicateCategory T} {X Y : Over P} (f : X ⟶ Y)
    (x : Obj T M X.left) :
    (F T M).map Y.hom ((F T M).map f.left x) = (F T M).map X.hom x := by
  have h := congrArg (F T M).map (Over.w f)
  rw [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

/-- Product projections detect model points of the chosen product. -/
theorem modelProduct_ext {C D : PredicateCategory T} {x y : Obj T M (C ⨯ D)}
    (h₁ : (F T M).map (prod.fst : C ⨯ D ⟶ C) x = (F T M).map prod.fst y)
    (h₂ : (F T M).map (prod.snd : C ⨯ D ⟶ D) x = (F T M).map prod.snd y) : x = y := by
  have hlim := (isLimitMapConeBinaryFanEquiv (F T M) _ _)
    (isLimitOfPreserves (F T M) (prodIsProd C D))
  let a : PUnit ⟶ Obj T M (C ⨯ D) := ↾fun _ => x
  let b : PUnit ⟶ Obj T M (C ⨯ D) := ↾fun _ => y
  have he : a = b := BinaryFan.IsLimit.hom_ext hlim
    (by ext u; exact h₁) (by ext u; exact h₂)
  exact ConcreteCategory.congr_hom he PUnit.unit

/-- Preservation of the product cone supplies a model point for every pair. -/
theorem modelProduct_exists (C D : PredicateCategory T) (x : Obj T M C) (y : Obj T M D) :
    ∃ z : Obj T M (C ⨯ D), (F T M).map (prod.fst : C ⨯ D ⟶ C) z = x ∧
      (F T M).map (prod.snd : C ⨯ D ⟶ D) z = y := by
  have hlim := (isLimitMapConeBinaryFanEquiv (F T M) _ _)
    (isLimitOfPreserves (F T M) (prodIsProd C D))
  let a : PUnit ⟶ Obj T M C := ↾fun _ => x
  let b : PUnit ⟶ Obj T M D := ↾fun _ => y
  let z := BinaryFan.IsLimit.lift hlim a b
  refine ⟨z PUnit.unit, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_fst hlim a b) PUnit.unit
  · exact ConcreteCategory.congr_hom (BinaryFan.IsLimit.lift_snd hlim a b) PUnit.unit

/-- The slice product is interpreted as the actual fiber product, for
arbitrary carrier predicates and arbitrary projections to the parameter. -/
theorem modelOverProduct_exists {P : PredicateCategory T} (A B : Over P)
    (a : Obj T M A.left) (b : Obj T M B.left)
    (h : (F T M).map A.hom a = (F T M).map B.hom b) :
    ∃ z : Obj T M (A ⨯ B).left,
      (F T M).map (prod.fst : A ⨯ B ⟶ A).left z = a ∧
        (F T M).map (prod.snd : A ⨯ B ⟶ B).left z = b := by
  have hp := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A B)).map (F T M)
  exact Types.exists_of_isPullback hp a b h

theorem modelOverProduct_ext {P : PredicateCategory T} (A B : Over P)
    {x y : Obj T M (A ⨯ B).left}
    (h₁ : (F T M).map (prod.fst : A ⨯ B ⟶ A).left x =
      (F T M).map (prod.fst : A ⨯ B ⟶ A).left y)
    (h₂ : (F T M).map (prod.snd : A ⨯ B ⟶ B).left x =
      (F T M).map (prod.snd : A ⨯ B ⟶ B).left y) : x = y := by
  have hp := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A B)).map (F T M)
  exact Types.ext_of_isPullback hp h₁ h₂

/-- Mapping a pair of slice morphisms acts componentwise on every
interpreted fiber product. -/
theorem modelOverProduct_map_fst {P : PredicateCategory T} {A B C D : Over P}
    (f : A ⟶ C) (g : B ⟶ D) (q : Obj T M (A ⨯ B).left) :
    (F T M).map (prod.fst : C ⨯ D ⟶ C).left
      ((F T M).map (prod.map f g).left q) =
        (F T M).map f.left ((F T M).map (prod.fst : A ⨯ B ⟶ A).left q) := by
  have h : (prod.map f g).left ≫ (prod.fst : C ⨯ D ⟶ C).left =
      (prod.fst : A ⨯ B ⟶ A).left ≫ f.left :=
    congrArg Over.Hom.left (prod.map_fst f g)
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm q

theorem modelOverProduct_map_snd {P : PredicateCategory T} {A B C D : Over P}
    (f : A ⟶ C) (g : B ⟶ D) (q : Obj T M (A ⨯ B).left) :
    (F T M).map (prod.snd : C ⨯ D ⟶ D).left
      ((F T M).map (prod.map f g).left q) =
        (F T M).map g.left ((F T M).map (prod.snd : A ⨯ B ⟶ B).left q) := by
  have h : (prod.map f g).left ≫ (prod.snd : C ⨯ D ⟶ D).left =
      (prod.snd : A ⨯ B ⟶ B).left ≫ g.left :=
    congrArg Over.Hom.left (prod.map_snd f g)
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm q

theorem nil_value (C V : PredicateCategory T) (x : Obj T M C) :
    ((F T M).map (representedArrow T (nilMorphism T C V)) x).val = 0 := by
  have h := (PredicateInterpretation.map_class_eq_iff T M (nilMorphism T C V) x
    ((F T M).map (representedArrow T (nilMorphism T C V)) x)).mp rfl
  exact ((nilGraph_eval C x.val _).mp h).2

section ArithmeticValues

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A canonical point of the chosen product, obtained from the literal
pair through the proved categorical comparison. -/
def pairPoint {C D : PredicateCategory T} (x : Obj T M C) (y : Obj T M D) :
    Obj T M (C ⨯ D) :=
  (F T M).map (fromRawProduct T C D) (PredicateInterpretation.productCoding T M C D (x, y))

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem pairPoint_fst {C D : PredicateCategory T}
    (x : Obj T M C) (y : Obj T M D) :
    (F T M).map (prod.fst : C ⨯ D ⟶ C) (pairPoint T M x y) = x := by
  have h : fromRawProduct T C D ≫ (prod.fst : C ⨯ D ⟶ C) =
      representedArrow T (productFst T C D) := prod.lift_fst _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp] at hm
  have hp := ConcreteCategory.congr_hom hm
    (PredicateInterpretation.productCoding T M C D (x, y))
  exact hp.trans (PredicateInterpretation.map_productFst T M C D (x, y))

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem pairPoint_snd {C D : PredicateCategory T}
    (x : Obj T M C) (y : Obj T M D) :
    (F T M).map (prod.snd : C ⨯ D ⟶ D) (pairPoint T M x y) = y := by
  have h : fromRawProduct T C D ≫ (prod.snd : C ⨯ D ⟶ D) =
      representedArrow T (productSnd T C D) := prod.lift_snd _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp] at hm
  have hp := ConcreteCategory.congr_hom hm
    (PredicateInterpretation.productCoding T M C D (x, y))
  exact hp.trans (PredicateInterpretation.map_productSnd T M C D (x, y))

theorem toRawProduct_value (C D : PredicateCategory T) (q : Obj T M (C ⨯ D)) :
    ((F T M).map (toRawProduct T C D) q).val =
      ⟪((F T M).map (prod.fst : C ⨯ D ⟶ C) q).val,
        ((F T M).map (prod.snd : C ⨯ D ⟶ D) q).val⟫ := by
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (productLift T (prod.fst : C ⨯ D ⟶ C) prod.snd) q
    ((F T M).map (toRawProduct T C D) q)).mp rfl
  obtain ⟨x, y, hx, hy, he⟩ := (productLift_eval T _ _ M q.val _).mp h
  have hx' := (map_eq_iff_relation T M (prod.fst : C ⨯ D ⟶ C) q
    ((F T M).map prod.fst q)).mp rfl
  have hy' := (map_eq_iff_relation T M (prod.snd : C ⨯ D ⟶ D) q
    ((F T M).map prod.snd q)).mp rfl
  have hxe := relation_functional T (prod.fst : C ⨯ D ⟶ C) M q.val _ _ hx hx'
  have hye := relation_functional T (prod.snd : C ⨯ D ⟶ D) M q.val _ _ hy hy'
  simpa only [hxe, hye] using he

theorem cons_value (V : PredicateCategory T) (q : Obj T M (V ⨯ listObject T V)) :
    ((F T M).map (algebra T V).cons q).val =
      adjoin ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
        ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val := by
  let r := (F T M).map (toRawProduct T V (listObject T V)) q
  let y := (F T M).map (representedArrow T (consMorphism T V)) r
  have hy := (PredicateInterpretation.map_class_eq_iff T M (consMorphism T V) r y).mp rfl
  obtain ⟨v, a, he, _, _, hy'⟩ := (consGraph_eval V r.val y.val).mp hy
  have hr := toRawProduct_value T M V (listObject T V) q
  change r.val = _ at hr
  obtain ⟨hv, ha⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans hr)
  have hymap : (F T M).map (algebra T V).cons q = y := by
    change (F T M).map (toRawProduct T V (listObject T V) ≫
      representedArrow T (consMorphism T V)) q = y
    rw [Functor.map_comp]
    rfl
  rw [hymap]
  simpa only [hv, ha] using hy'

end ArithmeticValues
end Models

end CategoricalEssentialIncompleteness.V46.SyntacticLists
