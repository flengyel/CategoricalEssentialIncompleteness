/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicates
public import CategoricalEssentialIncompleteness.V46RegularImage
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-! # Predicate inclusions, witness selection and regular images -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates

def inclusionSentence (C D : Carrier) : ArithmeticSentence := “∀ x, !C.val x → !D.val x”

@[simp] theorem inclusionSentence_eval {M : Type} [ORingStructure M] (C D : Carrier) :
    (inclusionSentence C D).Evalb (M := M) ![] ↔
      ∀ x : M, C.val.Evalb ![x] → D.val.Evalb ![x] := by
  simp [inclusionSentence]

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The graph class with its ambient category displayed in its type. -/
def representedArrow {C D : PredicateCategory T} (f : GraphMorphism T C D) : C ⟶ D :=
  classOfGraph T f


omit [𝗣𝗔 ⪯ T] in
theorem inclusion_model {C D : Carrier} (h : T ⊢ inclusionSentence C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M)
    (hx : C.val.Evalb ![x]) : D.val.Evalb ![x] := by
  have hm := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  rw [models_iff, inclusionSentence_eval] at hm
  exact hm x hx

namespace GraphMorphism

variable {T} {C D : PredicateCategory T}

/-- An inclusion uses the partial-identity graph of its source predicate. -/
def inclusion (h : T ⊢ inclusionSentence C D) : GraphMorphism T C D where
  graph := identityGraph C
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y hxy
    obtain ⟨hc, he⟩ := (identityGraph_eval C x y).mp hxy
    subst y
    exact ⟨hc, inclusion_model T h M x hc⟩
  total := (identity T C).total

@[simp] theorem inclusion_programClass (h : T ⊢ inclusionSentence C D) :
    (inclusion h).programClass = predicateClass T C := rfl

end GraphMorphism

section Inclusions

variable {T} {C D : PredicateCategory T} (h : T ⊢ inclusionSentence C D)

/-- The inclusion of a predicate has its concrete partial inverse in
the restriction splitting. -/
def inclusionReverse : (interpretedObject T D).obj ⟶ (interpretedObject T C).obj where
  hom := (predicateIdem T C).hom
  source := by
    change (predicateIdem T D).hom ≫ (predicateIdem T C).hom = (predicateIdem T C).hom
    have ht := (GraphMorphism.inclusion h).toSplit.target
    change (predicateIdem T C).hom ≫ (predicateIdem T D).hom =
      (predicateIdem T C).hom at ht
    exact (Idem.comm (predicateIdem T D) (predicateIdem T C)).trans ht
  target := (predicateIdem T C).idem

theorem inclusion_forward_reverse :
    (GraphMorphism.inclusion h).toSplit ≫ inclusionReverse h =
      𝟙 (interpretedObject T C).obj := by
  apply SplitObject.Hom.ext
  exact (predicateIdem T C).idem

theorem inclusion_reverse_forward :
    inclusionReverse h ≫ (GraphMorphism.inclusion h).toSplit = rst (inclusionReverse h) := by
  apply SplitObject.Hom.ext
  change (predicateIdem T C).hom ≫ (predicateIdem T C).hom = rst (predicateIdem T C).hom
  rw [(predicateIdem T C).idem, (predicateIdem T C).restriction]

instance inclusion_mono : Mono (representedArrow T (GraphMorphism.inclusion h)) := by
  apply (realization T).mono_of_mono_map
  exact LocalConnectedness.V46.total_split_mono
    (GraphMorphism.inclusion h).toTotal (inclusionReverse h) (inclusion_forward_reverse h)

end Inclusions

def surjectiveSentence (D : Carrier) (F : Graph) : ArithmeticSentence :=
  “∀ y, !D.val y → ∃ x, !F.val x y”

@[simp] theorem surjectiveSentence_eval {M : Type} [ORingStructure M]
    (D : Carrier) (F : Graph) :
    (surjectiveSentence D F).Evalb (M := M) ![] ↔
      ∀ y : M, D.val.Evalb ![y] → ∃ x : M, F.val.Evalb ![x, y] := by
  simp [surjectiveSentence]

namespace GraphMorphism

variable {T} {C D : PredicateCategory T}

def sectionGraph (f : GraphMorphism T C D) : Graph :=
  eventualGraph (TypedChoice.sectionIndex (SyntacticSearch.searchIndex f.graph))

theorem sectionGraph_sound (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (y x : M)
    (h : f.sectionGraph.val.Evalb ![y, x]) : f.graph.val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact (f.programClass_model M x y).mp
    (TypedChoice.sectionIndex_sound (SyntacticSearch.searchIndex f.graph) y x h)

theorem sectionGraph_domain (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (y : M) :
    (∃ x : M, f.sectionGraph.val.Evalb ![y, x]) ↔
      ∃ x : M, f.graph.val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [sectionGraph, TypedChoice.sectionIndex_domain]
  exact exists_congr (fun x => f.programClass_model M x y)

/-- Provable surjectivity makes witness search a total represented section. -/
def selectedSection (f : GraphMorphism T C D) (hs : T ⊢ surjectiveSentence D f.graph) :
    GraphMorphism T D C where
  graph := f.sectionGraph
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro y x hyx
    have hxy := f.sectionGraph_sound M y x hyx
    exact (f.support_model M x y hxy).symm
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    have hsurj := consequence_iff.mp (Theory.Proof.sound hs) M inferInstance
    rw [models_iff, surjectiveSentence_eval] at hsurj
    rw [models_iff, totalSentence_eval]
    intro y hy
    obtain ⟨x, hx⟩ := (f.sectionGraph_domain M y).mpr (hsurj y hy)
    refine ⟨x, hx, ?_⟩
    intro x' hx'
    exact eventualGraph_output_unique _ y x' x hx' hx

theorem section_comp (f : GraphMorphism T C D) (hs : T ⊢ surjectiveSentence D f.graph) :
    representedArrow T (f.selectedSection hs) ≫ representedArrow T f =
      𝟙 (D : PredicateCategory T) := by
  apply Quotient.sound
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro y z
  change (comp f.graph f.sectionGraph).val.Evalb ![y, z] ↔
    (identityGraph D).val.Evalb ![y, z]
  rw [comp_eval, identityGraph_eval]
  constructor
  · rintro ⟨x, hsx, hfx⟩
    have hfy := f.sectionGraph_sound M y x hsx
    exact ⟨((f.selectedSection hs).support_model M y x hsx).1,
      (f.total_model M x (f.support_model M x y hfy).1).unique hfx hfy⟩
  · rintro ⟨hy, he⟩
    subst z
    obtain ⟨x, hx, _⟩ := (f.selectedSection hs).total_model M y hy
    exact ⟨x, hx, f.sectionGraph_sound M y x hx⟩

theorem isSplitEpi_of_surjective (f : GraphMorphism T C D)
    (hs : T ⊢ surjectiveSentence D f.graph) : IsSplitEpi (representedArrow T f) :=
  ⟨⟨⟨representedArrow T (f.selectedSection hs), f.section_comp hs⟩⟩⟩

end GraphMorphism

def imageCarrier (F : Graph) : Carrier := .mkSigma “y. ∃ x, !F.val x y”

@[simp] theorem imageCarrier_eval {M : Type} [ORingStructure M] (F : Graph) (y : M) :
    (imageCarrier F).val.Evalb ![y] ↔ ∃ x : M, F.val.Evalb ![x, y] := by
  simp [imageCarrier]

namespace GraphMorphism

variable {T} {C D : PredicateCategory T}

theorem imageInclusionProof (f : GraphMorphism T C D) :
    T ⊢ inclusionSentence (imageCarrier f.graph) D := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, inclusionSentence_eval]
  intro y hy
  obtain ⟨x, hxy⟩ := (imageCarrier_eval f.graph y).mp hy
  exact (f.support_model M x y hxy).2

def corestriction (f : GraphMorphism T C D) : GraphMorphism T C (imageCarrier f.graph) where
  graph := f.graph
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y hxy
    exact ⟨(f.support_model M x y hxy).1, (imageCarrier_eval f.graph y).mpr ⟨x, hxy⟩⟩
  total := f.total

theorem corestriction_surjective (f : GraphMorphism T C D) :
    T ⊢ surjectiveSentence (imageCarrier f.graph) f.corestriction.graph := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, surjectiveSentence_eval]
  intro y hy
  exact (imageCarrier_eval f.graph y).mp hy

theorem image_factor (f : GraphMorphism T C D) :
    representedArrow T f.corestriction ≫ representedArrow T (inclusion f.imageInclusionProof) =
      representedArrow T f := by
  apply Quotient.sound
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  change (comp (identityGraph (imageCarrier f.graph)) f.graph).val.Evalb ![x, y] ↔ _
  rw [comp_eval]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    obtain ⟨_, he⟩ := (identityGraph_eval (imageCarrier f.graph) z y).mp hzy
    subst z
    exact hxz
  · intro hxy
    exact ⟨y, hxy, (identityGraph_eval (imageCarrier f.graph) y y).mpr
      ⟨(imageCarrier_eval f.graph y).mpr ⟨x, hxy⟩, rfl⟩⟩

/-- The image predicate gives a strong-epi/mono factorization. Its left
factor is a represented witness-search split epimorphism. -/
def imageFactorisation (f : GraphMorphism T C D) :
    StrongEpiMonoFactorisation (representedArrow T f) := by
  letI := f.corestriction.isSplitEpi_of_surjective f.corestriction_surjective
  exact
    { I := imageCarrier f.graph
      m := representedArrow T (inclusion f.imageInclusionProof)
      e := representedArrow T f.corestriction
      fac := f.image_factor }

end GraphMorphism

instance predicateStrongEpiMonoFactorisations :
    HasStrongEpiMonoFactorisations (PredicateCategory T) := by
  constructor
  intro C D f
  induction f using Quotient.inductionOn with
  | _ f => exact ⟨f.imageFactorisation⟩

instance totalSplitStrongEpiMonoFactorisations :
    HasStrongEpiMonoFactorisations (TotalSplit T) :=
  (realization T).hasStrongEpiMonoFactorisations_imp_of_isEquivalence

/-- The displayed existential image is a categorical image, before any
choice of a global image construction. -/
def representedImage {C D : PredicateCategory T} (f : GraphMorphism T C D) :
    ImageFactorisation (representedArrow T f) :=
  ⟨f.imageFactorisation.toMonoFactorisation, f.imageFactorisation.toMonoIsImage⟩

/-- A represented monomorphism is isomorphic over its codomain to the
inclusion of its existential image predicate. -/
theorem represented_mono_image_iso {C D : PredicateCategory T}
    (f : GraphMorphism T C D) [Mono (representedArrow T f)] :
    ∃ i : C ≅ (imageCarrier f.graph : PredicateCategory T),
      i.hom ≫ representedArrow T (GraphMorphism.inclusion f.imageInclusionProof) =
        representedArrow T f := by
  let F := f.imageFactorisation
  let : Mono F.e := by
    constructor
    intro Z u v huv
    apply (cancel_mono (representedArrow T f)).mp
    rw [← F.fac]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ F.m) huv
  let : IsIso F.e := isIso_of_mono_of_strongEpi F.e
  exact ⟨asIso F.e, F.fac⟩

/-- Every subobject is represented, over its carrier, by a predicate
inclusion with a theory proof of implication. -/
theorem subobject_is_predicate_inclusion {C D : PredicateCategory T} (m : C ⟶ D) [Mono m] :
    ∃ (P : Carrier) (h : T ⊢ inclusionSentence P D) (i : C ≅ (P : PredicateCategory T)),
      i.hom ≫ representedArrow T (GraphMorphism.inclusion h) = m := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep m
  have hf' : representedArrow T f = m := hf
  let : Mono (representedArrow T f) := by rw [hf']; infer_instance
  obtain ⟨i, hi⟩ := represented_mono_image_iso T f
  exact ⟨imageCarrier f.graph, f.imageInclusionProof, i, hi.trans hf'⟩

theorem restriction_precomp_iso {K : Type*} [Category K] [RestrictionCategory K]
    {X Y Z : K} (i : X ≅ Y) (f : Y ⟶ Z) :
    rst (i.hom ≫ f) = i.hom ≫ rst f ≫ i.inv := by
  have h := congrArg (fun k => k ≫ i.inv) (rst_comp i.hom f)
  simpa only [Category.assoc, i.hom_inv_id, Category.comp_id] using h

/-- Partial inverses transport along total categorical isomorphisms. -/
theorem transport_partial_inverse {K : Type*} [Category K] [RestrictionCategory K]
    {A B X Y : K} (a : A ≅ X) (b : B ≅ Y) (f : A ⟶ B) (r : B ⟶ A)
    (hfr : f ≫ r = 𝟙 A) (hrf : r ≫ f = rst r) :
    let g := a.inv ≫ f ≫ b.hom
    let s := b.inv ≫ r ≫ a.hom
    g ≫ s = 𝟙 X ∧ s ≫ g = rst s := by
  dsimp only
  constructor
  · simp only [Category.assoc, b.hom_inv_id_assoc]
    rw [← Category.assoc f, hfr, Category.id_comp, a.inv_hom_id]
  · calc
      (b.inv ≫ r ≫ a.hom) ≫ (a.inv ≫ f ≫ b.hom) = b.inv ≫ rst r ≫ b.hom := by
        simp only [Category.assoc, a.hom_inv_id_assoc]
        rw [← Category.assoc r, hrf]
      _ = rst (b.inv ≫ r) := (restriction_precomp_iso b.symm r).symm
      _ = rst ((b.inv ≫ r) ≫ a.hom) :=
        (rst_comp_of_isTotal (b.inv ≫ r) (iso_total a)).symm
      _ = rst (b.inv ≫ r ≫ a.hom) := by rw [Category.assoc]

theorem represented_mono_partial_inverse {C D : PredicateCategory T}
    (f : GraphMorphism T C D) [Mono (representedArrow T f)] :
    ∃ r : (interpretedObject T D).obj ⟶ (interpretedObject T C).obj,
      ((realization T).map (representedArrow T f)).hom ≫ r =
        𝟙 (interpretedObject T C).obj ∧
      r ≫ ((realization T).map (representedArrow T f)).hom = rst r := by
  obtain ⟨i, hi⟩ := represented_mono_image_iso T f
  let J : (interpretedObject T C).obj ≅
      (interpretedObject T (imageCarrier f.graph)).obj :=
    (wideSubcategoryInclusion (isTotal (C := SplitObject (CodedProgramCategory T)))).mapIso
      ((realization T).mapIso i)
  let a := J.symm
  let b := Iso.refl (interpretedObject T D).obj
  let j := (GraphMorphism.inclusion f.imageInclusionProof).toSplit
  let ri := inclusionReverse f.imageInclusionProof
  have hmap : J.hom ≫ j = ((realization T).map (representedArrow T f)).hom := by
    have hh := congrArg (realization T).map hi
    rw [Functor.map_comp] at hh
    exact congrArg (fun k : interpretedObject T C ⟶ interpretedObject T D => k.hom) hh
  have hconj : a.inv ≫ j ≫ b.hom =
      ((realization T).map (representedArrow T f)).hom := by
    change J.hom ≫ j ≫ 𝟙 (interpretedObject T D).obj = _
    rw [Category.comp_id, hmap]
  have h := transport_partial_inverse a b j ri
    (inclusion_forward_reverse f.imageInclusionProof)
    (inclusion_reverse_forward f.imageInclusionProof)
  refine ⟨b.inv ≫ ri ≫ a.hom, ?_, ?_⟩
  · simpa only [hconj] using h.1
  · simpa only [hconj] using h.2

theorem realized_mono_partial_inverse {C D : PredicateCategory T}
    (f : C ⟶ D) [Mono f] :
    ∃ r : (interpretedObject T D).obj ⟶ (interpretedObject T C).obj,
      ((realization T).map f).hom ≫ r = 𝟙 (interpretedObject T C).obj ∧
      r ≫ ((realization T).map f).hom = rst r := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep f
  have hg' : representedArrow T g = f := hg
  let : Mono (representedArrow T g) := by rw [hg']; infer_instance
  simpa only [hg'] using represented_mono_partial_inverse T g

/-- Every monomorphism in the total restriction splitting has a partial
inverse in the actual restriction splitting. -/
theorem totalSplit_mono_partial_inverse {X Y : TotalSplit T} (m : X ⟶ Y) [Mono m] :
    ∃ r : Y.obj ⟶ X.obj, m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r := by
  let E := predicateEquivalence T
  let C := E.inverse.obj X
  let D := E.inverse.obj Y
  let a := E.counitIso.app X
  let b := E.counitIso.app Y
  let n := a.hom ≫ m ≫ b.inv
  let f : C ⟶ D := (realization T).preimage n
  have hn : (realization T).map f = n := (realization T).map_preimage n
  let : Mono n := by dsimp [n]; infer_instance
  let : Mono f := (realization T).mono_of_mono_map (by rw [hn]; infer_instance)
  obtain ⟨r, hfr, hrf⟩ := realized_mono_partial_inverse T f
  let A : (interpretedObject T C).obj ≅ X.obj :=
    (wideSubcategoryInclusion (isTotal (C := SplitObject (CodedProgramCategory T)))).mapIso a
  let B : (interpretedObject T D).obj ≅ Y.obj :=
    (wideSubcategoryInclusion (isTotal (C := SplitObject (CodedProgramCategory T)))).mapIso b
  have hconj : A.inv ≫ ((realization T).map f).hom ≫ B.hom = m.hom := by
    rw [hn]
    change a.inv.hom ≫ ((a.hom ≫ m ≫ b.inv).hom) ≫ b.hom.hom = m.hom
    have hh : a.inv ≫ (a.hom ≫ m ≫ b.inv) ≫ b.hom = m := by simp
    exact congrArg (fun k : X ⟶ Y => k.hom) hh
  refine ⟨B.inv ≫ r ≫ A.hom, ?_, ?_⟩
  · have h := (transport_partial_inverse A B ((realization T).map f).hom r hfr hrf).1
    simpa only [hconj] using h
  · have h := (transport_partial_inverse A B ((realization T).map f).hom r hfr hrf).2
    simpa only [hconj] using h

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates
