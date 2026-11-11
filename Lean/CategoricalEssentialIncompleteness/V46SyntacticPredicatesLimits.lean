/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRelations
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Finite limits of provably total predicate graphs -/

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

def terminalCarrier : Carrier := .mkSigma “x. x = 0”

@[simp] theorem terminalCarrier_eval {M : Type} [ORingStructure M] (x : M) :
    terminalCarrier.val.Evalb ![x] ↔ x = 0 := by simp [terminalCarrier]

def terminalGraph (C : Carrier) : Graph := .mkSigma “x y. !C.val x ∧ y = 0”

@[simp] theorem terminalGraph_eval (C : Carrier)
    {M : Type} [ORingStructure M] (x y : M) :
    (terminalGraph C).val.Evalb ![x, y] ↔ C.val.Evalb ![x] ∧ y = 0 := by
  simp [terminalGraph]

def terminalMap (C : PredicateCategory T) : GraphMorphism T C terminalCarrier where
  graph := terminalGraph C
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y h
    have h' := (terminalGraph_eval C x y).mp h
    exact ⟨h'.1, (terminalCarrier_eval y).mpr h'.2⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro x hx
    refine ⟨0, (terminalGraph_eval C x 0).mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact ((terminalGraph_eval C x y).mp hy).2

@[simp] theorem terminalMap_eval (C : PredicateCategory T)
    {M : Type} [ORingStructure M] (x y : M) :
    (terminalMap T C).graph.val.Evalb ![x, y] ↔ C.val.Evalb ![x] ∧ y = 0 :=
  terminalGraph_eval C x y

def terminalIsTerminal : IsTerminal (C := PredicateCategory T) terminalCarrier :=
  IsTerminal.ofUniqueHom (fun C => representedArrow T (terminalMap T C)) (by
    intro C f
    apply hom_ext T
    intro M _ _ x y
    rw [relation_class, terminalMap_eval]
    constructor
    · intro h
      exact ⟨(relation_support T f M x y h).1,
        (terminalCarrier_eval y).mp (relation_support T f M x y h).2⟩
    · rintro ⟨hx, rfl⟩
      obtain ⟨y, hy, _⟩ := relation_total T f M x hx
      have he := (terminalCarrier_eval y).mp (relation_support T f M x y hy).2
      simpa only [he] using hy)

instance predicateHasTerminal : HasTerminal (PredicateCategory T) :=
  (terminalIsTerminal T).hasTerminal

def productCarrier (C D : Carrier) : Carrier :=
  .mkSigma “z. ∃ x y, !natPairFormula.val z x y ∧ !C.val x ∧ !D.val y”

@[simp] theorem productCarrier_eval {M : Type} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (C D : Carrier) (z : M) :
    (productCarrier C D).val.Evalb ![z] ↔
      ∃ x y, z = ⟪x, y⟫ ∧ C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  simp [productCarrier]

def fstGraph (C D : Carrier) : Graph :=
  .mkSigma “z x. ∃ y, !natPairFormula.val z x y ∧ !C.val x ∧ !D.val y”

def sndGraph (C D : Carrier) : Graph :=
  .mkSigma “z y. ∃ x, !natPairFormula.val z x y ∧ !C.val x ∧ !D.val y”

@[simp] theorem fstGraph_eval (C D : Carrier)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z x : M) :
    (fstGraph C D).val.Evalb ![z, x] ↔
      ∃ y, z = ⟪x, y⟫ ∧ C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  simp [fstGraph]

@[simp] theorem sndGraph_eval (C D : Carrier)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z y : M) :
    (sndGraph C D).val.Evalb ![z, y] ↔
      ∃ x, z = ⟪x, y⟫ ∧ C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  simp [sndGraph]

def productFst (C D : PredicateCategory T) : GraphMorphism T (productCarrier C D) C where
  graph := fstGraph C D
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z x h
    obtain ⟨y, he, hc, hd⟩ := (fstGraph_eval C D z x).mp h
    exact ⟨(productCarrier_eval C D z).mpr ⟨x, y, he, hc, hd⟩, hc⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    obtain ⟨x, y, he, hc, hd⟩ := (productCarrier_eval C D z).mp hz
    refine ⟨x, (fstGraph_eval C D z x).mpr ⟨y, he, hc, hd⟩, ?_⟩
    intro x' hx'
    obtain ⟨y', he', _, _⟩ := (fstGraph_eval C D z x').mp hx'
    exact ((pair_eq_pair_iff x' y' x y).mp (he'.symm.trans he)).1

def productSnd (C D : PredicateCategory T) : GraphMorphism T (productCarrier C D) D where
  graph := sndGraph C D
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z y h
    obtain ⟨x, he, hc, hd⟩ := (sndGraph_eval C D z y).mp h
    exact ⟨(productCarrier_eval C D z).mpr ⟨x, y, he, hc, hd⟩, hd⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    obtain ⟨x, y, he, hc, hd⟩ := (productCarrier_eval C D z).mp hz
    refine ⟨y, (sndGraph_eval C D z y).mpr ⟨x, he, hc, hd⟩, ?_⟩
    intro y' hy'
    obtain ⟨x', he', _, _⟩ := (sndGraph_eval C D z y').mp hy'
    exact ((pair_eq_pair_iff x' y' x y).mp (he'.symm.trans he)).2

@[simp] theorem productFst_eval (C D : PredicateCategory T)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z x : M) :
    (productFst T C D).graph.val.Evalb ![z, x] ↔
      ∃ y, z = ⟪x, y⟫ ∧ C.val.Evalb ![x] ∧ D.val.Evalb ![y] :=
  fstGraph_eval C D z x

@[simp] theorem productSnd_eval (C D : PredicateCategory T)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (z y : M) :
    (productSnd T C D).graph.val.Evalb ![z, y] ↔
      ∃ x, z = ⟪x, y⟫ ∧ C.val.Evalb ![x] ∧ D.val.Evalb ![y] :=
  sndGraph_eval C D z y

def pairedGraph (F G : Graph) : Graph :=
  .mkSigma “x z. ∃ y w, !F.val x y ∧ !G.val x w ∧ !natPairFormula.val z y w”

@[simp] theorem pairedGraph_eval (F G : Graph)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x z : M) :
    (pairedGraph F G).val.Evalb ![x, z] ↔
      ∃ y w, F.val.Evalb ![x, y] ∧ G.val.Evalb ![x, w] ∧ z = ⟪y, w⟫ := by
  simp [pairedGraph]

def productLift {A C D : PredicateCategory T} (f : A ⟶ C) (g : A ⟶ D) :
    GraphMorphism T A (productCarrier C D) where
  graph := pairedGraph (chosenGraph T f).graph (chosenGraph T g).graph
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x z h
    obtain ⟨y, w, hfy, hgw, he⟩ :=
      (pairedGraph_eval (chosenGraph T f).graph (chosenGraph T g).graph x z).mp h
    have hf := (chosenGraph_eval T f M x y).mp hfy
    have hg := (chosenGraph_eval T g M x w).mp hgw
    exact ⟨(relation_support T f M x y hf).1,
      (productCarrier_eval C D z).mpr ⟨y, w, he,
        (relation_support T f M x y hf).2, (relation_support T g M x w hg).2⟩⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro x hx
    obtain ⟨y, hy, _⟩ := relation_total T f M x hx
    obtain ⟨w, hw, _⟩ := relation_total T g M x hx
    refine ⟨⟪y, w⟫, ?_, ?_⟩
    · exact (pairedGraph_eval (chosenGraph T f).graph (chosenGraph T g).graph x ⟪y, w⟫).mpr
        ⟨y, w, (chosenGraph_eval T f M x y).mpr hy,
          (chosenGraph_eval T g M x w).mpr hw, rfl⟩
    · intro z hz
      obtain ⟨y', w', hfy', hgw', he⟩ :=
        (pairedGraph_eval (chosenGraph T f).graph (chosenGraph T g).graph x z).mp hz
      have hey := relation_functional T f M x y' y
        ((chosenGraph_eval T f M x y').mp hfy') hy
      have hew := relation_functional T g M x w' w
        ((chosenGraph_eval T g M x w').mp hgw') hw
      simpa only [hey, hew] using he

@[simp] theorem productLift_eval {A C D : PredicateCategory T} (f : A ⟶ C) (g : A ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x z : M) :
    (productLift T f g).graph.val.Evalb ![x, z] ↔
      ∃ y w, relation T f M x y ∧ relation T g M x w ∧ z = ⟪y, w⟫ := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (pairedGraph (chosenGraph T f).graph (chosenGraph T g).graph).val.Evalb ![x, z] ↔ _
  simp only [pairedGraph_eval, chosenGraph_eval]

theorem productLift_fst {A C D : PredicateCategory T} (f : A ⟶ C) (g : A ⟶ D) :
    representedArrow T (productLift T f g) ≫ representedArrow T (productFst T C D) = f := by
  apply hom_ext T
  intro M _ _ x y
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simp only [relation_comp, relation_class, productLift_eval, productFst_eval]
  constructor
  · rintro ⟨z, ⟨y', w, hfy, _, hz⟩, w', hz', _, _⟩
    have he := ((pair_eq_pair_iff y' w y w').mp (hz.symm.trans hz')).1
    simpa only [he] using hfy
  · intro hfy
    obtain ⟨w, hgw, _⟩ := relation_total T g M x (relation_support T f M x y hfy).1
    exact ⟨⟪y, w⟫, ⟨y, w, hfy, hgw, rfl⟩,
      w, rfl, (relation_support T f M x y hfy).2, (relation_support T g M x w hgw).2⟩

theorem productLift_snd {A C D : PredicateCategory T} (f : A ⟶ C) (g : A ⟶ D) :
    representedArrow T (productLift T f g) ≫ representedArrow T (productSnd T C D) = g := by
  apply hom_ext T
  intro M _ _ x w
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simp only [relation_comp, relation_class, productLift_eval, productSnd_eval]
  constructor
  · rintro ⟨z, ⟨y, w', _, hgw, hz⟩, y', hz', _, _⟩
    have he := ((pair_eq_pair_iff y w' y' w).mp (hz.symm.trans hz')).2
    simpa only [he] using hgw
  · intro hgw
    obtain ⟨y, hfy, _⟩ := relation_total T f M x (relation_support T g M x w hgw).1
    exact ⟨⟪y, w⟫, ⟨y, w, hfy, hgw, rfl⟩,
      y, rfl, (relation_support T f M x y hfy).2, (relation_support T g M x w hgw).2⟩

def productIsLimit (C D : PredicateCategory T) :
    IsLimit (BinaryFan.mk (representedArrow T (productFst T C D))
      (representedArrow T (productSnd T C D))) :=
  BinaryFan.IsLimit.mk _ (fun f g => representedArrow T (productLift T f g))
    (productLift_fst T) (productLift_snd T) (by
      intro A f g m hmf hmg
      apply hom_ext T
      intro M _ _ x z
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
      rw [relation_class, productLift_eval]
      constructor
      · intro hm
        obtain ⟨y, w, hz, hc, hd⟩ := (productCarrier_eval C D z).mp
          (relation_support T m M x z hm).2
        refine ⟨y, w, ?_, ?_, hz⟩
        · rw [← hmf, relation_comp]
          exact ⟨z, hm, (relation_class T (productFst T C D) M z y).mpr
            ((productFst_eval T C D z y).mpr ⟨w, hz, hc, hd⟩)⟩
        · rw [← hmg, relation_comp]
          exact ⟨z, hm, (relation_class T (productSnd T C D) M z w).mpr
            ((productSnd_eval T C D z w).mpr ⟨y, hz, hc, hd⟩)⟩
      · rintro ⟨y, w, hf, hg, hz⟩
        obtain ⟨z', hm, _⟩ := relation_total T m M x (relation_support T f M x y hf).1
        obtain ⟨y', w', hz', hc, hd⟩ := (productCarrier_eval C D z').mp
          (relation_support T m M x z' hm).2
        have hf' : relation T f M x y' := by
          rw [← hmf, relation_comp]
          exact ⟨z', hm, (relation_class T (productFst T C D) M z' y').mpr
            ((productFst_eval T C D z' y').mpr ⟨w', hz', hc, hd⟩)⟩
        have hg' : relation T g M x w' := by
          rw [← hmg, relation_comp]
          exact ⟨z', hm, (relation_class T (productSnd T C D) M z' w').mpr
            ((productSnd_eval T C D z' w').mpr ⟨y', hz', hc, hd⟩)⟩
        have hey := relation_functional T f M x y' y hf' hf
        have hew := relation_functional T g M x w' w hg' hg
        have hez : z' = z := by
          rw [hey, hew] at hz'
          exact hz'.trans hz.symm
        simpa only [hez] using hm)

instance predicateHasBinaryProducts : HasBinaryProducts (PredicateCategory T) := by
  let : ∀ {C D : PredicateCategory T}, HasLimit (CategoryTheory.Limits.pair C D) :=
    fun {C D} => ⟨⟨⟨_, productIsLimit T C D⟩⟩⟩
  exact hasBinaryProducts_of_hasLimit_pair (PredicateCategory T)

instance predicateHasFiniteProducts : HasFiniteProducts (PredicateCategory T) :=
  hasFiniteProducts_of_has_binary_and_terminal


def equalizerCarrier {C D : PredicateCategory T} (f g : C ⟶ D) : Carrier :=
  .mkSigma “x. ∃ y, !(chosenGraph T f).graph.val x y ∧ !(chosenGraph T g).graph.val x y”

@[simp] theorem equalizerCarrier_eval {C D : PredicateCategory T} (f g : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) :
    (equalizerCarrier T f g).val.Evalb ![x] ↔
      ∃ y, relation T f M x y ∧ relation T g M x y := by
  simp [equalizerCarrier]

theorem equalizerInclusionProof {C D : PredicateCategory T} (f g : C ⟶ D) :
    T ⊢ inclusionSentence (equalizerCarrier T f g) C := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, inclusionSentence_eval]
  intro x hx
  obtain ⟨y, hf, _⟩ := (equalizerCarrier_eval T f g M x).mp hx
  exact (relation_support T f M x y hf).1

def equalizerInclusion {C D : PredicateCategory T} (f g : C ⟶ D) :
    @Quiver.Hom (PredicateCategory T) inferInstance (equalizerCarrier T f g) C :=
  representedArrow T (GraphMorphism.inclusion (equalizerInclusionProof T f g))

@[simp] theorem equalizerInclusion_eval {C D : PredicateCategory T} (f g : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    relation T (equalizerInclusion T f g) M x y ↔
      (equalizerCarrier T f g).val.Evalb ![x] ∧ y = x := by
  rw [equalizerInclusion, relation_class]
  exact GraphMorphism.identityGraph_eval _ x y

theorem equalizer_condition {C D : PredicateCategory T} (f g : C ⟶ D) :
    equalizerInclusion T f g ≫ f = equalizerInclusion T f g ≫ g := by
  apply hom_ext T
  intro M _ _ x y
  simp only [relation_comp, equalizerInclusion_eval]
  constructor
  · rintro ⟨z, ⟨hx, he⟩, hf⟩
    subst z
    obtain ⟨w, hfw, hgw⟩ := (equalizerCarrier_eval T f g M x).mp hx
    have hew := relation_functional T f M x y w hf hfw
    exact ⟨x, ⟨hx, rfl⟩, by simpa only [hew] using hgw⟩
  · rintro ⟨z, ⟨hx, he⟩, hg⟩
    subst z
    obtain ⟨w, hfw, hgw⟩ := (equalizerCarrier_eval T f g M x).mp hx
    have hew := relation_functional T g M x y w hg hgw
    exact ⟨x, ⟨hx, rfl⟩, by simpa only [hew] using hfw⟩

def equalizerLift {A C D : PredicateCategory T} (f g : C ⟶ D) (h : A ⟶ C)
    (hh : h ≫ f = h ≫ g) : GraphMorphism T A (equalizerCarrier T f g) where
  graph := (chosenGraph T h).graph
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y hxy
    have hrel := (chosenGraph_eval T h M x y).mp hxy
    have hc := (relation_support T h M x y hrel).2
    obtain ⟨z, hf, _⟩ := relation_total T f M y hc
    have hcomp : relation T (h ≫ g) M x z := by
      rw [← hh, relation_comp]
      exact ⟨y, hrel, hf⟩
    obtain ⟨y', hy', hg⟩ := (relation_comp T h g M x z).mp hcomp
    have he := relation_functional T h M x y' y hy' hrel
    exact ⟨(relation_support T h M x y hrel).1,
      (equalizerCarrier_eval T f g M y).mpr
        ⟨z, hf, by simpa only [he] using hg⟩⟩
  total := (chosenGraph T h).total

@[simp] theorem equalizerLift_eval {A C D : PredicateCategory T} (f g : C ⟶ D) (h : A ⟶ C)
    (hh : h ≫ f = h ≫ g) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    (equalizerLift T f g h hh).graph.val.Evalb ![x, y] ↔ relation T h M x y :=
  chosenGraph_eval T h M x y

theorem equalizerLift_fac {A C D : PredicateCategory T} (f g : C ⟶ D) (h : A ⟶ C)
    (hh : h ≫ f = h ≫ g) :
    representedArrow T (equalizerLift T f g h hh) ≫ equalizerInclusion T f g = h := by
  apply hom_ext T
  intro M _ _ x y
  simp only [relation_comp, relation_class, equalizerLift_eval, equalizerInclusion_eval]
  constructor
  · rintro ⟨z, hhz, _, he⟩
    simpa only [he] using hhz
  · intro hhy
    have hs := (equalizerLift T f g h hh).support_model M x y
      ((equalizerLift_eval T f g h hh M x y).mpr hhy)
    exact ⟨y, hhy, hs.2, rfl⟩

def equalizerIsLimit {C D : PredicateCategory T} (f g : C ⟶ D) :
    IsLimit (Fork.ofι (equalizerInclusion T f g) (equalizer_condition T f g)) := by
  let : Mono (equalizerInclusion T f g) := inclusion_mono (equalizerInclusionProof T f g)
  refine Fork.IsLimit.mk _
    (fun s => representedArrow T (equalizerLift T f g s.ι s.condition))
    (fun s => equalizerLift_fac T f g s.ι s.condition) ?_
  intro s m hm
  apply (cancel_mono (equalizerInclusion T f g)).mp
  exact hm.trans (equalizerLift_fac T f g s.ι s.condition).symm

instance predicateHasEqualizers : HasEqualizers (PredicateCategory T) := by
  let : ∀ {C D : PredicateCategory T} {f g : C ⟶ D},
      HasLimit (parallelPair f g) := fun {C D f g} => ⟨⟨⟨_, equalizerIsLimit T f g⟩⟩⟩
  exact hasEqualizers_of_hasLimit_parallelPair (PredicateCategory T)

instance predicateHasFiniteLimits : HasFiniteLimits (PredicateCategory T) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance totalSplitHasFiniteLimits : HasFiniteLimits (TotalSplit T) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (predicateEquivalence T).inverse

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates
