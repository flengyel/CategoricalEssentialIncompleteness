/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSearch
import CategoricalEssentialIncompleteness.SyntacticModel
import CategoricalEssentialIncompleteness.RestrictionSplitting
import Mathlib.CategoryTheory.Widesubcategory

/-! # Arithmetic predicates and total morphisms in the restriction splitting -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates

/-- A carrier is an arbitrary one-variable Sigma-one formula. -/
abbrev Carrier := 𝚺₁.Semisentence 1

def supportSentence (C D : Carrier) (F : Graph) : ArithmeticSentence :=
  “∀ x y, !F.val x y → !C.val x ∧ !D.val y”

def totalSentence (C : Carrier) (F : Graph) : ArithmeticSentence :=
  “∀ x, !C.val x → ∃! y, !F.val x y”

@[simp] theorem supportSentence_eval {M : Type} [ORingStructure M]
    (C D : Carrier) (F : Graph) :
    (supportSentence C D F).Evalb (M := M) ![] ↔
      ∀ x y : M, F.val.Evalb ![x, y] → C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  simp [supportSentence]

@[simp] theorem totalSentence_eval {M : Type} [ORingStructure M]
    (C : Carrier) (F : Graph) :
    (totalSentence C F).Evalb (M := M) ![] ↔
      ∀ x : M, C.val.Evalb ![x] → ∃! y : M, F.val.Evalb ![x, y] := by
  simp [totalSentence]

/-- The two proof obligations are precisely support and unique totality
in the predicate presentation. -/
structure GraphMorphism (T : ArithmeticTheory) (C D : Carrier) where
  graph : Graph
  support : T ⊢ supportSentence C D graph
  total : T ⊢ totalSentence C graph

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

namespace GraphMorphism

variable {T} {C D E : Carrier}

omit [𝗣𝗔 ⪯ T] in
theorem support_model (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M)
    (h : f.graph.val.Evalb ![x, y]) : C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  have hs := consequence_iff.mp (Theory.Proof.sound f.support) M inferInstance
  rw [models_iff, supportSentence_eval] at hs
  exact hs x y h

omit [𝗣𝗔 ⪯ T] in
theorem total_model (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M)
    (h : C.val.Evalb ![x]) : ∃! y : M, f.graph.val.Evalb ![x, y] := by
  have ht := consequence_iff.mp (Theory.Proof.sound f.total) M inferInstance
  rw [models_iff, totalSentence_eval] at ht
  exact ht x h

/-- Unique totality on the carrier and support imply global functionality. -/
theorem functional (f : GraphMorphism T C D) : T ⊢ functionalSentence f.graph := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact (f.total_model M x (f.support_model M x y hy).1).unique hy hz

def identityGraph (C : Carrier) : Graph := .mkSigma “x y. !C.val x ∧ y = x”

@[simp] theorem identityGraph_eval {M : Type} [ORingStructure M]
    (C : Carrier) (x y : M) :
    (identityGraph C).val.Evalb ![x, y] ↔ C.val.Evalb ![x] ∧ y = x := by
  simp [identityGraph]

def identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C : Carrier) : GraphMorphism T C C where
  graph := identityGraph C
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y h
    obtain ⟨hc, rfl⟩ := (identityGraph_eval C x y).mp h
    exact ⟨hc, hc⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro x hx
    refine ⟨x, (identityGraph_eval C x x).mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact ((identityGraph_eval C x y).mp hy).2

def composition (f : GraphMorphism T C D) (g : GraphMorphism T D E) :
    GraphMorphism T C E where
  graph := comp g.graph f.graph
  support := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x z hxz
    obtain ⟨y, hxy, hyz⟩ := (comp_eval g.graph f.graph ![x, z]).mp hxz
    exact ⟨(f.support_model M x y hxy).1, (g.support_model M y z hyz).2⟩
  total := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    rw [models_iff, totalSentence_eval]
    intro x hx
    obtain ⟨y, hy, hfy⟩ := f.total_model M x hx
    obtain ⟨z, hz, hgz⟩ := g.total_model M y (f.support_model M x y hy).2
    refine ⟨z, (comp_eval g.graph f.graph ![x, z]).mpr ⟨y, hy, hz⟩, ?_⟩
    intro z' hz'
    obtain ⟨y', hxy', hyz'⟩ := (comp_eval g.graph f.graph ![x, z']).mp hz'
    have he := hfy y' hxy'
    subst y'
    exact hgz z' hyz'

def equalitySetoid (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C D : Carrier) :
    Setoid (GraphMorphism T C D) where
  r f g := Uniform T f.graph g.graph
  iseqv := ⟨fun f => uniform_refl T f.graph, fun h => uniform_symm h,
    fun h k => uniform_trans h k⟩

end GraphMorphism

/-- Objects retain their defining predicates, including provably equivalent
but syntactically distinct carrier formulas. -/
def PredicateCategory (_T : ArithmeticTheory) := Carrier

abbrev Hom (C D : PredicateCategory T) := Quotient (GraphMorphism.equalitySetoid T C D)

def classOfGraph {C D : PredicateCategory T} (f : GraphMorphism T C D) : Hom T C D :=
  Quotient.mk _ f

theorem classOfGraph_eq_iff {C D : PredicateCategory T} (f g : GraphMorphism T C D) :
    classOfGraph T f = classOfGraph T g ↔ Uniform T f.graph g.graph :=
  by
    constructor
    · exact Quotient.exact
    · intro h
      apply Quotient.sound
      exact h

def compose {C D E : PredicateCategory T} (f : Hom T C D) (g : Hom T D E) :
    Hom T C E :=
  Quotient.lift₂ (fun f g => classOfGraph T (f.composition g))
    (fun _ _ _ _ hf hg => Quotient.sound (uniform_comp_congr hg hf)) f g

instance predicateCategory : Category (PredicateCategory T) where
  Hom := Hom T
  id C := classOfGraph T (GraphMorphism.identity T C)
  comp f g := compose T f g
  id_comp f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      apply complete.{0} T
      intro M _ hM
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
      let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      rw [models_iff, uniformSentence_eval]
      intro x z
      change (comp f.graph (GraphMorphism.identityGraph _)).val.Evalb ![x, z] ↔ _
      rw [comp_eval]
      constructor
      · rintro ⟨y, hy, hz⟩
        obtain ⟨_, rfl⟩ := (GraphMorphism.identityGraph_eval _ x y).mp hy
        exact hz
      · intro hz
        exact ⟨x, (GraphMorphism.identityGraph_eval _ x x).mpr
          ⟨(f.support_model M x z hz).1, rfl⟩, hz⟩
  comp_id f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      apply complete.{0} T
      intro M _ hM
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
      let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      rw [models_iff, uniformSentence_eval]
      intro x z
      change (comp (GraphMorphism.identityGraph _) f.graph).val.Evalb ![x, z] ↔ _
      rw [comp_eval]
      constructor
      · rintro ⟨y, hy, hz⟩
        obtain ⟨_, rfl⟩ := (GraphMorphism.identityGraph_eval _ y z).mp hz
        exact hy
      · intro hz
        exact ⟨z, hz, (GraphMorphism.identityGraph_eval _ z z).mpr
          ⟨(f.support_model M x z hz).2, rfl⟩⟩
  assoc f g h := by
    induction f, g, h using Quotient.inductionOn₃ with
    | _ f g h =>
      apply Quotient.sound
      apply complete.{0} T
      intro M _ hM
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
      let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      rw [models_iff, uniformSentence_eval]
      intro x z
      change (comp h.graph (comp g.graph f.graph)).val.Evalb ![x, z] ↔
        (comp (comp h.graph g.graph) f.graph).val.Evalb ![x, z]
      simp only [comp_eval]
      constructor
      · rintro ⟨w, ⟨y, hxy, hyw⟩, hwz⟩
        exact ⟨y, hxy, w, hyw, hwz⟩
      · rintro ⟨y, hxy, w, hyw, hwz⟩
        exact ⟨w, ⟨y, hxy, hyw⟩, hwz⟩

/-- Equality of quotient programs can be proved from all T-model graphs. -/
theorem programClass_ext (a b : ProgramQuotient T)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M),
      SyntacticModel.programRelation T M a x y ↔
        SyntacticModel.programRelation T M b x y) : a = b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    apply (classOf_eq_classOf_iff T a b).mpr
    apply complete.{0} T
    intro M _ _
    rw [models_iff, uniformSentence_eval]
    exact h M

theorem domainClass_model (a : ProgramQuotient T)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (domainClass T a) x y ↔
      y = x ∧ ∃ z : M, SyntacticModel.programRelation T M a x z := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  induction a using Quotient.inductionOn with
  | _ a => exact eventualGraph_domainIndex_eval a x y

namespace GraphMorphism

variable {T} {C D E : Carrier}

def programClass (f : GraphMorphism T C D) : ProgramQuotient T :=
  classOf T (SyntacticSearch.searchIndex f.graph)

theorem programClass_model (f : GraphMorphism T C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M f.programClass x y ↔ f.graph.val.Evalb ![x, y] :=
  SyntacticModel.uniform_model T M
    (SyntacticSearch.search_uniform_of_functional T f.graph f.functional) x y

theorem programClass_eq_iff (f g : GraphMorphism T C D) :
    f.programClass = g.programClass ↔ Uniform T f.graph g.graph := by
  constructor
  · intro h
    have he := (classOf_eq_classOf_iff T _ _).mp h
    exact uniform_trans
      (uniform_symm (SyntacticSearch.search_uniform_of_functional T f.graph f.functional))
      (uniform_trans he (SyntacticSearch.search_uniform_of_functional T g.graph g.functional))
  · intro h
    apply (classOf_eq_classOf_iff T _ _).mpr
    exact uniform_trans (SyntacticSearch.search_uniform_of_functional T f.graph f.functional)
      (uniform_trans h
        (uniform_symm (SyntacticSearch.search_uniform_of_functional T g.graph g.functional)))

end GraphMorphism

def predicateClass (C : Carrier) : ProgramQuotient T :=
  (GraphMorphism.identity T C).programClass

theorem predicateClass_model (C : Carrier)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (predicateClass T C) x y ↔
      C.val.Evalb ![x] ∧ y = x := by
  rw [predicateClass, GraphMorphism.programClass_model]
  exact GraphMorphism.identityGraph_eval C x y

def omegaArrow (a : ProgramQuotient T) : omegaObject T ⟶ omegaObject T :=
  (omegaEndEquiv T).symm a

@[simp] theorem omegaArrow_val (a : ProgramQuotient T) : (omegaArrow T a).val = a := rfl

theorem restriction_val {X Y : CodedProgramCategory T} (f : X ⟶ Y) :
    (rst f).val = domainClass T f.val := by
  rw [← domainArrow_eq_restriction T f]
  rfl

/-- The actual restriction idempotent realizing an arbitrary carrier. -/
def predicateIdem (C : Carrier) : Idem (omegaObject T) where
  hom := omegaArrow T (predicateClass T C)
  restriction := by
    apply CodedHom.ext
    rw [restriction_val]
    change domainClass T (predicateClass T C) = predicateClass T C
    apply programClass_ext T
    intro M _ _ x y
    simp only [domainClass_model, predicateClass_model]
    constructor
    · rintro ⟨he, z, hc, _⟩
      exact ⟨hc, he⟩
    · rintro ⟨hc, he⟩
      exact ⟨he, x, hc, rfl⟩

abbrev TotalSplit (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :=
  WideSubcategory (isTotal (C := SplitObject (CodedProgramCategory T)))

def interpretedObject (C : PredicateCategory T) : TotalSplit T :=
  ⟨⟨omegaObject T, predicateIdem T C⟩⟩

namespace GraphMorphism

variable {T} {C D : Carrier}

theorem programClass_source (f : GraphMorphism T C D) :
    f.programClass * predicateClass T C = f.programClass := by
  apply programClass_ext T
  intro M _ _ x y
  rw [SyntacticModel.programRelation_mul, f.programClass_model M x y]
  constructor
  · rintro ⟨z, hc, hz⟩
    obtain ⟨_, he⟩ := (predicateClass_model T C M x z).mp hc
    subst z
    exact (f.programClass_model M x y).mp hz
  · intro hz
    exact ⟨x, (predicateClass_model T C M x x).mpr
      ⟨(f.support_model M x y hz).1, rfl⟩, (f.programClass_model M x y).mpr hz⟩

theorem programClass_target (f : GraphMorphism T C D) :
    predicateClass T D * f.programClass = f.programClass := by
  apply programClass_ext T
  intro M _ _ x y
  rw [SyntacticModel.programRelation_mul, f.programClass_model M x y]
  constructor
  · rintro ⟨z, hz, hc⟩
    obtain ⟨_, he⟩ := (predicateClass_model T D M z y).mp hc
    subst y
    exact (f.programClass_model M x z).mp hz
  · intro hz
    exact ⟨y, (f.programClass_model M x y).mpr hz,
      (predicateClass_model T D M y y).mpr ⟨(f.support_model M x y hz).2, rfl⟩⟩

theorem programClass_domain (f : GraphMorphism T C D) :
    domainClass T f.programClass = predicateClass T C := by
  apply programClass_ext T
  intro M _ _ x y
  rw [domainClass_model, predicateClass_model]
  constructor
  · rintro ⟨he, z, hz⟩
    exact ⟨(f.support_model M x z ((f.programClass_model M x z).mp hz)).1, he⟩
  · rintro ⟨hc, he⟩
    obtain ⟨z, hz, _⟩ := f.total_model M x hc
    exact ⟨he, z, (f.programClass_model M x z).mpr hz⟩

/-- Realize a represented graph as a morphism between its carrier
restriction idempotents. -/
def toSplit (f : GraphMorphism T C D) :
    (interpretedObject T C).obj ⟶ (interpretedObject T D).obj where
  hom := omegaArrow T f.programClass
  source := CodedHom.ext f.programClass_source
  target := CodedHom.ext f.programClass_target

theorem toSplit_total (f : GraphMorphism T C D) : isTotal f.toSplit := by
  apply SplitObject.Hom.ext
  apply CodedHom.ext
  change (rst (omegaArrow T f.programClass)).val = predicateClass T C
  rw [restriction_val]
  exact f.programClass_domain

def toTotal (f : GraphMorphism T C D) : interpretedObject T C ⟶ interpretedObject T D :=
  ⟨f.toSplit, f.toSplit_total⟩

theorem toTotal_congr (f g : GraphMorphism T C D) (h : Uniform T f.graph g.graph) :
    f.toTotal = g.toTotal := by
  apply WideSubcategory.hom_ext
  apply SplitObject.Hom.ext
  apply CodedHom.ext
  exact (f.programClass_eq_iff g).mpr h

end GraphMorphism

/-- The predicate presentation maps into the total restriction splitting
by the actual functional-search realization. -/
def realization : PredicateCategory T ⥤ TotalSplit T where
  obj := interpretedObject T
  map := Quotient.lift GraphMorphism.toTotal GraphMorphism.toTotal_congr
  map_id C := by
    apply WideSubcategory.hom_ext
    apply SplitObject.Hom.ext
    apply CodedHom.ext
    rfl
  map_comp f g := by
    induction f, g using Quotient.inductionOn₂ with
    | _ f g =>
      apply WideSubcategory.hom_ext
      apply SplitObject.Hom.ext
      apply CodedHom.ext
      apply programClass_ext T
      intro M _ hM x z
      let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
      let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      change SyntacticModel.programRelation T M (f.composition g).programClass x z ↔
        SyntacticModel.programRelation T M (g.programClass * f.programClass) x z
      rw [(f.composition g).programClass_model M x z, SyntacticModel.programRelation_mul]
      change (comp g.graph f.graph).val.Evalb ![x, z] ↔ _
      rw [comp_eval]
      exact exists_congr fun y => and_congr
        (f.programClass_model M x y).symm (g.programClass_model M y z).symm

@[simp] theorem realization_map_class {C D : PredicateCategory T}
    (f : GraphMorphism T C D) :
    (realization T).map (classOfGraph T f) = f.toTotal := rfl

instance realization_faithful : (realization T).Faithful where
  map_injective {C D} f g h := by
    induction f, g using Quotient.inductionOn₂ with
    | _ f g =>
      apply Quotient.sound
      apply (f.programClass_eq_iff g).mp
      exact congrArg (fun k : interpretedObject T C ⟶ interpretedObject T D =>
        k.hom.hom.val) h

section Fullness

variable {T} {C D : PredicateCategory T}

theorem total_source_class (f : interpretedObject T C ⟶ interpretedObject T D) :
    f.hom.hom.val * predicateClass T C = f.hom.hom.val :=
  congrArg (fun k : omegaObject T ⟶ omegaObject T => k.val) f.hom.source

theorem total_target_class (f : interpretedObject T C ⟶ interpretedObject T D) :
    predicateClass T D * f.hom.hom.val = f.hom.hom.val :=
  congrArg (fun k : omegaObject T ⟶ omegaObject T => k.val) f.hom.target

theorem total_domain_class (f : interpretedObject T C ⟶ interpretedObject T D) :
    domainClass T f.hom.hom.val = predicateClass T C := by
  have ht : rst f.hom = 𝟙 (interpretedObject T C).obj := f.property
  have h := congrArg (fun k : (interpretedObject T C).obj ⟶
    (interpretedObject T C).obj => k.hom.val) ht
  change (rst f.hom.hom).val = predicateClass T C at h
  rwa [restriction_val] at h

theorem total_support_model (f : interpretedObject T C ⟶ interpretedObject T D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M)
    (h : SyntacticModel.programRelation T M f.hom.hom.val x y) :
    C.val.Evalb ![x] ∧ D.val.Evalb ![y] := by
  constructor
  · have hs : SyntacticModel.programRelation T M
        (f.hom.hom.val * predicateClass T C) x y := by
      rw [total_source_class]
      exact h
    obtain ⟨z, hz, _⟩ := (SyntacticModel.programRelation_mul T M _ _ x y).mp hs
    exact ((predicateClass_model T C M x z).mp hz).1
  · have ht : SyntacticModel.programRelation T M
        (predicateClass T D * f.hom.hom.val) x y := by
      rw [total_target_class]
      exact h
    obtain ⟨z, _, hz⟩ := (SyntacticModel.programRelation_mul T M _ _ x y).mp ht
    obtain ⟨hd, he⟩ := (predicateClass_model T D M z y).mp hz
    exact he.symm ▸ hd

theorem total_domain_model (f : interpretedObject T C ⟶ interpretedObject T D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M)
    (hx : C.val.Evalb ![x]) :
    ∃ y : M, SyntacticModel.programRelation T M f.hom.hom.val x y := by
  have ht : SyntacticModel.programRelation T M (domainClass T f.hom.hom.val) x x := by
    rw [total_domain_class]
    exact (predicateClass_model T C M x x).mpr ⟨hx, rfl⟩
  exact ((domainClass_model T _ M x x).mp ht).2

def graphIndex (f : interpretedObject T C ⟶ interpretedObject T D) : ℕ :=
  Quotient.out f.hom.hom.val

theorem graphIndex_class (f : interpretedObject T C ⟶ interpretedObject T D) :
    classOf T (graphIndex f) = f.hom.hom.val := Quotient.out_eq _

theorem graphIndex_model (f : interpretedObject T C ⟶ interpretedObject T D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    (eventualGraph (graphIndex f)).val.Evalb ![x, y] ↔
      SyntacticModel.programRelation T M f.hom.hom.val x y := by
  change SyntacticModel.programRelation T M (classOf T (graphIndex f)) x y ↔ _
  rw [graphIndex_class]

/-- Every total morphism between predicate objects has the required
support and unique-totality proofs as a Sigma-one graph. -/
def graphOfTotal (f : interpretedObject T C ⟶ interpretedObject T D) :
    GraphMorphism T C D where
  graph := eventualGraph (graphIndex f)
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro x y hxy
    exact total_support_model f M x y ((graphIndex_model f M x y).mp hxy)
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro x hx
    obtain ⟨y, hy⟩ := total_domain_model f M x hx
    refine ⟨y, (graphIndex_model f M x y).mpr hy, ?_⟩
    intro z hz
    exact SyntacticModel.programRelation_functional T M _ x z y
      ((graphIndex_model f M x z).mp hz) hy

theorem graphOfTotal_realizes (f : interpretedObject T C ⟶ interpretedObject T D) :
    (graphOfTotal f).toTotal = f := by
  apply WideSubcategory.hom_ext
  apply SplitObject.Hom.ext
  apply CodedHom.ext
  change (graphOfTotal f).programClass = f.hom.hom.val
  apply programClass_ext T
  intro M _ _ x y
  rw [GraphMorphism.programClass_model]
  exact graphIndex_model f M x y

end Fullness

instance realization_full : (realization T).Full where
  map_surjective f := ⟨classOfGraph T (graphOfTotal f), graphOfTotal_realizes f⟩

section EssentialSurjectivity

theorem pull_iso_conjugate {X Y : CodedProgramCategory T} (i : X ≅ Y) (a : Idem X) :
    (Idem.pull i.inv a).hom = i.inv ≫ a.hom ≫ i.hom := by
  have h := congrArg (fun f => f ≫ i.hom) (Idem.pull_commute i.inv a)
  simpa only [Category.assoc, i.inv_hom_id, Category.comp_id] using h

def rebaseObject (X : SplitObject (CodedProgramCategory T))
    {Y : CodedProgramCategory T} (i : X.base ≅ Y) :
    SplitObject (CodedProgramCategory T) :=
  ⟨Y, Idem.pull i.inv X.domain⟩

/-- Transporting the support along a coding isomorphism gives an actual
isomorphism of split objects. -/
def rebaseIso (X : SplitObject (CodedProgramCategory T))
    {Y : CodedProgramCategory T} (i : X.base ≅ Y) : X ≅ rebaseObject T X i where
  hom :=
    { hom := X.domain.hom ≫ i.hom
      source := by rw [← Category.assoc, X.domain.idem]
      target := by
        change (X.domain.hom ≫ i.hom) ≫ (Idem.pull i.inv X.domain).hom = _
        rw [pull_iso_conjugate]
        simp only [Category.assoc, i.hom_inv_id_assoc]
        rw [← Category.assoc, X.domain.idem] }
  inv :=
    { hom := i.inv ≫ X.domain.hom
      source := by
        change (Idem.pull i.inv X.domain).hom ≫ (i.inv ≫ X.domain.hom) = _
        rw [pull_iso_conjugate]
        simp only [Category.assoc, i.hom_inv_id_assoc]
        rw [X.domain.idem]
      target := by rw [Category.assoc, X.domain.idem] }
  hom_inv_id := by
    apply SplitObject.Hom.ext
    change (X.domain.hom ≫ i.hom) ≫ (i.inv ≫ X.domain.hom) = X.domain.hom
    simp only [Category.assoc, i.hom_inv_id_assoc]
    exact X.domain.idem
  inv_hom_id := by
    apply SplitObject.Hom.ext
    change (i.inv ≫ X.domain.hom) ≫ (X.domain.hom ≫ i.hom) =
      (Idem.pull i.inv X.domain).hom
    rw [pull_iso_conjugate]
    simp only [Category.assoc]
    rw [← Category.assoc X.domain.hom X.domain.hom i.hom, X.domain.idem]

def domainCarrier (q : ℕ) : Carrier := .mkSigma “x. ∃ y, !(eventualGraph q).val x y”

@[simp] theorem domainCarrier_eval {M : Type} [ORingStructure M] (q : ℕ) (x : M) :
    (domainCarrier q).val.Evalb ![x] ↔ ∃ y : M, (eventualGraph q).val.Evalb ![x, y] := by
  simp [domainCarrier]

theorem predicateClass_domainCarrier (q : ℕ) :
    predicateClass T (domainCarrier q) = domainClass T (classOf T q) := by
  apply programClass_ext T
  intro M _ _ x y
  rw [predicateClass_model, domainClass_model, domainCarrier_eval]
  exact and_comm

/-- Every restriction idempotent on omega is the partial identity of an
arithmetic Sigma-one carrier predicate. -/
theorem omegaIdem_is_predicate (e : Idem (omegaObject T)) :
    ∃ C : Carrier, e = predicateIdem T C := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep e.hom.val
  refine ⟨domainCarrier q, ?_⟩
  apply Idem.ext
  apply CodedHom.ext
  have he := congrArg (fun f : omegaObject T ⟶ omegaObject T => f.val) e.restriction
  rw [restriction_val] at he
  change e.hom.val = predicateClass T (domainCarrier q)
  have hq' : classOf T q = e.hom.val := hq
  calc
    e.hom.val = domainClass T e.hom.val := he.symm
    _ = domainClass T (classOf T q) := congrArg (domainClass T) hq'.symm
    _ = predicateClass T (domainCarrier q) := (predicateClass_domainCarrier T q).symm

instance realization_essSurj : (realization T).EssSurj := by
  constructor
  intro X
  let i := TypedRecursionCategory.isoToOmega T (objectCode X.obj.base)
  let Y := rebaseObject T X.obj i
  obtain ⟨C, hC⟩ := omegaIdem_is_predicate T Y.domain
  have hY : (⟨Y⟩ : TotalSplit T) = interpretedObject T C := by
    change (⟨⟨omegaObject T, Y.domain⟩⟩ : TotalSplit T) =
      ⟨⟨omegaObject T, predicateIdem T C⟩⟩
    rw [hC]
  let e : X ≅ (⟨Y⟩ : TotalSplit T) :=
    WideSubcategory.isoMk (rebaseIso T X.obj i)
      (iso_total (rebaseIso T X.obj i)) (iso_total (rebaseIso T X.obj i).symm)
  exact ⟨C, ⟨(eqToIso hY.symm).trans e.symm⟩⟩

instance realization_isEquivalence : (realization T).IsEquivalence := {}

/-- The predicate presentation and the total restriction splitting are
equivalent in the fixed production program presentation. -/
def predicateEquivalence : PredicateCategory T ≌ TotalSplit T :=
  (realization T).asEquivalence

end EssentialSurjectivity

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates
