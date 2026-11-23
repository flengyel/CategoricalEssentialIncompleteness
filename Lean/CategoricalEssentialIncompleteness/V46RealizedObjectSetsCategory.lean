/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RealizedObjectSets
public import CategoricalEssentialIncompleteness.V46UniformTraceComparison

/-! # The set presentation of the syntactic recursion category

The functor `Π_T` of §6 sends each object term to its realized set. A numerical program index
represents the same class at the source and target objects on both sides of the functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RealizedObjectSets

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The objects of the set presentation in §6 are the generated sets. Each pair of objects
has the numerical program quotient of `T` as its hom-set. -/
abbrev SetPresentation :=
  InducedCategory (CodedProgramCategory T) (fun _ : Set.range realize => omegaObject T)

/-- The class of a morphism in the set presentation. -/
def homProgramEquiv (A B : SetPresentation T) : (A ⟶ B) ≃ ProgramQuotient T :=
  InducedCategory.homEquiv.trans (omegaEndEquiv T)

/-- A numerical index interpreted using the codings of its two endpoint sets. -/
def represented (A B : SetPresentation T) (e : ℕ) : A ⟶ B :=
  (homProgramEquiv T A B).symm (classOf T e)

/-- Equality of represented morphisms is the uniform provability relation of §6 for the
first-success computation graphs. -/
theorem represented_eq_iff (A B : SetPresentation T) (e f : ℕ) :
    represented T A B e = represented T A B f ↔
      Uniform T (firstSuccessGraph e) (firstSuccessGraph f) := by
  have h (i : ℕ) : Uniform T (firstSuccessGraph i) (ConcreteEvaluator.eventualGraph i) :=
    WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph i)
  calc
    _ ↔ classOf T e = classOf T f := (homProgramEquiv T A B).symm.injective.eq_iff
    _ ↔ EqIndex T e f := classOf_eq_classOf_iff T e f
    _ ↔ _ := ⟨fun hef => uniform_trans (h e) (uniform_trans hef (uniform_symm (h f))),
      fun hef => uniform_trans (uniform_symm (h e)) (uniform_trans hef (h f))⟩

theorem represented_identity (A : SetPresentation T) :
    represented T A A Kleene.identityIndex = 𝟙 A :=
  (homProgramEquiv T A A).injective (omegaEndEquiv_id T).symm

theorem identity_index_composite (A B : SetPresentation T) :
    represented T A B Kleene.identityIndex ≫ represented T B A Kleene.identityIndex = 𝟙 A := by
  apply (homProgramEquiv T A A).injective
  change classOf T Kleene.identityIndex * classOf T Kleene.identityIndex = _
  rw [← one_eq_classOf T, one_mul]
  exact (omegaEndEquiv_id T).symm

theorem represented_comp (A B C : SetPresentation T) (e f : ℕ) :
    represented T A B e ≫ represented T B C f = represented T A C (UniformTrace.compose f e) := by
  apply (homProgramEquiv T A C).injective
  change classOf T (compIndex f e) = classOf T (UniformTrace.compose f e)
  exact (classOf_eq_classOf_iff T _ _).mpr
    (uniform_symm (WeakerThan.pbl (UniformTrace.compose_production_PA f e)))

/-- Realization sends each term to its set and each morphism to the same numerical program class. -/
def realizationFunctor : PrintedObjectCoding.NormalizedCategory T ⥤ SetPresentation T where
  obj := objectSet
  map f := InducedCategory.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem realization_obj (X : PrintedObjectCoding.NormalizedCategory T) :
    ((realizationFunctor T).obj X : Set.range realize).val = realize X := rfl

theorem realization_map_index (X Y : PrintedObjectCoding.NormalizedCategory T) (e : ℕ) :
    (realizationFunctor T).map ((PrintedObjectCoding.homProgramEquiv T X Y).symm (classOf T e)) =
      represented T ((realizationFunctor T).obj X) ((realizationFunctor T).obj Y) e := rfl

theorem realization_map_bijective (X Y : PrintedObjectCoding.NormalizedCategory T) :
    Function.Bijective ((realizationFunctor T).map (X := X) (Y := Y)) := by
  constructor
  · intro f g h
    apply InducedCategory.hom_ext
    exact congrArg (fun k : (realizationFunctor T).obj X ⟶ (realizationFunctor T).obj Y => k.hom) h
  · exact fun f => ⟨InducedCategory.homMk f.hom, rfl⟩

theorem realization_obj_bijective : Function.Bijective (realizationFunctor T).obj :=
  objectEquiv.bijective

instance : (realizationFunctor T).Faithful where
  map_injective {X Y} _ _ h := (realization_map_bijective T X Y).injective h

instance : (realizationFunctor T).Full where
  map_surjective := (realization_map_bijective T _ _).surjective

instance : (realizationFunctor T).EssSurj :=
  Functor.essSurj_of_surj (realization_obj_bijective T).surjective

instance : (realizationFunctor T).IsEquivalence := {}

/-- The inverse functor recovers the term of every generated set and preserves each class. -/
def termFunctor : SetPresentation T ⥤ PrintedObjectCoding.NormalizedCategory T where
  obj := objectEquiv.symm
  map f := InducedCategory.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem term_realization (X : PrintedObjectCoding.NormalizedCategory T) :
    (termFunctor T).obj ((realizationFunctor T).obj X) = X := objectEquiv.symm_apply_apply X

theorem realization_term (A : SetPresentation T) :
    (realizationFunctor T).obj ((termFunctor T).obj A) = A := objectEquiv.apply_symm_apply A

/-- The formal terms and the generated sets give equivalent categories. Both directions use
numerical identity programs as the components of the unit and counit. -/
def realizationEquivalence : PrintedObjectCoding.NormalizedCategory T ≌ SetPresentation T where
  functor := realizationFunctor T
  inverse := termFunctor T
  unitIso := NatIso.ofComponents (fun _ => InducedCategory.isoMk (Iso.refl _)) (by
    intro X Y f
    apply InducedCategory.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  counitIso := NatIso.ofComponents (fun _ => InducedCategory.isoMk (Iso.refl _)) (by
    intro A B f
    apply InducedCategory.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  functor_unitIso_comp _ := by
    apply InducedCategory.hom_ext
    change (𝟙 _ : omegaObject T ⟶ omegaObject T) ≫ 𝟙 _ = 𝟙 _
    simp

/-- Conjugating by the numerical coding of each typed object and then realizing its term
identifies the original typed program category with the category on the generated sets. -/
def codedProgramEquivalence : CodedProgramCategory T ≌ SetPresentation T :=
  (PrintedObjectCoding.equivalence T).trans (realizationEquivalence T)

/-- The graph of a fixed program on the decoded sets uses the specified numerical codings. -/
def decodedGraph (e : ℕ) {A B : Set.range realize} (x : A.val) (y : B.val) : Prop :=
  (firstSuccessGraph e).val.Evalb (M := ℕ) ![setCoding A x, setCoding B y]

theorem decodedGraph_realize (X Y : STObjectCode) (e : ℕ) (x : realize X) (y : realize Y) :
    decodedGraph e (A := objectSet X) (B := objectSet Y) x y ↔
      (firstSuccessGraph e).val.Evalb (M := ℕ) ![coding X x, coding Y y] := by
  unfold decodedGraph
  rw [setCoding_realize X, setCoding_realize Y]

theorem identity_decodedGraph {A B : Set.range realize} (x : A.val) (y : B.val) :
    decodedGraph Kleene.identityIndex x y ↔ setCoding B y = setCoding A x :=
  (SyntacticModel.uniform_model 𝗣𝗔 ℕ (firstSuccessGraph_uniform_eventualGraph _) _ _).trans
    (TypedNearProduct.eventualGraph_identityIndex_eval _ _)

theorem identity_represents_coding (X : STObjectCode) (x : realize X) (n : ℕ) :
    decodedGraph Kleene.identityIndex (A := objectSet X) (B := objectSet .omega)
      x ⟨ordinal n, ordinal_mem_omega n⟩ ↔ n = coding X x := by
  rw [identity_decodedGraph (A := objectSet X) (B := objectSet .omega),
    setCoding_realize .omega, setCoding_realize X, coding_ordinal]

theorem identity_represents_inverse (X : STObjectCode) (n : ℕ) (x : realize X) :
    decodedGraph Kleene.identityIndex (A := objectSet .omega) (B := objectSet X)
      ⟨ordinal n, ordinal_mem_omega n⟩ x ↔ x = (coding X).symm n := by
  rw [identity_decodedGraph (A := objectSet .omega) (B := objectSet X),
    setCoding_realize X, setCoding_realize .omega, coding_ordinal, Equiv.eq_symm_apply]

end CategoricalEssentialIncompleteness.V46.RealizedObjectSets
