/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RealizedObjectSetsCategory

/-! # Object sets, numerical codings and the realization functor of §6 -/

@[expose] public section

noncomputable section

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.V46 RealizedObjectSets

example : realize .omega = ZFSet.omega := rfl
example : ordinal 0 = ∅ := rfl
example : ordinal 1 = {∅} := rfl
example (X Y : STObjectCode) : realize (.product X Y) = (realize X).prod (realize Y) := rfl
example (X Y : STObjectCode) : realize (.coproduct X Y) =
    (realize X).prod {∅} ∪ (realize Y).prod {({∅} : ZFSet.{0})} := rfl

example (X : STObjectCode) : (realize X : Set ZFSet.{0}).Infinite := infinite_realize X
example (X Y : STObjectCode) : (firstProjection (realize (.product X Y)) = realize X) ∧
    secondProjection (realize (.product X Y)) = realize Y :=
  ⟨firstProjection_product _ _ (infinite_realize Y).nonempty,
    secondProjection_product _ _ (infinite_realize X).nonempty⟩
example (X Y : STObjectCode) : secondProjection (realize (.coproduct X Y)) = {∅, {∅}} :=
  secondProjection_taggedUnion _ _ (infinite_realize X).nonempty (infinite_realize Y).nonempty
example (X Y : STObjectCode) (x : ZFSet.{0}) :
    (ZFSet.pair x ∅ ∈ realize (.coproduct X Y) ↔ x ∈ realize X) ∧
    (ZFSet.pair x {∅} ∈ realize (.coproduct X Y) ↔ x ∈ realize Y) :=
  ⟨tag_zero_fibre, tag_one_fibre⟩
example (X Y : STObjectCode) : realize X = realize Y ↔ X = Y := realize_injective.eq_iff
example (A : ZFSet.{0}) : A ∈ Set.range realize ↔
    ∀ S : Set ZFSet.{0}, ZFSet.omega ∈ S →
      (∀ B ∈ S, ∀ C ∈ S, B.prod C ∈ S) →
      (∀ B ∈ S, ∀ C ∈ S, B.prod {∅} ∪ C.prod {({∅} : ZFSet.{0})} ∈ S) → A ∈ S :=
  mem_range_realize_iff A
example (A : Set.range realize) : ∃! X : STObjectCode, realize X = A.val := unique_term A

example (X : STObjectCode) : ↥(realize X) ≃ ℕ := coding X
example (n : ℕ) : coding .omega ⟨ZFSet.mk (PSet.ofNat n), ordinal_mem_omega n⟩ = n :=
  coding_ordinal n
example (X Y : STObjectCode) (x : realize X) (y : realize Y) :
    coding (.product X Y)
      ⟨ZFSet.pair x.val y.val, ZFSet.pair_mem_prod.mpr ⟨x.property, y.property⟩⟩ =
        2 ^ coding X x * (2 * coding Y y + 1) - 1 := coding_product X Y x y
example (X Y : STObjectCode) (x : realize X) :
    coding (.coproduct X Y) ⟨ZFSet.pair x.val ∅, tag_zero_fibre.mpr x.property⟩ = 2 * coding X x :=
  coding_inl X Y x
example (X Y : STObjectCode) (y : realize Y) :
    coding (.coproduct X Y) ⟨ZFSet.pair y.val {∅}, tag_one_fibre.mpr y.property⟩ =
      2 * coding Y y + 1 :=
  coding_inr X Y y
example (X : STObjectCode) : setCoding ⟨realize X, ⟨X, rfl⟩⟩ = coding X := setCoding_realize X
example (A : Set.range realize) :
    ∃! γ : ↥A.val ≃ ℕ, ∃ (X : STObjectCode) (h : realize X = A.val),
      γ = codingOfRealization X h := unique_coding A

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example : PrintedObjectCoding.NormalizedCategory T ⥤ SetPresentation T := realizationFunctor T
example (X : STObjectCode) : ((realizationFunctor T).obj X : Set.range realize).val = realize X :=
  realization_obj T X
example (X Y : STObjectCode) (e : ℕ) :
    homProgramEquiv T _ _ ((realizationFunctor T).map
      ((PrintedObjectCoding.homProgramEquiv T X Y).symm (classOf T e))) = classOf T e := rfl
example (A B : SetPresentation T) (e f : ℕ) :
    represented T A B e = represented T A B f ↔
      T ⊢ ProofSearch.uniformSentence (firstSuccessGraph e) (firstSuccessGraph f) :=
  represented_eq_iff T A B e f
example (A B C : SetPresentation T) (e f : ℕ) :
    represented T A B e ≫ represented T B C f = represented T A C (UniformTrace.compose f e) :=
  represented_comp T A B C e f
example (A : SetPresentation T) : represented T A A Kleene.identityIndex = 𝟙 A :=
  represented_identity T A
example (A B : SetPresentation T) :
    represented T A B Kleene.identityIndex ≫ represented T B A Kleene.identityIndex = 𝟙 A :=
  identity_index_composite T A B
example (X Y : PrintedObjectCoding.NormalizedCategory T) :
    Function.Bijective ((realizationFunctor T).map (X := X) (Y := Y)) :=
  realization_map_bijective T X Y
example (A : SetPresentation T) : ∃ X, (realizationFunctor T).obj X = A :=
  (realization_obj_bijective T).surjective A
example : (realizationFunctor T).EssSurj := inferInstance
example : PrintedObjectCoding.NormalizedCategory T ≌ SetPresentation T := realizationEquivalence T
example : CodedProgramCategory T ≌ SetPresentation T := codedProgramEquivalence T
example (A : SetPresentation 𝗣𝗔) : (realizationEquivalence 𝗣𝗔).functor.obj
    ((realizationEquivalence 𝗣𝗔).inverse.obj A) = A := realization_term 𝗣𝗔 A

example (X Y : STObjectCode) (e : ℕ) (x : realize X) (y : realize Y) :
    decodedGraph e (A := objectSet X) (B := objectSet Y) x y ↔
      (firstSuccessGraph e).val.Evalb (M := ℕ) ![coding X x, coding Y y] :=
  decodedGraph_realize X Y e x y

example (X : STObjectCode) (x : realize X) (n : ℕ) :
    (firstSuccessGraph Kleene.identityIndex).val.Evalb (M := ℕ)
      ![setCoding (objectSet X) x,
        setCoding (objectSet .omega) ⟨ordinal n, ordinal_mem_omega n⟩] ↔
          n = coding X x := identity_represents_coding X x n
example (X : STObjectCode) (n : ℕ) (x : realize X) :
    (firstSuccessGraph Kleene.identityIndex).val.Evalb (M := ℕ)
      ![setCoding (objectSet .omega) ⟨ordinal n, ordinal_mem_omega n⟩,
        setCoding (objectSet X) x] ↔
          x = (coding X).symm n := identity_represents_inverse X n x
