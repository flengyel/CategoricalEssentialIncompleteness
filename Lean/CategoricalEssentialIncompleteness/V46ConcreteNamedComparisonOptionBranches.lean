/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptions
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions

/-! # Failure branches and scalar option-operation equations -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

section Generic
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

theorem binary_failure_left {X Y Z : D} (h : Y ⨯ Y ⟶ Z)
    (a : X ⟶ ⊤_ D) (v : X ⟶ OptionSyntax.obj Y) :
    prod.lift (a ≫ coprod.inl) v ≫ OptionSyntax.binary h = OptionSyntax.fail := by
  unfold OptionSyntax.binary
  rw [SumFibers.comp_caseOf_inl _ _ _ (prod.lift (a ≫ coprod.inl) v) a (by simp)]
  simp [OptionSyntax.fail]

theorem binary_failure_right {X Y Z : D} (h : Y ⨯ Y ⟶ Z)
    (y : X ⟶ Y) (a : X ⟶ ⊤_ D) :
    prod.lift (y ≫ coprod.inr) (a ≫ coprod.inl) ≫ OptionSyntax.binary h = OptionSyntax.fail := by
  let k : X ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y :=
    prod.lift (y ≫ coprod.inr) (a ≫ coprod.inl)
  have hk : k ≫ prod.fst = y ≫ coprod.inr := by simp [k]
  let l := pullback.lift k y hk
  have hl : l ≫ (pullback.fst (prod.fst : OptionSyntax.obj Y ⨯ OptionSyntax.obj Y ⟶ _) coprod.inr ≫
      prod.snd) = a ≫ coprod.inl := by simp [l,k]
  change k ≫ OptionSyntax.binary h = _
  unfold OptionSyntax.binary
  rw [SumFibers.comp_caseOf_inr _ _ _ k y hk,
    SumFibers.comp_caseOf_inl _ _ _ l a hl]
  simp [OptionSyntax.fail]

theorem coefficient_failure {X V Y Z : D} (h : V ⨯ Y ⟶ Z)
    (v : X ⟶ V) (a : X ⟶ ⊤_ D) :
    prod.lift v (a ≫ coprod.inl) ≫ OptionSyntax.coefficient h = OptionSyntax.fail := by
  unfold OptionSyntax.coefficient
  rw [SumFibers.comp_caseOf_inl _ _ _ (prod.lift v (a ≫ coprod.inl)) a (by simp)]
  simp [OptionSyntax.fail]

@[reassoc] theorem binary_failure_left_map {Y Z : D} (h : Y ⨯ Y ⟶ Z) :
    prod.map (coprod.inl : (⊤_ D) ⟶ OptionSyntax.obj Y) (𝟙 (OptionSyntax.obj Y)) ≫
      OptionSyntax.binary h = OptionSyntax.fail := by
  have he : prod.map (coprod.inl : (⊤_ D) ⟶ OptionSyntax.obj Y) (𝟙 (OptionSyntax.obj Y)) =
      prod.lift (prod.fst ≫ coprod.inl) prod.snd := by
    apply prod.hom_ext <;> simp
  rw [he]
  exact binary_failure_left h (prod.fst : (⊤_ D) ⨯ OptionSyntax.obj Y ⟶ _) prod.snd

@[reassoc] theorem binary_failure_right_map {Y Z : D} (h : Y ⨯ Y ⟶ Z) :
    prod.map (coprod.inr : Y ⟶ OptionSyntax.obj Y) (coprod.inl : (⊤_ D) ⟶ OptionSyntax.obj Y) ≫
      OptionSyntax.binary h = OptionSyntax.fail := by
  simpa using binary_failure_right h (prod.fst : Y ⨯ (⊤_ D) ⟶ Y) prod.snd

@[reassoc] theorem coefficient_failure_map {V Y Z : D} (h : V ⨯ Y ⟶ Z) :
    prod.map (𝟙 V) (coprod.inl : (⊤_ D) ⟶ OptionSyntax.obj Y) ≫
      OptionSyntax.coefficient h = OptionSyntax.fail := by
  have he : prod.map (𝟙 V) (coprod.inl : (⊤_ D) ⟶ OptionSyntax.obj Y) =
      prod.lift prod.fst (prod.snd ≫ coprod.inl) := by
    apply prod.hom_ext <;> simp
  rw [he]
  exact coefficient_failure h (prod.fst : V ⨯ (⊤_ D) ⟶ V) prod.snd

end Generic

section Models
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem model_binary_failure_left {C D : PredicateCategory T} (h : C ⨯ C ⟶ D)
    (q : Obj T M (OptionSyntax.obj C ⨯ OptionSyntax.obj C))
    (a : Obj T M (⊤_ (PredicateCategory T)))
    (ha : (F T M).map (prod.fst : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) a) :
    optionCode T M D ((F T M).map (OptionSyntax.binary h) q) = 0 := by
  let b := (F T M).map (prod.snd : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q
  obtain ⟨z,hza,hzb⟩ := modelProduct_exists T M (⊤_ (PredicateCategory T)) (OptionSyntax.obj C) a b
  let k := (prod.map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) (𝟙 (OptionSyntax.obj C)))
  have hz : (F T M).map k z = q := by
    apply modelProduct_ext T M
    · erw [model_map_fst T M _ _ z,hza]
      exact ha.symm
    · erw [model_map_snd T M _ _ z,hzb,Functor.map_id_apply]
  rw [← hz,← Functor.map_comp_apply,binary_failure_left_map]
  exact optionCode_fail T M z

theorem model_binary_failure_right {C D : PredicateCategory T} (h : C ⨯ C ⟶ D)
    (q : Obj T M (OptionSyntax.obj C ⨯ OptionSyntax.obj C))
    (y : Obj T M C) (a : Obj T M (⊤_ (PredicateCategory T)))
    (hy : (F T M).map (prod.fst : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y)
    (ha : (F T M).map (prod.snd : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) a) :
    optionCode T M D ((F T M).map (OptionSyntax.binary h) q) = 0 := by
  obtain ⟨z,hzy,hza⟩ := modelProduct_exists T M C (⊤_ (PredicateCategory T)) y a
  let k := (prod.map (coprod.inr : C ⟶ OptionSyntax.obj C)
    (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C))
  have hz : (F T M).map k z = q := by
    apply modelProduct_ext T M
    · erw [model_map_fst T M _ _ z,hzy]
      exact hy.symm
    · erw [model_map_snd T M _ _ z,hza]
      exact ha.symm
  rw [← hz,← Functor.map_comp_apply,binary_failure_right_map]
  exact optionCode_fail T M z

theorem model_binary_success {C D : PredicateCategory T} (h : C ⨯ C ⟶ D)
    (φ : M → M → M)
    (hf : ∀ z : Obj T M (C ⨯ C), ((F T M).map h z).val =
      φ ((F T M).map (prod.fst : C ⨯ C ⟶ C) z).val ((F T M).map (prod.snd : C ⨯ C ⟶ C) z).val)
    (q : Obj T M (OptionSyntax.obj C ⨯ OptionSyntax.obj C))
    (x y : Obj T M C)
    (hx : (F T M).map (prod.fst : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) x)
    (hy : (F T M).map (prod.snd : OptionSyntax.obj C ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y) :
    optionCode T M D ((F T M).map (OptionSyntax.binary h) q) = Arithmetic.pair (φ x.val y.val) 1 := by
  obtain ⟨z,hzx,hzy⟩ := modelProduct_exists T M C C x y
  let k := (prod.map (coprod.inr : C ⟶ OptionSyntax.obj C) (coprod.inr : C ⟶ OptionSyntax.obj C))
  have hz : (F T M).map k z = q := by
    apply modelProduct_ext T M
    · erw [model_map_fst T M _ _ z,hzx]
      exact hx.symm
    · erw [model_map_snd T M _ _ z,hzy]
      exact hy.symm
  rw [← hz,← Functor.map_comp_apply,OptionSyntax.binary_ok_map,Functor.map_comp_apply,optionCode_inr]
  exact congrArg (fun w => Arithmetic.pair w 1) (by simpa only [hzx,hzy] using hf z)

/-- Failure propagation is computed from the coproduct fibers; the successful values use
the product projections of h. -/
theorem optionCode_binary {C D : PredicateCategory T} (h : C ⨯ C ⟶ D)
    (φ : M → M → M)
    (hf : ∀ z : Obj T M (C ⨯ C), ((F T M).map h z).val =
      φ ((F T M).map (prod.fst : C ⨯ C ⟶ C) z).val ((F T M).map (prod.snd : C ⨯ C ⟶ C) z).val)
    (q : Obj T M (OptionSyntax.obj C ⨯ OptionSyntax.obj C)) :
    optionCode T M D ((F T M).map (OptionSyntax.binary h) q) =
      if π₂ (optionCode T M C ((F T M).map prod.fst q)) = 1 ∧
          π₂ (optionCode T M C ((F T M).map prod.snd q)) = 1
      then Arithmetic.pair
        (φ (π₁ (optionCode T M C ((F T M).map prod.fst q)))
          (π₁ (optionCode T M C ((F T M).map prod.snd q)))) 1 else 0 := by
  rcases modelSum_cases T M (⊤_ (PredicateCategory T)) C ((F T M).map prod.fst q) with
    ⟨a,ha⟩ | ⟨x,hx⟩
  · have hl := optionCode_inl T M C a
    have hleft : optionCode T M C ((F T M).map prod.fst q) = 0 := by rw [← ha]; exact hl
    rw [model_binary_failure_left T M h q a ha.symm,hleft]
    simp [pi₂_zero]
  · rcases modelSum_cases T M (⊤_ (PredicateCategory T)) C ((F T M).map prod.snd q) with
      ⟨a,ha⟩ | ⟨y,hy⟩
    · have hright : optionCode T M C ((F T M).map prod.snd q) = 0 := by
        rw [← ha]; exact optionCode_inl T M C a
      rw [model_binary_failure_right T M h q x a hx.symm ha.symm,hright]
      simp [pi₂_zero]
    · have hleft : optionCode T M C ((F T M).map prod.fst q) = Arithmetic.pair x.val 1 := by
        rw [← hx]; exact optionCode_inr T M C x
      have hright : optionCode T M C ((F T M).map prod.snd q) = Arithmetic.pair y.val 1 := by
        rw [← hy]; exact optionCode_inr T M C y
      rw [model_binary_success T M h φ hf q x y hx.symm hy.symm,hleft,hright]
      simp only [pi₂_pair,true_and,↓reduceIte,pi₁_pair]

theorem model_coefficient_failure {V C D : PredicateCategory T} (h : V ⨯ C ⟶ D)
    (q : Obj T M (V ⨯ OptionSyntax.obj C))
    (a : Obj T M (⊤_ (PredicateCategory T)))
    (ha : (F T M).map (prod.snd : V ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C) a) :
    optionCode T M D ((F T M).map (OptionSyntax.coefficient h) q) = 0 := by
  let x := (F T M).map (prod.fst : V ⨯ OptionSyntax.obj C ⟶ V) q
  obtain ⟨z,hzx,hza⟩ := modelProduct_exists T M V (⊤_ (PredicateCategory T)) x a
  let k := (prod.map (𝟙 V) (coprod.inl : (⊤_ (PredicateCategory T)) ⟶ OptionSyntax.obj C))
  have hz : (F T M).map k z = q := by
    apply modelProduct_ext T M
    · erw [model_map_fst T M _ _ z,hzx,Functor.map_id_apply]
    · erw [model_map_snd T M _ _ z,hza]
      exact ha.symm
  rw [← hz,← Functor.map_comp_apply,coefficient_failure_map]
  exact optionCode_fail T M z

theorem model_coefficient_success {V C D : PredicateCategory T} (h : V ⨯ C ⟶ D)
    (φ : M → M → M)
    (hf : ∀ z : Obj T M (V ⨯ C), ((F T M).map h z).val =
      φ ((F T M).map (prod.fst : V ⨯ C ⟶ V) z).val ((F T M).map (prod.snd : V ⨯ C ⟶ C) z).val)
    (q : Obj T M (V ⨯ OptionSyntax.obj C)) (y : Obj T M C)
    (hy : (F T M).map (prod.snd : V ⨯ OptionSyntax.obj C ⟶ _) q =
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y) :
    optionCode T M D ((F T M).map (OptionSyntax.coefficient h) q) =
      Arithmetic.pair (φ ((F T M).map (prod.fst : V ⨯ OptionSyntax.obj C ⟶ V) q).val y.val) 1 := by
  let x := (F T M).map (prod.fst : V ⨯ OptionSyntax.obj C ⟶ V) q
  obtain ⟨z,hzx,hzy⟩ := modelProduct_exists T M V C x y
  let k := (prod.map (𝟙 V) (coprod.inr : C ⟶ OptionSyntax.obj C))
  have hz : (F T M).map k z = q := by
    apply modelProduct_ext T M
    · erw [model_map_fst T M _ _ z,hzx,Functor.map_id_apply]
    · erw [model_map_snd T M _ _ z,hzy]
      exact hy.symm
  have he : (F T M).map (OptionSyntax.coefficient h) q =
      (F T M).map (h ≫ coprod.inr) z := by
    rw [← hz,← Functor.map_comp_apply,OptionSyntax.coefficient_ok_map]
  rw [he,Functor.map_comp_apply,optionCode_inr]
  have hv := hf z
  rw [hzx,hzy] at hv
  exact congrArg (fun w => Arithmetic.pair w 1) hv

theorem optionCode_coefficient {V C D : PredicateCategory T} (h : V ⨯ C ⟶ D)
    (φ : M → M → M)
    (hf : ∀ z : Obj T M (V ⨯ C), ((F T M).map h z).val =
      φ ((F T M).map (prod.fst : V ⨯ C ⟶ V) z).val ((F T M).map (prod.snd : V ⨯ C ⟶ C) z).val)
    (q : Obj T M (V ⨯ OptionSyntax.obj C)) :
    optionCode T M D ((F T M).map (OptionSyntax.coefficient h) q) =
      if π₂ (optionCode T M C ((F T M).map prod.snd q)) = 1
      then Arithmetic.pair (φ ((F T M).map (prod.fst : V ⨯ OptionSyntax.obj C ⟶ V) q).val
        (π₁ (optionCode T M C ((F T M).map prod.snd q)))) 1 else 0 := by
  rcases modelSum_cases T M (⊤_ (PredicateCategory T)) C ((F T M).map prod.snd q) with
    ⟨a,ha⟩ | ⟨y,hy⟩
  · have hright : optionCode T M C ((F T M).map prod.snd q) = 0 := by
      rw [← ha]; exact optionCode_inl T M C a
    rw [model_coefficient_failure T M h q a ha.symm,hright]
    simp [pi₂_zero]
  · have hright : optionCode T M C ((F T M).map prod.snd q) = Arithmetic.pair y.val 1 := by
      rw [← hy]; exact optionCode_inr T M C y
    rw [model_coefficient_success T M h φ hf q y hy.symm,hright]
    simp only [pi₂_pair,↓reduceIte,pi₁_pair]

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
