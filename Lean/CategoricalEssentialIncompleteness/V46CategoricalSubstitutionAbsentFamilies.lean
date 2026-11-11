/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentInvariant

/-! The equalizer invariant as an equation of parameter-family morphisms. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.AbsentFamilies
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P V U Y : D} (L : StableListAlgebra V) (E : DecidableVariables V)
  (name : P ⟶ V) (FV : U ⟶ L.algebra.carrier) (embed : U ⟶ Y)
attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

def test : P ⨯ (U ⨯ Y) ⟶ Two D :=
  prod.lift (prod.fst ≫ name) (prod.snd ≫ prod.fst ≫ FV) ≫ L.membership E

def mask : constantFamily P (U ⨯ Y) ⟶ constantFamily P Y :=
  parameterHom (Two.branch (test L E name FV)
    (prod.snd ≫ prod.fst ≫ embed) (prod.snd ≫ prod.snd))

def result : constantFamily P (U ⨯ Y) ⟶ constantFamily P Y :=
  parameterHom (prod.snd ≫ prod.snd)

/-- Pair an original value and a computed result over their common parameter. -/
def pairFamily {X : Over P} (original : X ⟶ constantFamily P U)
    (computed : X ⟶ constantFamily P Y) : X ⟶ constantFamily P (U ⨯ Y) :=
  Over.homMk (prod.lift X.hom
    (prod.lift (original.left ≫ prod.snd) (computed.left ≫ prod.snd))) (by
      simp [constantFamily])

omit [FinitaryExtensive D] in
@[simp, reassoc] theorem pairFamily_original {X : Over P}
    (original : X ⟶ constantFamily P U) (computed : X ⟶ constantFamily P Y) :
    pairFamily original computed ≫ (constantFamilyFunctor P).map prod.fst = original := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simp [pairFamily, constantFamilyFunctor]

omit [FinitaryExtensive D] in
@[simp, reassoc] theorem pairFamily_result {X : Over P}
    (original : X ⟶ constantFamily P U) (computed : X ⟶ constantFamily P Y) :
    pairFamily original computed ≫ (constantFamilyFunctor P).map prod.snd = computed := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simp [pairFamily, constantFamilyFunctor]

omit [FinitaryExtensive D] in
@[simp] theorem pairFamily_natural {X Z : Over P} (k : Z ⟶ X)
    (original : X ⟶ constantFamily P U) (computed : X ⟶ constantFamily P Y) :
    k ≫ pairFamily original computed = pairFamily (k ≫ original) (k ≫ computed) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simp [pairFamily, Over.comp_left, prod.comp_lift, Category.assoc]

omit [FinitaryExtensive D] in
theorem product_hom_ext {X : Over P}
    (f g : X ⟶ constantFamily P (U ⨯ Y))
    (hf : f ≫ (constantFamilyFunctor P).map prod.fst =
      g ≫ (constantFamilyFunctor P).map prod.fst)
    (hg : f ≫ (constantFamilyFunctor P).map prod.snd =
      g ≫ (constantFamilyFunctor P).map prod.snd) : f = g := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · apply prod.hom_ext
    · simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
        Category.assoc, prod.map_snd] using congrArg (fun h => h.left ≫ prod.snd) hf
    · simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
        Category.assoc, prod.map_snd] using congrArg (fun h => h.left ≫ prod.snd) hg

/-- A parameter-family equation expresses the conditional equality exactly. -/
theorem equation_iff {X : Over P} (m : X ⟶ constantFamily P (U ⨯ Y)) :
    m ≫ mask L E name FV embed = m ≫ result ↔
      ConditionalInvariant.Holds
        (prod.lift (X.hom ≫ name) (m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫ L.membership E)
        (m.left ≫ prod.snd ≫ prod.fst ≫ embed) (m.left ≫ prod.snd ≫ prod.snd) := by
  have hb : m.left ≫ prod.fst = X.hom := Over.w m
  have hb' : m.left ≫ prod.fst ≫ name = X.hom ≫ name := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ name) hb
  have ht : m.left ≫ test L E name FV =
      prod.lift (X.hom ≫ name) (m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫ L.membership E := by
    simp only [test, prod.comp_lift_assoc, hb']
  constructor
  · intro h
    have hh := congrArg (fun f => f.left ≫ prod.snd) h
    simpa only [mask, result, parameterHom, Over.comp_left, Over.homMk_left,
      prod.lift_snd, branch_natural, ConditionalInvariant.Holds, Category.assoc, ht] using hh
  · intro h
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w _).trans (Over.w _).symm
    · simpa only [mask, result, parameterHom, Over.comp_left, Over.homMk_left,
        prod.lift_snd, branch_natural, ConditionalInvariant.Holds, Category.assoc, ht] using h

theorem fixed_of_equation {X : Over P} (m : X ⟶ constantFamily P (U ⨯ Y))
    (hm : m ≫ mask L E name FV embed = m ≫ result) {Z : D} (k : Z ⟶ X.left)
    (ha : prod.lift (k ≫ X.hom ≫ name) (k ≫ m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫
      L.membership E = Two.constant Z false) :
    k ≫ m.left ≫ prod.snd ≫ prod.snd = k ≫ m.left ≫ prod.snd ≫ prod.fst ≫ embed := by
  have h := (equation_iff L E name FV embed m).mp hm
  apply ConditionalInvariant.fixed_of_false h k
  simpa only [prod.comp_lift_assoc, Category.assoc] using ha

theorem equation_of_fixed {X : Over P} (m : X ⟶ constantFamily P (U ⨯ Y))
    (h : ∀ {Z : D} (k : Z ⟶ X.left),
      prod.lift (k ≫ X.hom ≫ name) (k ≫ m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫
        L.membership E = Two.constant Z false →
      k ≫ m.left ≫ prod.snd ≫ prod.snd =
        k ≫ m.left ≫ prod.snd ≫ prod.fst ≫ embed) :
    m ≫ mask L E name FV embed = m ≫ result := by
  apply (equation_iff L E name FV embed m).mpr
  apply ConditionalInvariant.holds_of_false_fiber
  exact h _ (by
    simpa only [prod.comp_lift_assoc, Category.assoc] using
      (Two.fiberι_comp
        (prod.lift (X.hom ≫ name) (m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫ L.membership E) false))

end CategoricalEssentialIncompleteness.V46.AbsentFamilies
