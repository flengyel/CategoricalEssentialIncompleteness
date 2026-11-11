/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationGluing
public import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # Initiality on the actual natural fork of finite derivations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

/-- The carrier and conclusion are the original finite proof fork. -/
def inferenceAlgebra (a b : Idem EffectiveFork.V) : Endofunctor.Algebra (rules a b).inference where
  a := proofSlice a b
  str := Over.homMk (fromComponents (constructorComponent a b) (fun {_j _k} g => constructorComponents_natural a b g)) (by
    apply component_jointly_faithful
    intro j
    rw [Functor.map_comp,component_fromComponents]
    exact constructorComponent_conclusion a b j)

@[simp] theorem inference_carrier (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a = proofSlice a b := rfl

@[simp] theorem inference_conclusion (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a.hom =
      (⟨ForkSyntax.conclusion a b,ForkSyntax.conclusion_total a b⟩ :
        (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) ⟶ (⟨ForkSyntax.S⟩ : EffectiveFork.Total)) := rfl

theorem component_inferenceConstructor (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (inferenceAlgebra a b).str.left = constructorComponent a b j :=
  component_fromComponents (constructorComponent a b) (fun {_j _k} g => constructorComponents_natural a b g) j

theorem component_inferenceConstructor_native (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (inferenceAlgebra a b).str.left ≫ (componentProofIso a b j).hom =
      (componentInputIso a b (proofSlice a b) j).hom ≫
        ((nativeRules a b j).inference.map (componentProofSliceIso a b j).hom).left ≫
          (nativeAlgebra a b j).str.left := by
  rw [component_inferenceConstructor]
  exact constructorComponent_native a b j

/-- Mapping the constructed global constructor recovers the actual
pointwise algebra, not an evaluator supplied as an assumption. -/
def component_inferenceIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    componentAlgebra a b (inferenceAlgebra a b) j ≅ pointwiseAlgebra a b j :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    erw [Iso.refl_hom,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
    apply Over.OverMorphism.ext
    rw [componentAlgebra_str_left,component_inferenceConstructor]
    change (pointwiseAlgebra a b j).str.left =
      (componentInputIso a b (proofSlice a b) j).inv ≫ constructorComponent a b j
    rw [constructorComponent]
    erw [← Category.assoc,Iso.inv_hom_id,Category.id_comp])

def component_inferenceInitial (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    IsInitial (componentAlgebra a b (inferenceAlgebra a b) j) :=
  (pointwiseInitial a b j).ofIso (component_inferenceIso a b j).symm

@[simp] theorem component_inferenceIso_hom_left (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (component_inferenceIso a b j).hom.f.left = 𝟙 _ := rfl

def foldCarrier (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) : proofObject a b ⟶ B.a.left :=
  fromComponents (foldedComponent a b B) (fun {_j _k} g => foldComponents_natural a b B g)

@[simp] theorem foldCarrier_component (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentFunctor j).map (foldCarrier a b B) = foldedComponent a b B j :=
  component_fromComponents (foldedComponent a b B) (fun {_j _k} g => foldComponents_natural a b B g) j

theorem fold_conclusion (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) : foldCarrier a b B ≫ B.a.hom = conclusion a b := by
  apply component_jointly_faithful
  intro j
  rw [Functor.map_comp,foldCarrier_component]
  exact foldedComponent_conclusion a b B j

def foldHom (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference) :
    inferenceAlgebra a b ⟶ B where
  f := Over.homMk (foldCarrier a b B) (fold_conclusion a b B)
  h := by
    apply Over.OverMorphism.ext
    apply component_jointly_faithful
    intro j
    let m := (component_inferenceIso a b j).hom ≫ foldedComponentHom a b B j
    have he : componentOverMap
        (Over.homMk (foldCarrier a b B) (fold_conclusion a b B)) j = m.f := by
      apply Over.OverMorphism.ext
      change (componentFunctor j).map (foldCarrier a b B) =
        ((component_inferenceIso a b j).hom ≫ foldedComponentHom a b B j).f.left
      erw [Endofunctor.Algebra.comp_f,Over.comp_left,
        component_inferenceIso_hom_left,Category.id_comp]
      exact foldCarrier_component a b B j
    have hm := m.h
    rw [← he] at hm
    exact (component_hom_condition a b (inferenceAlgebra a b) B
      (Over.homMk (foldCarrier a b B) (fold_conclusion a b B)) j).mp hm

theorem fold_unique (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (m : inferenceAlgebra a b ⟶ B) :
    m = foldHom a b B := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  apply component_jointly_faithful
  intro j
  let v := (component_inferenceIso a b j).hom ≫ foldedComponentHom a b B j
  have he := (component_inferenceInitial a b j).hom_ext
    ((toComponentAlgebra a b j).map m) v
  have hv := congrArg (fun h => h.f.left) he
  simpa only [toComponentAlgebra_map_left,v,Endofunctor.Algebra.comp_f,
    Over.comp_left,component_inferenceIso_hom_left,Category.id_comp,foldedComponent,
    foldHom,Over.homMk_left,foldCarrier_component] using hv

/-- Initiality quantifies over all natural computable slice-algebra morphisms. -/
def inferenceInitial (a b : Idem EffectiveFork.V) : IsInitial (inferenceAlgebra a b) :=
  IsInitial.ofUniqueHom (foldHom a b) (by intro B m; exact fold_unique a b B m)

def printedComparison (a b : Idem EffectiveFork.V) :
    (rules a b).inference ⋙ 𝟭 (Over sentenceObject) ≅
      𝟭 (Over sentenceObject) ⋙ printedH a b :=
  Functor.rightUnitor (rules a b).inference ≪≫ inferenceIso a b ≪≫
    (Functor.leftUnitor (printedH a b)).symm

def printedAlgebra (a b : Idem EffectiveFork.V) : Endofunctor.Algebra (printedH a b) :=
  AlgebraTransport.mappedAlgebra (CategoryTheory.Equivalence.refl (C := Over sentenceObject))
    (printedComparison a b) (inferenceAlgebra a b)

theorem printed_constructor (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).str =
      (inferenceIso a b).inv.app (proofSlice a b) ≫ (inferenceAlgebra a b).str := by
  simp [printedAlgebra,AlgebraTransport.mappedAlgebra,printedComparison]

def printedInitial (a b : Idem EffectiveFork.V) : IsInitial (printedAlgebra a b) :=
  AlgebraTransport.initial (CategoryTheory.Equivalence.refl (C := Over sentenceObject))
    (printedComparison a b) (inferenceAlgebra a b) (inferenceInitial a b)


@[simp] theorem printed_carrier (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).a = proofSlice a b := rfl

/-- The printed universal property for every supplied algebra structure,
with uniqueness among all natural computable slice morphisms. -/
theorem printed_unique (a b : Idem EffectiveFork.V) (Q : EffectiveFork.Total)
    (q : Q ⟶ sentenceObject)
    (η : (printedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : proofSlice a b ⟶ Over.mk q,
      (printedH a b).map u ≫ η = (printedAlgebra a b).str ≫ u := by
  let B : Endofunctor.Algebra (printedH a b) := ⟨Over.mk q,η⟩
  let m := (printedInitial a b).to B
  refine ⟨m.f,m.h,?_⟩
  intro u hu
  exact congrArg Endofunctor.Algebra.Hom.f
    ((printedInitial a b).hom_ext (⟨u,hu⟩ : printedAlgebra a b ⟶ B) m)
end CategoricalEssentialIncompleteness.V46.ForkDerivation
