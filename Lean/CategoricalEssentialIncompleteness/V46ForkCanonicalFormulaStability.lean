/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkCanonicalFormulaSource

/-! # Canonical formula initiality in every fork parameter slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.AlgebraEvaluation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (F : C ⥤ D) {K : C ⥤ C} {L : D ⥤ D} (α : K ⋙ F ≅ F ⋙ L)

def algebra (A : Endofunctor.Algebra K) : Endofunctor.Algebra L :=
  ⟨F.obj A.a, α.inv.app A.a ≫ F.map A.str⟩

/-- No faithfulness assumption is needed to compare an evaluated
constructor equation with the local algebra-morphism equation. -/
theorem hom_condition_iff (A B : Endofunctor.Algebra K) (f : A.a ⟶ B.a) :
    L.map (F.map f) ≫ (algebra F α B).str = (algebra F α A).str ≫ F.map f ↔
      F.map (K.map f ≫ B.str) = F.map (A.str ≫ f) := by
  change L.map (F.map f) ≫ (α.inv.app B.a ≫ F.map B.str) =
    (α.inv.app A.a ≫ F.map A.str) ≫ F.map f ↔ _
  have hn : L.map (F.map f) ≫ α.inv.app B.a = α.inv.app A.a ≫ F.map (K.map f) := by
    simpa only [Functor.comp_map] using α.inv.naturality f
  rw [← Category.assoc, hn, Category.assoc, Category.assoc,
    ← F.map_comp, ← F.map_comp, cancel_epi]
end CategoricalEssentialIncompleteness.V46.AlgebraEvaluation

namespace CategoricalEssentialIncompleteness.V46.ForkCanonicalFormulaStability
open ForkFirstOrderFormula
variable (D P : Object)
abbrev source := ForkCanonicalFormulaSource.algebra D P
abbrev localPolynomial (j : WalkingSpan) :=
  ForkFormulaParameterComponents.polynomial (numbers.obj j) (D.obj j) (P.obj j)

def componentIso (j : WalkingSpan) :
    ForkCanonicalParameterTargets.polynomial D P ⋙ SliceEvaluation.componentFunctor P j ≅
      SliceEvaluation.componentFunctor P j ⋙ localPolynomial D P j :=
  NatIso.ofComponents (fun Y => asIso (SlicePolynomialComparison.component
    (ForkCanonicalParameterTargets.coefficients D) P ForkFormulaParameterChange.template
      (⊤_ (Over P), Y) j)) (by
        intro X Y m
        exact LaxPolynomialComparison.naturality (SliceEvaluation.componentFunctor P j)
          (fun i => (SliceEvaluation.coefficientIso P
            (ForkCanonicalParameterTargets.coefficients D i) j).hom)
          ForkFormulaParameterChange.template
          ((𝟙 (⊤_ (Over P)), m) : (⊤_ (Over P), X) ⟶ (⊤_ (Over P), Y)))

abbrev componentAlgebra (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P))
    (j : WalkingSpan) :=
  AlgebraEvaluation.algebra (SliceEvaluation.componentFunctor P j) (componentIso D P j) B

def sourceIso (j : WalkingSpan) : componentAlgebra D P (source D P) j ≅
    ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j) :=
  Endofunctor.Algebra.isoMk
    (SliceEvaluation.coefficientIso P (ForkCanonicalFormulaSource.carrier D) j)
    (ForkCanonicalFormulaSource.source_hom D P j)

def componentInitial (j : WalkingSpan) : IsInitial (componentAlgebra D P (source D P) j) :=
  (ForkFormulaParameterComponents.initial (numbers.obj j) (D.obj j) (P.obj j)).ofIso
    (sourceIso D P j).symm

theorem fold_component (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P))
    (j : WalkingSpan) :
    (SliceEvaluation.componentFunctor P j).map (ForkCanonicalParameterTargets.constantFold D P B) =
      (SliceEvaluation.coefficientIso P (ForkCanonicalFormulaSource.carrier D) j).hom ≫
        (ForkParameterizedFormulaFolds.componentFold D P
          (ForkCanonicalParameterTargets.target D P B) j).f := by
  apply Over.OverMorphism.ext
  rfl

theorem fold_local_constructor
    (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P)) (j : WalkingSpan) :
    (localPolynomial D P j).map ((SliceEvaluation.componentFunctor P j).map
        (ForkCanonicalParameterTargets.constantFold D P B)) ≫ (componentAlgebra D P B j).str =
      (componentAlgebra D P (source D P) j).str ≫ (SliceEvaluation.componentFunctor P j).map
        (ForkCanonicalParameterTargets.constantFold D P B) := by
  simp only [fold_component, Functor.map_comp, Category.assoc]
  erw [(ForkParameterizedFormulaFolds.componentFold D P
    (ForkCanonicalParameterTargets.target D P B) j).h]
  rw [← Category.assoc, ForkCanonicalFormulaSource.source_hom D P j, Category.assoc]
  rfl

/-- The global constructor equation is proved for the exact canonical
parameter source, with every canonical target family included. -/
theorem fold_constructor (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P)) :
    (ForkCanonicalParameterTargets.polynomial D P).map
        (ForkCanonicalParameterTargets.constantFold D P B) ≫ B.str =
      (source D P).str ≫ ForkCanonicalParameterTargets.constantFold D P B := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext j
  exact congrArg Over.Hom.left
    ((AlgebraEvaluation.hom_condition_iff (SliceEvaluation.componentFunctor P j)
      (componentIso D P j) (source D P) B _).mp (fold_local_constructor D P B j))

def fold (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P)) :
    source D P ⟶ B := ⟨ForkCanonicalParameterTargets.constantFold D P B, fold_constructor D P B⟩

/-- Initiality holds in the actual global slice algebra category, with
uniqueness among all algebra morphisms. -/
def initial : IsInitial (source D P) :=
  IsInitial.ofUniqueHom (fold D P) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    exact congrArg (fun n => n.f.left) ((componentInitial D P j).hom_ext
      (⟨(SliceEvaluation.componentFunctor P j).map m.f,
        (AlgebraEvaluation.hom_condition_iff (SliceEvaluation.componentFunctor P j)
          (componentIso D P j) (source D P) B m.f).mpr
          (congrArg (SliceEvaluation.componentFunctor P j).map m.h)⟩ :
        componentAlgebra D P (source D P) j ⟶ componentAlgebra D P B j)
      (⟨_, fold_local_constructor D P B j⟩ :
        componentAlgebra D P (source D P) j ⟶ componentAlgebra D P B j)))

theorem fold_underlying_unique
    (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P))
    (m : (source D P).a ⟶ B.a)
    (hm : (ForkCanonicalParameterTargets.polynomial D P).map m ≫ B.str = (source D P).str ≫ m) :
    m = (fold D P B).f :=
  congrArg Endofunctor.Algebra.Hom.f ((initial D P).hom_ext (⟨m, hm⟩ : source D P ⟶ B) _)
end CategoricalEssentialIncompleteness.V46.ForkCanonicalFormulaStability
