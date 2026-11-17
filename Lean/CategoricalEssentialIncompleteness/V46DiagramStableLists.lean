/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NumericalDiagramParameterStability

/-! # Stable list algebras obtained from the full diagram syntax construction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ListAlgebraProjection
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasFiniteCoproducts C]

def expression (V : C) : SyntaxPolynomial C := .sum .unit (.product (.coefficient V) .formula)

variable {V : C} (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit (expression V)))
def algebra : ListAlgebra V :=
  ⟨A.a.2, coprod.inl ≫ A.str.2, coprod.inr ≫ A.str.2⟩

theorem constructor_eq : (algebra A).asAlgebra.str = A.str.2 := by
  apply coprod.hom_ext <;> simp [algebra, ListAlgebra.asAlgebra] <;> rfl

def lift (B : Endofunctor.Algebra (listFunctor V)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit (expression V)) :=
  ⟨(⊤_ C, B.a), (𝟙 _, B.str)⟩

def fold (hA : IsInitial A) (B : Endofunctor.Algebra (listFunctor V)) : (algebra A).asAlgebra ⟶ B where
  f := (hA.to (lift B)).f.2
  h := by
    have h := congrArg Prod.snd (hA.to (lift B)).h
    change (listFunctor V).map (hA.to (lift B)).f.2 ≫ B.str = A.str.2 ≫ _ at h
    rw [constructor_eq]
    exact h

def initial (hA : IsInitial A) : IsInitial (algebra A).asAlgebra :=
  IsInitial.ofUniqueHom (fold A hA) (by
    intro B m
    let n : A ⟶ lift B := {
      f := (terminal.from A.a.1, m.f)
      h := by
        apply Prod.ext
        · exact terminalIsTerminal.hom_ext _ _
        · change (listFunctor V).map m.f ≫ B.str = A.str.2 ≫ m.f
          rw [← constructor_eq A]
          exact m.h }
    exact Endofunctor.Algebra.Hom.ext
      (congrArg (fun f => f.f.2) (hA.hom_ext n (hA.to (lift B)))))

section Parameters
variable [HasFiniteLimits C] (P : C)
abbrev parameterAlgebra := SyntaxPolynomial.algebraWithParameters .unit (expression V) A P

theorem parameter_nil : ((algebra A).withParameters P).nil = (algebra (parameterAlgebra A P)).nil := by
  change _ = coprod.inl ≫
    ((coprod.map (constantUnitComparison P)
      (prod.map (𝟙 _) (𝟙 _) ≫ constantProductComparison P V A.a.2) ≫
        constantCoproductComparison P (⊤_ C) (V ⨯ A.a.2)) ≫ (constantFamilyFunctor P).map A.str.2)
  simp only [Category.assoc, coprod.inl_map_assoc, constantCoproductComparison,
    coprod.inl_desc_assoc, ← CategoryTheory.Functor.map_comp]
  apply Over.OverMorphism.ext
  simp [ListAlgebra.withParameters, algebra, constantUnitComparison, constantFamilyFunctor,
    Over.comp_left]
  rfl

theorem parameter_cons : ((algebra A).withParameters P).cons = (algebra (parameterAlgebra A P)).cons := by
  change _ = coprod.inr ≫
    ((coprod.map (constantUnitComparison P)
      (prod.map (𝟙 _) (𝟙 _) ≫ constantProductComparison P V A.a.2) ≫
        constantCoproductComparison P (⊤_ C) (V ⨯ A.a.2)) ≫ (constantFamilyFunctor P).map A.str.2)
  simp only [Category.assoc, coprod.inr_map_assoc, constantCoproductComparison,
    coprod.inr_desc_assoc, ← CategoryTheory.Functor.map_comp, prod.map_id_id, Category.id_comp]
  apply Over.OverMorphism.ext
  simp [ListAlgebra.withParameters, algebra, constantProductComparison, constantFamilyFunctor,
    Over.comp_left]
  rfl

def parameterIso : (algebra (parameterAlgebra A P)).asAlgebra ≅ ((algebra A).withParameters P).asAlgebra :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (listFunctor (constantFamily P V)).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    apply coprod.hom_ext
    · simpa only [ListAlgebra.asAlgebra, coprod.inl_desc] using parameter_nil A P
    · simpa only [ListAlgebra.asAlgebra, coprod.inr_desc] using parameter_cons A P)
end Parameters
end CategoricalEssentialIncompleteness.V46.ListAlgebraProjection

namespace CategoricalEssentialIncompleteness.V46.DiagramStableLists
variable {J : Type u} [Category.{v} J] [Regular (J ⥤ NumericalTuples.Object)]
variable (V : J ⥤ NumericalTuples.Object)

abbrev data := NumericalDiagramParameterStability.data
  (.unit : SyntaxPolynomial (J ⥤ NumericalTuples.Object)) (ListAlgebraProjection.expression V)

/-- Stable lists exist for arbitrary numerical coefficient diagrams.
The parameter target is any family over the chosen parameter diagram. -/
def stableListAlgebra : StableListAlgebra V where
  algebra := ListAlgebraProjection.algebra (data V).1
  initial := ListAlgebraProjection.initial (data V).1 (data V).2.1
  stable P := (ListAlgebraProjection.initial
    (ListAlgebraProjection.parameterAlgebra (data V).1 P) ((data V).2.2 P)).ofIso
      (ListAlgebraProjection.parameterIso (data V).1 P)
end CategoricalEssentialIncompleteness.V46.DiagramStableLists
