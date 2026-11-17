/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46DiagramParameterConstructor
public import CategoricalEssentialIncompleteness.V46LabelledParameterAlgebras
public import CategoricalEssentialIncompleteness.V46SliceAlgebraInitiality

/-! # Parameter stability of the complete two-sorted numerical diagram algebra -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalDiagramParameterStability
abbrev C := NumericalTuples.Object
variable {J : Type u} [Category.{v} J] [Regular (J ⥤ C)] {I : Type w}
variable (c : I → J ⥤ C) (p q : SyntaxPolynomial I)
abbrev algebra := NumericalCanonicalDiagramSyntax.algebra c p q
abbrev localAlgebra (j : J) := NumericalDiagramSyntax.componentAlgebra c p q j

omit [Regular (J ⥤ C)] in
theorem constructor_square (j : J) :
    ((algebra c p q).str.1.app j, (algebra c p q).str.2.app j) =
      (NumericalCanonicalDiagramSyntax.comparisonHom c p q (algebra c p q).a).app j ≫
        (localAlgebra c p q j).str := by
  have h := congrArg (fun m => m.app j)
    (NumericalCanonicalDiagramSyntax.constructorIso c p q).hom.h
  change ((NumericalDiagramSyntax.polynomials c p q).obj j).map
      (𝟙 (localAlgebra c p q j).a) ≫ (localAlgebra c p q j).str =
    ((inv (NumericalCanonicalDiagramSyntax.comparisonHom c p q (algebra c p q).a)).app j ≫
      ((algebra c p q).str.1.app j, (algebra c p q).str.2.app j)) ≫ 𝟙 _ at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  have hh := congrArg (fun m =>
    (NumericalCanonicalDiagramSyntax.comparisonHom c p q (algebra c p q).a).app j ≫ m) h
  erw [← Category.assoc, ← NatTrans.comp_app, IsIso.hom_inv_id] at hh
  simpa only [NatTrans.id_app, Category.id_comp] using hh.symm

variable (P : J ⥤ C)
abbrev source := LabelledParameterAlgebras.algebra c P p q (algebra c p q)
abbrev localSource (j : J) := LabelledParameterAlgebras.algebra
  (fun i => (c i).obj j) (P.obj j) p q (localAlgebra c p q j)

def sourceIso (j : J) : SliceAlgebraInitiality.component c P p q (source c p q P) j ≅
    localSource c p q P j := by
  refine Endofunctor.Algebra.isoMk (Iso.prod
    (SliceEvaluation.coefficientIso P (algebra c p q).a.1 j)
    (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j)) ?_
  apply Prod.ext
  · apply (cancel_epi (SlicePolynomialComparison.component c P p (source c p q P).a j)).mp
    have h := DiagramParameterConstructor.square c P (algebra c p q).a p
      (algebra c p q).str.1 j (localAlgebra c p q j).str.1
        (congrArg Prod.fst (constructor_square c p q j))
    change SlicePolynomialComparison.component c P p (source c p q P).a j ≫
      ((p.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j)).eval.map
        (((SliceEvaluation.coefficientIso P (algebra c p q).a.1 j).hom,
          (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j).hom) :
            SlicePolynomialComparison.localCarrier P (source c p q P).a j ⟶
              (localSource c p q P j).a) ≫
        (localSource c p q P j).str.1) =
      SlicePolynomialComparison.component c P p (source c p q P).a j ≫
        ((inv (SlicePolynomialComparison.component c P p (source c p q P).a j) ≫
          (SliceEvaluation.componentFunctor P j).map (source c p q P).str.1) ≫
            (SliceEvaluation.coefficientIso P (algebra c p q).a.1 j).hom)
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hι : SliceParameterConstructorComparison.relativeInput c P (algebra c p q).a p j =
        SlicePolynomialComparison.component c P p (source c p q P).a j ≫
          (p.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j)).eval.map
            (((SliceEvaluation.coefficientIso P (algebra c p q).a.1 j).hom,
              (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j).hom) :
                SlicePolynomialComparison.localCarrier P (source c p q P).a j ⟶
                  (localSource c p q P j).a) := rfl
    rw [hι] at h
    have hκ : (localSource c p q P j).str.1 =
        PolynomialParameterValues.comparison (P.obj j) (fun i => (c i).obj j)
          ((algebra c p q).a.1.obj j, (algebra c p q).a.2.obj j) p ≫
            (constantFamilyFunctor (P.obj j)).map (localAlgebra c p q j).str.1 := rfl
    rw [hκ]
    simpa only [source, LabelledParameterAlgebras.algebra, Category.assoc] using h.symm
  · apply (cancel_epi (SlicePolynomialComparison.component c P q (source c p q P).a j)).mp
    have h := DiagramParameterConstructor.square c P (algebra c p q).a q
      (algebra c p q).str.2 j (localAlgebra c p q j).str.2
        (congrArg Prod.snd (constructor_square c p q j))
    change SlicePolynomialComparison.component c P q (source c p q P).a j ≫
      ((q.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j)).eval.map
        (((SliceEvaluation.coefficientIso P (algebra c p q).a.1 j).hom,
          (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j).hom) :
            SlicePolynomialComparison.localCarrier P (source c p q P).a j ⟶
              (localSource c p q P j).a) ≫
        (localSource c p q P j).str.2) =
      SlicePolynomialComparison.component c P q (source c p q P).a j ≫
        ((inv (SlicePolynomialComparison.component c P q (source c p q P).a j) ≫
          (SliceEvaluation.componentFunctor P j).map (source c p q P).str.2) ≫
            (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j).hom)
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hι : SliceParameterConstructorComparison.relativeInput c P (algebra c p q).a q j =
        SlicePolynomialComparison.component c P q (source c p q P).a j ≫
          (q.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j)).eval.map
            (((SliceEvaluation.coefficientIso P (algebra c p q).a.1 j).hom,
              (SliceEvaluation.coefficientIso P (algebra c p q).a.2 j).hom) :
                SlicePolynomialComparison.localCarrier P (source c p q P).a j ⟶
                  (localSource c p q P j).a) := rfl
    rw [hι] at h
    have hκ : (localSource c p q P j).str.2 =
        PolynomialParameterValues.comparison (P.obj j) (fun i => (c i).obj j)
          ((algebra c p q).a.1.obj j, (algebra c p q).a.2.obj j) q ≫
            (constantFamilyFunctor (P.obj j)).map (localAlgebra c p q j).str.2 := rfl
    rw [hκ]
    simpa only [source, LabelledParameterAlgebras.algebra, Category.assoc] using h.symm

def componentInitial (j : J) : IsInitial
    (SliceAlgebraInitiality.component c P p q (source c p q P) j) :=
  (LabelledParameterAlgebras.toInitial (fun i => (c i).obj j) (P.obj j) p q
    (localAlgebra c p q j) (NumericalDiagramSyntax.componentStable c p q j (P.obj j))).ofIso
      (sourceIso c p q P j).symm

def labelledInitial : IsInitial (source c p q P) :=
  SliceAlgebraInitiality.initial c P p q (source c p q P) (componentInitial c p q P)

/-- Exact canonical parameter initiality for both recursive sorts,
every coefficient diagram and every target family in the global slice. -/
def stable : IsInitial (SyntaxPolynomial.algebraWithParameters
    (p.mapCoefficients c) (q.mapCoefficients c) (algebra c p q) P) :=
  LabelledParameterAlgebras.fromInitial c P p q (algebra c p q) (labelledInitial c p q P)

def data (r s : SyntaxPolynomial (J ⥤ C)) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s),
      IsInitial A × (∀ P : J ⥤ C, IsInitial (SyntaxPolynomial.algebraWithParameters r s A P)) := by
  let S := fun a b : SyntaxPolynomial (J ⥤ C) =>
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b),
      IsInitial A × (∀ P : J ⥤ C, IsInitial (SyntaxPolynomial.algebraWithParameters a b A P))
  have h : S (r.mapCoefficients id) (s.mapCoefficients id) :=
    ⟨algebra id r s, NumericalCanonicalDiagramSyntax.initial id r s, stable id r s⟩
  exact Eq.mp (congrArg₂ S (SyntaxPolynomial.mapCoefficients_id r)
    (SyntaxPolynomial.mapCoefficients_id s)) h
end CategoricalEssentialIncompleteness.V46.NumericalDiagramParameterStability
