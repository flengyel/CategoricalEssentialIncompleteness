/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation

/-! # Uniqueness of folds retaining the underlying derivation tree -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
open SyntacticDerivation
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
variable (B : Endofunctor.Algebra (PolynomialComparison.ordinary R))

/-- Pair an arbitrary ordinary-tree algebra with the prescribed conclusion.
The target remains a genuine algebra for the original inference functor. -/
def treePairAlgebra : Endofunctor.Algebra R.inference where
  a := Over.mk (prod.fst : F ⨯ B.a ⟶ F)
  str := Over.homMk (prod.lift
    (R.inference.obj (Over.mk (prod.fst : F ⨯ B.a ⟶ F))).hom
    (InputGeometry.forget R (Over.mk (prod.fst : F ⨯ B.a ⟶ F)) ≫
      (PolynomialComparison.ordinary R).map prod.snd ≫ B.str)) (by simp)

def treePairHom (A : Endofunctor.Algebra R.inference) (f : A.a.left ⟶ B.a)
    (hf : A.str.left ≫ f =
      InputGeometry.forget R A.a ≫
        (PolynomialComparison.ordinary R).map f ≫ B.str) :
    A ⟶ treePairAlgebra R B := by
  let g : A.a ⟶ (treePairAlgebra R B).a :=
    Over.homMk (prod.lift A.a.hom f) (by
      change prod.lift A.a.hom f ≫ (prod.fst : F ⨯ B.a ⟶ F) = A.a.hom
      exact prod.lift_fst _ _)
  refine ⟨g,?_⟩
  apply Over.OverMorphism.ext
  change (R.inference.map g).left ≫ prod.lift
      (R.inference.obj (treePairAlgebra R B).a).hom
      (InputGeometry.forget R (treePairAlgebra R B).a ≫
        (PolynomialComparison.ordinary R).map prod.snd ≫ B.str) =
    A.str.left ≫ prod.lift A.a.hom f
  apply prod.hom_ext
  · simp only [Category.assoc,prod.lift_fst]
    exact (Over.w (R.inference.map g)).trans (Over.w A.str).symm
  · simp only [Category.assoc,prod.lift_snd]
    rw [← Category.assoc,InputGeometry.forget_natural,Category.assoc,
      ← Functor.map_comp_assoc]
    have hg : g.left ≫ (prod.snd : F ⨯ B.a ⟶ B.a) = f := by simp [g]
    rw [hg]
    exact hf.symm

/-- Uniqueness is a consequence of the proved slice initiality, even
though the ordinary-tree target need not itself be initial. -/
theorem tree_map_unique (f g : (codeAlgebra R).a.left ⟶ B.a)
    (hf : (codeAlgebra R).str.left ≫ f =
      InputGeometry.forget R (codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map f ≫ B.str)
    (hg : (codeAlgebra R).str.left ≫ g =
      InputGeometry.forget R (codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map g ≫ B.str) : f = g := by
  have h := (codeInitial R).hom_ext (treePairHom R B (codeAlgebra R) f hf) (treePairHom R B (codeAlgebra R) g hg)
  have hp := congrArg (fun k : codeAlgebra R ⟶ treePairAlgebra R B =>
    k.f.left ≫ (prod.snd : F ⨯ B.a ⟶ B.a)) h
  simpa only [treePairHom,Over.homMk_left,prod.lift_snd] using hp

theorem code_tree_unique (f : (codeAlgebra R).a.left ⟶ (ordinaryTree R).a)
    (hf : (codeAlgebra R).str.left ≫ f =
      InputGeometry.forget R (codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map f ≫ (ordinaryTree R).str) :
    f = codeTreeInclusion R :=
  tree_map_unique R (ordinaryTree R) f (codeTreeInclusion R) hf (code_constructor_tree R)

end CategoricalEssentialIncompleteness.V46.NumericalDerivation
