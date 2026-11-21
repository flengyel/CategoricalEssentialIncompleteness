/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra
public import CategoricalEssentialIncompleteness.V46MillerDerivationValidation
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSort

/-! # Ordinary rule-labelled tree algebra with uniform coefficients

The coefficient in each finite summand is the supplied rule-instance object, including
nullary rules. The constructor comparison is constructed before any initiality
assertion. The base initiality proof is to be instantiated from the uniform syntax
universal property.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)

abbrev treePolynomial : SyntaxPolynomial (Total.TotalCategory P) :=
  SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N

abbrev treePair : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (treePolynomial R) .unit) :=
  Syntax.Raw.wordAlgebra (treePolynomial R) .unit

def oneSortTree : Endofunctor.Algebra (SyntacticSyntax.constructorFunctor (PolynomialComparison.coefficients R) N) :=
  SyntacticSyntax.projectedConstructorAlgebra (PolynomialComparison.coefficients R) N (treePair R)

def ordinaryTree : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  PolynomialComparison.mappedAlgebra R (oneSortTree R)

theorem ordinaryTree_carrier : (ordinaryTree R).a=
    Syntax.Raw.wordObject false (treePolynomial R) .unit := rfl

def ordinaryInputIso :
    (⟨Syntax.Raw.carrier
      (Syntax.Raw.uniformWords false (treePolynomial R) .unit)
      (Syntax.Raw.uniformWords true (treePolynomial R) .unit) (treePolynomial R)⟩ : Total.TotalCategory P) ≅
      (PolynomialComparison.ordinary R).obj (ordinaryTree R).a :=
  Syntax.Raw.baseComparison (treePair R).a.1 (treePair R).a.2 (treePolynomial R) ≪≫
    asIso (SyntacticSyntax.constructorProjection (PolynomialComparison.coefficients R) N (treePair R)) ≪≫
      (PolynomialComparison.comparison R).app (ordinaryTree R).a

/-- Under the input chart the constructor is the original successful-word constructor,
preserving its rule label and child order. -/
theorem ordinaryInputIso_constructor :
    (ordinaryInputIso R).hom ≫ (ordinaryTree R).str=
      Syntax.Raw.rawWordConstructor (treePolynomial R) .unit false := by
  change ((Syntax.Raw.baseComparison _ _ _).hom ≫
    SyntacticSyntax.constructorProjection (PolynomialComparison.coefficients R) N (treePair R) ≫
    (PolynomialComparison.comparison R).hom.app _) ≫ (ordinaryTree R).str=_
  have hm : (PolynomialComparison.comparison R).hom.app (ordinaryTree R).a ≫ (ordinaryTree R).str=
      (oneSortTree R).str := by
    simp [ordinaryTree,PolynomialComparison.mappedAlgebra,PolynomialComparison.endofunctorComparison,
      AlgebraTransport.mappedAlgebra]
  erw [Category.assoc,Category.assoc,hm]
  change (Syntax.Raw.baseComparison _ _ _).hom ≫
    (SyntacticSyntax.constructorProjection (PolynomialComparison.coefficients R) N (treePair R) ≫
      (inv (SyntacticSyntax.constructorProjection (PolynomialComparison.coefficients R) N (treePair R)) ≫
        (treePair R).str.1))=_
  rw [IsIso.hom_inv_id_assoc]
  exact Syntax.Raw.wordAlgebra_term_constructor (treePolynomial R) .unit

def branchConstructor (i : Fin (N+1)) :
    R.instances i ⨯ finitePower (ordinaryTree R).a i.val ⟶ (ordinaryTree R).a :=
  Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (ordinaryTree R).a j.val) i ≫
    (ordinaryTree R).str

theorem branch_label (i : Fin (N+1)) :
    PolynomialComparison.injection (PolynomialComparison.coefficients R) (ordinaryTree R).a N i ≫
      (PolynomialComparison.comparison R).hom.app (ordinaryTree R).a ≫ (ordinaryTree R).str=
        prod.map (eqToHom (PolynomialComparison.coefficients_fin R i)) (𝟙 _) ≫ branchConstructor R i := by
  rw [← Category.assoc,PolynomialComparison.injection_comparison,Category.assoc]
  rfl

end CategoricalEssentialIncompleteness.V46.Miller.Derivation
