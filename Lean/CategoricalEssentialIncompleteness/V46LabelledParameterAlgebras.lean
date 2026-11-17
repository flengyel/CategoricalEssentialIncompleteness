/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PolynomialParameterValues

/-! # Exact canonical parameter algebras with labelled coefficient positions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.LabelledParameterAlgebras
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w} (c : I → C) (P : C) (X : C × C)

/-- Retain the polynomial and its comparison together, so the equality
compares the actual morphisms across the change of coefficient expression. -/
theorem comparison_data (p : SyntaxPolynomial I) :
    (⟨(p.mapCoefficients c).withParameters P,
      SyntaxPolynomial.parameterComparison P X (p.mapCoefficients c)⟩ :
      Σ r : SyntaxPolynomial (Over P), r.eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
        constantFamily P ((p.mapCoefficients c).eval.obj X)) =
      ⟨p.mapCoefficients (fun i => constantFamily P (c i)),
        PolynomialParameterValues.comparison P c X p⟩ := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient => rfl
  | unit => rfl
  | product p q hp hq =>
      exact congrArg₂ (fun a b =>
        (⟨.product a.1 b.1, prod.map a.2 b.2 ≫ constantProductComparison P
          ((p.mapCoefficients c).eval.obj X) ((q.mapCoefficients c).eval.obj X)⟩ :
          Σ r : SyntaxPolynomial (Over P), r.eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
            constantFamily P (((p.mapCoefficients c).eval.obj X) ⨯ ((q.mapCoefficients c).eval.obj X)))) hp hq
  | sum p q hp hq =>
      exact congrArg₂ (fun a b =>
        (⟨.sum a.1 b.1, coprod.map a.2 b.2 ≫ constantCoproductComparison P
          ((p.mapCoefficients c).eval.obj X) ((q.mapCoefficients c).eval.obj X)⟩ :
          Σ r : SyntaxPolynomial (Over P), r.eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
            constantFamily P (((p.mapCoefficients c).eval.obj X) ⨿ ((q.mapCoefficients c).eval.obj X)))) hp hq

variable (p q : SyntaxPolynomial I)
variable (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (p.mapCoefficients c) (q.mapCoefficients c)))

def algebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (p.mapCoefficients (fun i => constantFamily P (c i)))
    (q.mapCoefficients (fun i => constantFamily P (c i)))) :=
  ⟨(constantFamily P A.a.1, constantFamily P A.a.2),
    (PolynomialParameterValues.comparison P c A.a p ≫ (constantFamilyFunctor P).map A.str.1,
      PolynomialParameterValues.comparison P c A.a q ≫ (constantFamilyFunctor P).map A.str.2)⟩

theorem algebra_data :
    (⟨_, SyntaxPolynomial.algebraWithParameters (p.mapCoefficients c) (q.mapCoefficients c) A P⟩ :
      Σ F : (Over P × Over P) ⥤ (Over P × Over P), Endofunctor.Algebra F) =
      ⟨_, algebra c P p q A⟩ := by
  exact congrArg₂ (fun a b =>
    (⟨SyntaxPolynomial.jointFunctor a.1 b.1,
      ⟨(constantFamily P A.a.1, constantFamily P A.a.2),
        (a.2 ≫ (constantFamilyFunctor P).map A.str.1,
          b.2 ≫ (constantFamilyFunctor P).map A.str.2)⟩⟩ :
      Σ F : (Over P × Over P) ⥤ (Over P × Over P), Endofunctor.Algebra F))
    (comparison_data c P A.a p) (comparison_data c P A.a q)

def toInitial (h : IsInitial (SyntaxPolynomial.algebraWithParameters
    (p.mapCoefficients c) (q.mapCoefficients c) A P)) : IsInitial (algebra c P p q A) := by
  let S := fun z : Σ F : (Over P × Over P) ⥤ (Over P × Over P), Endofunctor.Algebra F => IsInitial z.2
  exact Eq.mp (congrArg S (algebra_data c P p q A)) h

def fromInitial (h : IsInitial (algebra c P p q A)) : IsInitial
    (SyntaxPolynomial.algebraWithParameters (p.mapCoefficients c) (q.mapCoefficients c) A P) := by
  let S := fun z : Σ F : (Over P × Over P) ⥤ (Over P × Over P), Endofunctor.Algebra F => IsInitial z.2
  exact Eq.mp (congrArg S (algebra_data c P p q A)).symm h
end CategoricalEssentialIncompleteness.V46.LabelledParameterAlgebras
