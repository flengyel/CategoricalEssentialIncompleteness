/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawActionGraphs


/-! # Statement checks in `V46MillerSyntaxRawActionGraphsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P:Uniform.Family} (R:Total.TotalCategory P) (X Y X' Y':Over R)

example (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) (r u s v:ℕ) :
    Nat.pair s v∈Total.val (((Raw.comparison R X Y p).hom ≫
      (p.withParameters R).eval.map (f,g) ≫ (Raw.comparison R X' Y' p).inv).left.hom) (Nat.pair r u) ↔
      s=r ∧ Raw.ActionGraph R X Y X' Y' f g p r u v :=
  Raw.transportedAction_graph R X Y X' Y' f g p r u s v

example (f:X⟶X') (g:Y⟶Y') (r u s v:ℕ) :
    Nat.pair s v∈Total.val (((Raw.comparison R X Y .unit).hom ≫
      ((SyntaxPolynomial.unit:SyntaxPolynomial (Total.TotalCategory P)).withParameters R).eval.map (f,g) ≫
      (Raw.comparison R X' Y' .unit).inv).left.hom) (Nat.pair r u) ↔
      s=r ∧ r∈R.obj.support ∧ u=0 ∧ v=u := Raw.transportedAction_unit_graph R X Y X' Y' f g r u s v

example (f:X⟶X') (g:Y⟶Y') (C:Total.TotalCategory P) (r label word s label' value:ℕ) :
    Nat.pair s (Nat.pair label' value)∈Total.val (((Raw.comparison R X Y (.product (.coefficient C) .term)).hom ≫
      ((SyntaxPolynomial.product (.coefficient C) .term).withParameters R).eval.map (f,g) ≫
      (Raw.comparison R X' Y' (.product (.coefficient C) .term)).inv).left.hom)
      (Nat.pair r (Nat.pair label word)) ↔
      s=r ∧ (r∈R.obj.support ∧ label∈C.obj.support ∧ label'=label) ∧
        r∈Total.val X.hom.hom word ∧ value∈Total.val f.left.hom word :=
  Raw.transportedAction_coefficient_term_graph R X Y X' Y' f g C r label word s label' value

example (f:X⟶X') (g:Y⟶Y') (a b:SyntaxPolynomial (Total.TotalCategory P)) (r u v u' v':ℕ) :
    Raw.ActionGraph R X Y X' Y' f g (.product a b) r (Nat.pair u v) (Nat.pair u' v') ↔
      Raw.ActionGraph R X Y X' Y' f g a r u u' ∧ Raw.ActionGraph R X Y X' Y' f g b r v v' := by
  simp only [Raw.ActionGraph,Nat.unpair_pair]

example (f:X⟶X') (g:Y⟶Y') (a b:SyntaxPolynomial (Total.TotalCategory P)) (r u v:ℕ) :
    Raw.ActionGraph R X Y X' Y' f g (.sum a b) r (Nat.pair u 0) (Nat.pair v 1) ↔ False := by
  simp [Raw.ActionGraph]
