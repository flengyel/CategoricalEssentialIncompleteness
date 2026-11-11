/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformHomLaws


/-! # Statement checks in `V46MillerSyntaxUniformHomLawsChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P}
  {p q : SyntaxPolynomial (Total.TotalCategory P)}
  (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)))
  (f : Endofunctor.Algebra.Hom (parameterWordAlgebra R p q) B)

example : algebraTermOperation B = (comparison R B.a.1 B.a.2 p).hom ≫ B.str.1 := rfl
example : algebraFormulaOperation B = (comparison R B.a.1 B.a.2 q).hom ≫ B.str.2 := rfl

example : rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
    B.a.1 B.a.2 f.f.1 f.f.2 p ≫ ((comparison R B.a.1 B.a.2 p).hom ≫ B.str.1) =
      parameterConstructor R p q false ≫ f.f.1 := algebraHom_raw_term_constructor B f

example : rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
    B.a.1 B.a.2 f.f.1 f.f.2 q ≫ ((comparison R B.a.1 B.a.2 q).hom ≫ B.str.2) =
      parameterConstructor R p q true ≫ f.f.2 := algebraHom_raw_formula_constructor B f

example : ∀ (formula : Bool) (r u value : ℕ),
    u∈(carrier (uniformWords false p q) (uniformWords true p q)
      (if formula then q else p)).support →
    candidateRelation f.f.1 f.f.2 formula r
      (constructor formula (skeleton (if formula then q else p)) u) value →
    ∃ v,Relations.map (fun r => r∈R.obj.support) (candidateRelation f.f.1 f.f.2)
      (erased (if formula then q else p)) r u v ∧
      operationRelation ((comparison R B.a.1 B.a.2 p).hom ≫ B.str.1)
        ((comparison R B.a.1 B.a.2 q).hom ≫ B.str.2) formula r v value :=
  candidateRelation_rootLaw B f

example (formula : Bool) (word : ℕ) (hw : word∈(uniformWords formula p q).support)
    (r x y : ℕ)
    (hx : candidateRelation f.f.1 f.f.2 formula r word x)
    (hy : foldRelation ((comparison R B.a.1 B.a.2 p).hom ≫ B.str.1)
      ((comparison R B.a.1 B.a.2 q).hom ≫ B.str.2) formula r word y) : x=y :=
  algebraHom_candidate_fold_value B f formula word hw r x y hx hy

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
