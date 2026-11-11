/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFoldUnique


/-! # Statement checks in `V46MillerSyntaxUniformFoldUniqueChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
  {p q : SyntaxPolynomial (Total.TotalCategory P)}
  (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

example : UniformRootLaw p q (fun r => r∈R.obj.support)
    (operationRelation hT hF) (foldRelation hT hF) := foldRelation_rootLaw hT hF

example (S : Relations.Relation)
    (hS : UniformRootLaw p q (fun r => r∈R.obj.support) (operationRelation hT hF) S)
    (formula : Bool) (word : ℕ) (hw : word∈(uniformWords formula p q).support)
    (r x y : ℕ) (hx : S formula r word x) (hy : foldRelation hT hF formula r word y) : x=y :=
  candidate_fold_value hT hF S hS formula word hw r x y hx hy

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
