/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformLiftedAction


/-! # Statement checks in `V46MillerSyntaxUniformLiftedActionChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {p q : SyntaxPolynomial (Total.TotalCategory P)}
  {X Y : Over R} (f : uniformWordFamily R false p q ⟶ X)
  (g : uniformWordFamily R true p q ⟶ Y)

example (Q : SyntaxPolynomial (Total.TotalCategory P)) (r u v : ℕ) (hr : r∈R.obj.support)
    (hu : u∈(carrier (uniformWords false p q) (uniformWords true p q) Q).support) :
    ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y f g Q r (constantLift Q r u) v ↔
      Relations.map (fun r => r∈R.obj.support) (candidateRelation f g) (erased Q) r u v :=
  liftedAction_graph f g Q r u v hr hu

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
