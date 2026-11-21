/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFoldCommutation


/-! # Constructor commutation of the uniform fold -/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {p q : SyntaxPolynomial (Total.TotalCategory P)}
  {X Y : Over R} (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

example (formula : Bool) :
    rawAction R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y (uniformFold hT hF false) (uniformFold hT hF true)
      (if formula then q else p) ≫ chosenOperation hT hF formula =
      parameterConstructor R p q formula ≫ uniformFold hT hF formula :=
  uniformFold_raw_commutes hT hF formula

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
