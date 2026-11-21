/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionRank


/-! # Strict decrease for every typed child of a uniform proof -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example (i : Fin (N+1)) (k : Fin i.val) :
    Derivation.WordInduction.typedChild R i k ≫ Derivation.wordConclusion R=
      Derivation.WordInduction.typedPremise R i k :=
  Derivation.WordInduction.typedChild_conclusion R i k
example (i : Fin (N+1))
    (r : (Total.underlying (P := P)).obj (R.ruleObject (Derivation.wordAlgebra R).a i)) (k : Fin i.val) :
    FFL.FirstOrder.Arithmetic.len ((Total.underlying (P := P)).map
      (Derivation.WordInduction.typedChild R i k) r).val<
      FFL.FirstOrder.Arithmetic.len ((Total.underlying (P := P)).map
        (Derivation.WordInduction.constructor R i) r).val :=
  Derivation.WordInduction.typed_children_smaller R i r k

example (i : Fin (N+1)) :
    Derivation.WordInduction.constructor R i=Derivation.wordConstructor R i :=
  Derivation.WordInduction.constructor_eq_wordConstructor R i
example (i : Fin (N+1)) :
    Derivation.WordInduction.constructor R i ≫ Derivation.wordInclusion R=
      SyntacticDerivation.CheckedRoot.matchingMap R (Derivation.wordAlgebra R).a i ≫
        prod.map (𝟙 (R.instances i)) (finitePowerMap (Derivation.wordInclusion R) i.val) ≫
        Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (Derivation.ordinaryTree R).a j.val) i ≫
          (Derivation.ordinaryTree R).str :=
  Derivation.WordInduction.typed_constructor_tree R i
