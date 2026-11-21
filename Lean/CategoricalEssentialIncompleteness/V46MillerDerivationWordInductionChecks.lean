/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordInduction


/-! # External induction on the successful uniform derivations -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example (H : (Total.underlying (P := P)).obj F → Prop)
    (step : ∀ (i : Fin (N+1))
      (r : (Total.underlying (P := P)).obj (R.ruleObject (Derivation.wordAlgebra R).a i)),
      (∀ k : Fin i.val,H ((Total.underlying (P := P)).map (Derivation.WordInduction.typedPremise R i k) r)) →
        H ((Total.underlying (P := P)).map (R.ruleConclusion (Derivation.wordAlgebra R).a i) r)) :
    ∀ d : (Total.underlying (P := P)).obj (Derivation.wordAlgebra R).a.left,
      H ((Total.underlying (P := P)).map (Derivation.wordConclusion R) d) :=
  Derivation.WordInduction.conclusion_induction R H step

example (d : (Total.underlying (P := P)).obj (Derivation.wordAlgebra R).a.left) :
    ∃ (i : Fin (N+1))
      (r : (Total.underlying (P := P)).obj (R.ruleObject (Derivation.wordAlgebra R).a i)),
      (Total.underlying (P := P)).map (Derivation.WordInduction.constructor R i) r=d :=
  Derivation.WordInduction.constructor_cases R d
example (H : (Total.underlying (P := P)).obj (Derivation.wordAlgebra R).a.left → Prop)
    (step : ∀ (i : Fin (N+1))
      (r : (Total.underlying (P := P)).obj (R.ruleObject (Derivation.wordAlgebra R).a i)),
      (∀ k : Fin i.val,H ((Total.underlying (P := P)).map (Derivation.WordInduction.typedChild R i k) r)) →
        H ((Total.underlying (P := P)).map (Derivation.WordInduction.constructor R i) r)) :
    ∀ d : (Total.underlying (P := P)).obj (Derivation.wordAlgebra R).a.left,H d :=
  Derivation.WordInduction.word_rule_induction R H step
