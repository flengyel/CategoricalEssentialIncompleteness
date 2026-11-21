/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordFirstOrderInduction


/-! # First-order conclusion induction with arbitrary uniform axioms -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {V F L Sent A : Total.TotalCategory P}
variable (logical : L ⟶ F) (sentence : Sent ⟶ F) (axioms : A ⟶ Sent)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
example (H : (Total.underlying (P := P)).obj F → Prop)
    (hl : ∀ l,H ((Total.underlying (P := P)).map logical l))
    (ha : ∀ a,H ((Total.underlying (P := P)).map (axioms ≫ sentence) a))
    (hg : ∀ z,H ((Total.underlying (P := P)).map (prod.snd : V ⨯ F ⟶ F) z) → H ((Total.underlying (P := P)).map all z))
    (hm : ∀ z,H ((Total.underlying (P := P)).map (prod.fst : F ⨯ F ⟶ F) z) →
      H ((Total.underlying (P := P)).map imp z) → H ((Total.underlying (P := P)).map (prod.snd : F ⨯ F ⟶ F) z)) :
    ∀ d : (Total.underlying (P := P)).obj
      (Derivation.wordAlgebra (firstOrderRules logical sentence axioms all imp)).a.left,
      H ((Total.underlying (P := P)).map (Derivation.wordConclusion (firstOrderRules logical sentence axioms all imp)) d) :=
  Derivation.WordInduction.firstOrder_conclusion_induction logical sentence axioms all imp H hl ha hg hm
