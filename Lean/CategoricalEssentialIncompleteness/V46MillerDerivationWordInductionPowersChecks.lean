import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionPowers
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} (X : Total.TotalCategory P) (n : ℕ) (k : Fin n)
example (z : (Total.underlying (P := P)).obj (finitePower X n)) :
    ((Total.underlying (P := P)).map (Derivation.WordInduction.finiteChild X n k) z).val=
      Derivation.WordInduction.tupleChild n k
        ((Total.underlying (P := P)).map (Derivation.WordInduction.rawPowerIso X n).hom z).val :=
  Derivation.WordInduction.finiteChild_value X n k z
example {Y : Total.TotalCategory P} (f : X ⟶ Y) :
    finitePowerMap f n ≫ Derivation.WordInduction.finiteChild Y n k=
      Derivation.WordInduction.finiteChild X n k ≫ f :=
  Derivation.WordInduction.finiteChild_natural f n k
