import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionInputs
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example (i : Fin (N+1))
    (p : (Total.underlying (P := P)).obj (R.instances i ⨯ finitePower (Derivation.ordinaryTree R).a i.val)) :
    ((Total.underlying (P := P)).map (Derivation.ordinaryInputIso R).inv
      ((Total.underlying (P := P)).map (Sigma.ι (fun j : Fin (N+1) =>
        R.instances j ⨯ finitePower (Derivation.ordinaryTree R).a j.val) i) p)).val=
      Derivation.WordInduction.ruleTag N i
        (Nat.pair (((Total.underlying (P := P)).map prod.fst p).val)
          (((Total.underlying (P := P)).map
            (Derivation.WordInduction.rawPowerIso (Derivation.ordinaryTree R).a i.val).hom
            ((Total.underlying (P := P)).map prod.snd p)).val)) :=
  Derivation.WordInduction.ordinaryInput_inverse_value R i p
