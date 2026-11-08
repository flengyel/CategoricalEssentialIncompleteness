import CategoricalEssentialIncompleteness.V46ForkDerivationEvaluation
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Evaluation
variable {K L : EffectiveFork.Total ⥤ NumericalTuples.Object}
variable [PreservesFiniteLimits K] [PreservesFiniteCoproducts K]
variable [PreservesFiniteLimits L] [PreservesFiniteCoproducts L]
variable {F : EffectiveFork.Total} {N : ℕ} (R : RulePresentation F N)

example (X : EffectiveFork.Total) (n : ℕ) :
    K.obj (finitePower X n) ≅ finitePower (K.obj X) n := finitePowerIso X n
example : (interpretedRules (K := K) R).instances = fun i => K.obj (R.instances i) := rfl
example (i : Fin (N+1)) : (interpretedRules (K := K) R).premises i =
    K.map (R.premises i) ≫ (finitePowerIso (K := K) F i.val).hom := rfl
example (i : Fin (N+1)) : (interpretedRules (K := K) R).conclusion i =
    K.map (R.conclusion i) := rfl
example (Q : Over F) (i : Fin (N+1)) :
    (inputIso (K := K) R Q i).hom ≫ pullback.fst _ _ =
      K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) := inputIso_fst R Q i
example (Q : Over F) (i : Fin (N+1)) :
    (inputIso (K := K) R Q i).hom ≫ pullback.snd _ _ =
      K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso (K := K) Q.left i.val).hom := inputIso_snd R Q i
example : R.inference ⋙ Over.post K ≅
    Over.post K ⋙ (interpretedRules (K := K) R).inference := comparison R
example (A : Endofunctor.Algebra R.inference) :
    (mappedAlgebra (K := K) R A).a.hom = K.map A.a.hom := rfl
example (α : K ⟶ L) (X : EffectiveFork.Total) (n : ℕ) :
    α.app (finitePower X n) ≫ (finitePowerIso (K := L) X n).hom =
      (finitePowerIso (K := K) X n).hom ≫ finitePowerMap (α.app X) n :=
  finitePowerIso_transformation α X n
example (α : K ⟶ L) {I : Type} [Finite I] (X : I → EffectiveFork.Total) :
    α.app (∐ X) ≫ inv (sigmaComparison L X) =
      inv (sigmaComparison K X) ≫ Limits.Sigma.map (fun i => α.app (X i)) :=
  sigmaComparison_transformation α X
end CategoricalEssentialIncompleteness.V46.ForkDerivation.Evaluation
