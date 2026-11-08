import CategoricalEssentialIncompleteness.V46MillerDerivationTotal
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable (z : Point) {F : Total.CanonicalTotal z} {N : ℕ} (R : RulePresentation F N)
example : IsInitial (Derivation.Canonical.derivationAlgebra z R) :=
  Derivation.Canonical.derivationInitial z R
example (Q : Over F) (i : Fin (N+1)) : R.ruleObject Q i=
    pullback (R.premises i) (finitePowerMap Q.hom i.val) := rfl
example (i : Fin (N+1)) : DecidableVariables (finitePower F i.val) :=
  Derivation.Canonical.ruleEquality z R i
example : (Derivation.Canonical.interpretation z).ReflectsIsomorphisms := inferInstance
example : IsPullback (Derivation.Canonical.treeInclusion z R) (Derivation.Canonical.conclusion z R)
    (Derivation.Canonical.validatorFold z R).f (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  Derivation.Canonical.successful_pullback z R
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.Canonical.derivationFold z R B).f.left ≫ B.a.hom=Derivation.Canonical.conclusion z R :=
  Derivation.Canonical.fold_conclusion z R B
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.Canonical.derivationAlgebra z R).str ≫ (Derivation.Canonical.derivationFold z R B).f=
      R.inference.map (Derivation.Canonical.derivationFold z R B).f ≫ B.str :=
  Derivation.Canonical.fold_constructor z R B
example (B : Endofunctor.Algebra R.inference) (f : Derivation.Canonical.derivationAlgebra z R ⟶ B) :
    f=Derivation.Canonical.derivationFold z R B := Derivation.Canonical.fold_unique z R B f
example (B : Endofunctor.Algebra R.inference)
    (f : (Derivation.Canonical.derivationAlgebra z R).a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom=Derivation.Canonical.conclusion z R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str=
      (Derivation.Canonical.derivationAlgebra z R).str ≫ Over.homMk f hf) :
    f=(Derivation.Canonical.derivationFold z R B).f.left :=
  Derivation.Canonical.fold_underlying_unique z R B f hf hc
example : (Derivation.Canonical.derivationAlgebra z R).str.left ≫ Derivation.Canonical.treeInclusion z R=
    InputGeometry.forget R (Derivation.Canonical.derivationAlgebra z R).a ≫
      (PolynomialComparison.ordinary R).map (Derivation.Canonical.treeInclusion z R) ≫
        (Derivation.Canonical.ordinaryTree z R).str := Derivation.Canonical.constructor_tree z R
example (i : Fin (N+1)) : Derivation.Canonical.constructor z R i ≫ Derivation.Canonical.conclusion z R=
    R.ruleConclusion (Derivation.Canonical.derivationAlgebra z R).a i :=
  Derivation.Canonical.constructor_conclusion z R i
example : Derivation.Canonical.nullary z R ≫ Derivation.Canonical.conclusion z R=R.conclusion 0 :=
  Derivation.Canonical.nullary_conclusion z R
