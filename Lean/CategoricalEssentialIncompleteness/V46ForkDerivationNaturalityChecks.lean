/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationNaturality


/-! # Folds and naturality on the valid fork proof carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Naturality.Checks

example {X Y : EnumerableCarriers.Total} (f : X ⟶ Y)
    (x : {n // n ∈ X.obj.support}) : (unaryMap f).toFun x = EnumerableCarriers.totalFunction f x := rfl

example : unaryFunctor ⋙ NumericalTuples.comparison ≅ 𝟭 EnumerableCarriers.Total := unaryComparison
example : unaryFunctor.IsEquivalence := inferInstance
example : PreservesLimits unaryFunctor := inferInstance
example : PreservesColimits unaryFunctor := inferInstance

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) (e : P ≅ NumericalDerivation.codeAlgebra R) :
    IsInitial P := comparedInitial R P e

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) (e : P ≅ NumericalDerivation.codeAlgebra R)
    (B : Endofunctor.Algebra R.inference) :
    comparedFold R P e B ≫ B.a.hom = P.a.hom := comparedFold_conclusion R P e B

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) (e : P ≅ NumericalDerivation.codeAlgebra R)
    (B : Endofunctor.Algebra R.inference) :
    P.str.left ≫ comparedFold R P e B =
      (R.inference.map (comparedFoldHom R P e B).f).left ≫ B.str.left :=
  comparedFold_constructor R P e B

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) (e : P ≅ NumericalDerivation.codeAlgebra R)
    (B : Endofunctor.Algebra R.inference) (f : P.a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom = P.a.hom)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str = P.str ≫ Over.homMk f hf) :
    f = comparedFold R P e B := comparedFold_unique R P e B f hf hc

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) (e : P ≅ NumericalDerivation.codeAlgebra R)
    {B C : Endofunctor.Algebra R.inference} (h : B ⟶ C) :
    comparedFold R P e B ≫ h.f.left = comparedFold R P e C :=
  comparedFold_postcompose R P e h

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    {B C : Endofunctor.Algebra R.inference} (m : B ⟶ C) (i : Fin (N + 1)) :
    branch R B i ≫ m.f.left = R.ruleMap m.f i ≫ branch R C i := branch_natural R m i

open ForkSyntax SelectedTrees
example {A B A' B' : Set ℕ} {O : Operations A B} {O' : Operations A' B'}
    (E : Evaluation O) (E' : Evaluation O') (f : ℕ → ℕ)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (h : NaturalOperations O O' f ha hb) {t p} (ht : Concludes A B t p) :
    h.map p (E.value ht) = E'.value (ht.mapAtoms f ha hb) := evaluation_natural E E' f ha hb h ht

example {A B : Set ℕ} {O : Operations A B} (E E' : Evaluation O)
    {t p} (ht : Concludes A B t p) : E.value ht = E'.value ht := evaluation_unique E E' ht

example (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    fold A B hA hB D ≫ D.a.hom = Component.conclusion A B hA hB := fold_conclusion A B hA hB D

example (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    (Component.algebra A B hA hB).str.left ≫ fold A B hA hB D =
      ((Component.rules A B hA hB).inference.map (foldHom A B hA hB D).f).left ≫ D.str.left :=
  fold_constructor A B hA hB D

example (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (u : Component.proofObject A B hA hB ⟶ D.a.left)
    (hu : u ≫ D.a.hom = Component.conclusion A B hA hB)
    (hc : (Component.rules A B hA hB).inference.map (Over.homMk u hu) ≫ D.str =
      (Component.algebra A B hA hB).str ≫ Over.homMk u hu) : u = fold A B hA hB D :=
  fold_unique A B hA hB D u hu hc

example (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    SelectedTrees.Evaluation (targetOperations A B hA hB D) := foldEvaluation A B hA hB D

example {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (D' : Endofunctor.Algebra (Component.rules A' B' hA' hB').inference)
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (h : D.a.left ⟶ D'.a.left)
    (hc : h ≫ D'.a.hom = D.a.hom ≫ formulaMap f hf)
    (hn : AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc) :
    fold A B hA hB D ≫ h = proofMap hA hB hA' hB' f hf ha hb ≫ fold A' B' hA' hB' D' :=
  fold_natural hA hB hA' hB' D D' f hf ha hb h hc hn

example {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B') :
    proofMap hA hB hA' hB' f hf ha hb ≫ Component.conclusion A' B' hA' hB' =
      Component.conclusion A B hA hB ≫ formulaMap f hf :=
  proofMap_conclusion hA hB hA' hB' f hf ha hb

example {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B') :
    AlgebraNaturality hA hB hA' hB' (Component.algebra A B hA hB)
      (Component.algebra A' B' hA' hB') f hf ha hb
      (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) :=
  native_algebra_naturality hA hB hA' hB' f hf ha hb

example {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (n : Component.Node A B (Component.algebra A B hA hB).a) :
    (proofMap hA hB hA' hB' f hf ha hb).toFun
      ((Component.algebra A B hA hB).str.left.toFun
        (Component.nodeInput A B hA hB (Component.algebra A B hA hB).a n)) =
      (Component.algebra A' B' hA' hB').str.left.toFun
        (Component.nodeInput A' B' hA' hB' (Component.algebra A' B' hA' hB').a
          (relabelNode hA hB hA' hB' (Component.algebra A B hA hB)
            (Component.algebra A' B' hA' hB') f hf ha hb
            (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) n)) :=
  native_node_naturality hA hB hA' hB' f hf ha hb n

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Naturality.Checks
