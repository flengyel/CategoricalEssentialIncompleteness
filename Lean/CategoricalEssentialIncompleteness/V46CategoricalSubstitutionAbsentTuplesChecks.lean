import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentTuples

/-! Arbitrary internal parameter families and finite argument tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P V T Z : D} (A : Over P × Over P) (L : StableListAlgebra V) (E : DecidableVariables V)
variable (name : P ⟶ V) (FV : T ⟶ L.algebra.carrier) (original result : A.1.left ⟶ T)
variable (good : ∀ {X : D} (k : X ⟶ A.1.left),
  prod.lift (k ≫ A.1.hom ≫ name) (k ≫ original ≫ FV) ≫ L.membership E =
    Two.constant X false → k ≫ result = k ≫ original)

example (n : ℕ) {X : D} (k : X ⟶ (AbsentTuples.family A n).left)
    (ha : prod.lift (k ≫ (AbsentTuples.family A n).hom ≫ name)
      (k ≫ AbsentTuples.tupleMap A (Z := L.algebra.carrier) (original ≫ FV) n ≫ L.tupleAppend n) ≫
        L.membership E = Two.constant X false) :
    k ≫ AbsentTuples.tupleMap A (Z := Z) result n =
      k ≫ AbsentTuples.tupleMap A (Z := Z) original n :=
  AbsentTuples.tuple_absence A L E name FV original result good n k ha
