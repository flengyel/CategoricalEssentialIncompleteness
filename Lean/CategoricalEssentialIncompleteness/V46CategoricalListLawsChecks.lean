import CategoricalEssentialIncompleteness.V46CategoricalListLaws

/-! Statement checks for parameter recursion and membership of concatenation. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (L : StableListAlgebra V) (E : DecidableVariables V)

example (x : X ⟶ V) (w w' : X ⟶ L.algebra.carrier) :
    prod.lift x (prod.lift w w' ≫ L.append) ≫ L.membership E =
      Two.binary Bool.or (prod.lift x w ≫ L.membership E)
        (prod.lift x w' ≫ L.membership E) :=
  L.membership_append E x w w'

example (x y : X ⟶ V) :
    prod.lift x y ≫ E.test = Two.constant X true ↔ x = y := E.test_true_iff x y

example {P Y : D} (n : P ⟶ Y) (c : P ⨯ (V ⨯ Y) ⟶ Y)
    (f : P ⨯ L.algebra.carrier ⟶ Y)
    (hn : L.parameterNil P ≫ f = n)
    (hc : L.parameterCons P ≫ f = L.parameterRec f ≫ c) :
    f = L.parameterFold n c := L.parameterFold_unique n c f hn hc
