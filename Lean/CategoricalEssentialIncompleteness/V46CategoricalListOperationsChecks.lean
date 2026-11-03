import CategoricalEssentialIncompleteness.V46CategoricalListOperations

/-! List operations at categorical types, with no numerical carrier. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (L : StableListAlgebra V) (E : DecidableVariables V)

example : Mono L.algebra.nil := L.nil_mono

example : V ⨯ L.algebra.carrier ⟶ Two D := L.membership E

example : V ⨯ L.algebra.carrier ⟶ L.algebra.carrier := L.deletion E

example : V ⟶ L.algebra.carrier := L.singleton

example : prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) ≫ L.membership E =
    Two.constant V false := L.membership_nil E

example : prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) ≫ L.deletion E =
    terminal.from V ≫ L.algebra.nil := L.deletion_nil E

example : (L.algebra.withParameters V).cons ≫ L.membershipFold E =
    prod.map (𝟙 (constantFamily V V)) (L.membershipFold E) ≫
      (StableListAlgebra.membershipAlgebra E).cons := L.membershipFold_cons E

example : (L.algebra.withParameters V).cons ≫ L.deletionFold E =
    prod.map (𝟙 (constantFamily V V)) (L.deletionFold E) ≫
      (L.deletionAlgebra E).cons := L.deletionFold_cons E
