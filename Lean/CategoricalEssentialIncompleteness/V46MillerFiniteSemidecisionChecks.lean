import CategoricalEssentialIncompleteness.V46MillerFiniteSemidecision

namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteSemidecision.Checks

open Encodable
open Nat.Partrec (Code)

example {α : Type*} [Primcodable α] (c : Code) :
    PrimrecRel (fun x : α => fun fuel : ℕ =>
      (c.evaln fuel (encode x)).isSome = true) :=
  haltsWithin_primrec c

example {α : Type*} [Primcodable α] (c : Code) (L : List α) :
    (∀ x ∈ L,(c.eval (encode x)).Dom) ↔
      ∃ fuel,∀ x ∈ L,(c.evaln fuel (encode x)).isSome = true :=
  list_uniform_fuel c L

example {α : Type*} [Primcodable α] {P : α → Prop} (hP : REPred P) :
    REPred (fun L : List α => ∀ x ∈ L,P x) :=
  listAll_re hP

example {α : Type*} [Primcodable α] {R : α × ℕ → Prop} (hR : REPred R)
    (hU : ∀ a x y,R (a,x) → R (a,y) → x = y) :
    ∃ F : α → Part ℕ,Partrec F ∧ ∀ a m,m ∈ F a ↔ R (a,m) :=
  functional_graph hR hU

/-- No inhabitant of the input type is needed, including for the empty list. -/
example (P : Empty → Prop) (hP : REPred P) :
    REPred (fun L : List Empty => ∀ x ∈ L,P x) :=
  listAll_re hP

end CategoricalEssentialIncompleteness.V46.Miller.FiniteSemidecision.Checks
