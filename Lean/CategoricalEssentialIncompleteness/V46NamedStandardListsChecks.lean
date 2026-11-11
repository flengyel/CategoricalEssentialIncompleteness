/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedStandardLists


/-! # Statement checks in `V46NamedStandardListsChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.NamedStandardListsChecks
open NamedPostfixEncoding SyntacticSyntax SyntacticSyntax.NatVectors
example (xs ys : List ℕ) : Words.append (pack xs) (pack ys) = pack (xs ++ ys) := append_pack xs ys
example (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.member x (pack xs) = 1 ↔ x ∈ xs := member_pack_eq_one x xs
example (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.delete x (pack xs) = pack (xs.filter (fun y => decide (y ≠ x))) :=
  delete_pack x xs
example (xs : List ℕ) : pack xs = 0 ↔ xs = [] := pack_eq_zero xs
end CategoricalEssentialIncompleteness.V46.NamedStandardListsChecks
