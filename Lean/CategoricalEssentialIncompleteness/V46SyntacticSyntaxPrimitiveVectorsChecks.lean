/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveVectors


/-! # Statement checks in `V46SyntacticSyntaxPrimitiveVectorsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.PrimitiveVectorsChecks
example (a : ℕ) : pack (Nat.natToList a) = a := pack_natToList a
example (l : List ℕ) : Nat.natToList (pack l) = l := natToList_pack l

example : Nat.Primrec (Nat.unpaired (Words.append : ℕ → ℕ → ℕ)) :=
  Primrec₂.unpaired'.mpr append_primrec

example : Primrec (len : ℕ → ℕ) := len_primrec
example : Primrec₂ (nth : ℕ → ℕ → ℕ) := nth_primrec
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.PrimitiveVectorsChecks
