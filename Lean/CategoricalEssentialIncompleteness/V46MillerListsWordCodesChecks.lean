/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsWordCodes


/-! # Translation from list codes to word codes -/

@[expose] public section
noncomputable section
open FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (V : Total.Carrier P)
example : Primrec (Lists.wordOfCode V) := Lists.wordOfCode_primrec V
example (v rest : ℕ) :
    Lists.wordOfCode V (adjoin v rest)=Lists.consWord V v (Lists.wordOfCode V rest) :=
  Lists.wordOfCode_adjoin V v rest
example (n word : ℕ) : word ∈ Total.val (Lists.wordMap V).hom n ↔
    n ∈ (Lists.carrier V).support ∧ word=Lists.wordOfCode V n := Lists.wordMap_graph V n word
