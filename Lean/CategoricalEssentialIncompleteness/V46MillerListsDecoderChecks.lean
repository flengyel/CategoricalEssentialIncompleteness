/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsDecoder


/-! # An ordinary partial-recursive decoder for literal list words -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller
example : Partrec Lists.CodeInverse.decode := Lists.CodeInverse.decode_partrec
example {P : Uniform.Family} (V : Total.Carrier P) (n : ℕ) :
    n ∈ Lists.CodeInverse.decode (Lists.wordOfCode V n) := Lists.CodeInverse.decode_wordOfCode V n
