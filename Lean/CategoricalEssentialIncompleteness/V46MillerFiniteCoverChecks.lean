/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFiniteCover


/-! # Statement checks in `V46MillerFiniteCoverChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteCover

example : Primrec words := words_primrec
example : Computable words := words_computable
example (n : ℕ) (s : Word) : s ∈ words n ↔ s.length = n := mem_words_iff_length n s
example : Primrec depth := depth_primrec
example : Computable depth := depth_computable
example {s : Word} {L : List Word} (hs : s ∈ L) : s.length ≤ depth L := length_le_depth hs

example (L : List Word) : covers L = decide (∀ t ∈ words (depth L),∃ s ∈ L,t.take s.length = s) := rfl
example : Primrec covers := covers_primrec
example : Computable covers := covers_computable
example (L : List Word) : covers L = true ↔ ∀ p : Bits,∃ s ∈ L,p ∈ cylinder s := covers_iff L
example (L : List Word) : Decidable (∀ p : Bits,∃ s ∈ L,p ∈ cylinder s) := coverageDecidable L

example : words 0 = [[]] := rfl
example : depth [] = 0 := rfl
example : covers [] = false := covers_nil
example : covers [[]] = true := covers_singleton_nil
example {L : List Word} (h : [] ∈ L) : covers L = true := covers_of_nil_mem h
example (p : Bits) {m n : ℕ} (h : m ≤ n) :
    (bitPrefix p n).take m = bitPrefix p m := take_prefix p h
example (s : Word) : bitPrefix (extension s) s.length = s := prefix_extension s

end CategoricalEssentialIncompleteness.V46.Miller.FiniteCover
