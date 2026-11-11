/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDyadicEffective


/-! # Statement checks in `V46MillerDyadicEffectiveChecks` -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Checks
example : Primrec (fun t : (List (Fin 2) × ℕ) × ℕ => wordNumeral t.1.1 t.1.2 t.2) := wordNumeral_primrec
example : PrimrecPred (fun t : (List (Fin 2) × ℕ) × ℕ => ∀ j < t.2, Nat.pair t.1.2 j < t.1.1.length) := located_primrec
example : PrimrecPred (fun t : (List (Fin 2) × List (Fin 2)) × (ℕ × ℕ) => ApartAt t.1.1 t.1.2 t.2.1 t.2.2) := apartAt_primrec
example : REPred (fun t : List (Fin 2) × List (Fin 2) => ∃ n k, ApartAt t.1 t.2 n k) := apart_re
example : Primrec normalizeWord := normalizeWord_primrec
example (p : ℕ → Fin 2) (k : ℕ) : normalizeWord ((bitPrefix p k).map Fin.val) = bitPrefix p k := normalizeWord_numericalPrefix p k
end CategoricalEssentialIncompleteness.V46.Miller.Checks
