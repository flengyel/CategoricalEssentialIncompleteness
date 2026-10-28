/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PrfEqTransportRepair.RETheory

/-!
# Additive repair for primitive-recursive equality-proof transport

This umbrella exports the separately named checker extension, its total
primitive-recursive transport constructor, soundness and compatibility
results, exact structural graph, and PA-internal preservation theorem.  It does
not change the production `PrfEq` endpoint or assert
`HasPrimitiveRecursivePrfEqTransport` for that endpoint.
-/
