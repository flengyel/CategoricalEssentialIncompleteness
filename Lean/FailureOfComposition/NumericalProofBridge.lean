/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.RETheory

/-!
# Proof-presentation bridges for numerical specialization

This umbrella imports the actual graph-sentence code builders, the sound
extended presentation, its exact structural proof graph, the primitive-
recursive stage-to-tag maps, the composed forward/reverse transfer maps, and
their instantiation for every r.e.-axiomatized extension of PA.
-/

@[expose] public section
