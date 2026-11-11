/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Arith.Feferman.ProofFormula
public import Arith.Feferman.StructuralProof
public import Arith.FixedFormulaNumeralSubstitution
public import Arith.Feferman.Specialization

/-!
# Arith

The root holding arithmetic representation of the Feferman proof predicate.
It is the only root that imports Foundation.

`Arith.Feferman.ProofFormula` provides the selected Sigma-one representation.
`Arith.Feferman.StructuralProof` gives an all-model structural representation
of the same numerical proof predicate, and `Arith.Feferman.Specialization`
uses that representation for PA-uniform numeral specialization and graph-proof
transfer. The fixed-formula numeral-substitution module proves primitive
recursiveness of the actual sentence substitutions used by the
proof-presentation bridge.

`PCats`, `RiceShapiro` and `Metamath` do not import this root or Foundation.
`Metamath` remains buildable in a Lake configuration with no Foundation
requirement. `scripts/syncpcats.sh` checks the source-layer separation.
-/

@[expose] public section
