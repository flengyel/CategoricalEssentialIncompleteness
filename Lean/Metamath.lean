/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Metamath.Feferman.MPSequence
public import Metamath.Feferman.ProofCode

/-!
# Metamath

The root reserved for the metamathematical formalization, in the sense of
Feferman 1960. It holds two modules. `Metamath.Feferman.MPSequence` develops
MP-only proof sequences at the level of finite token strings and lists.
`Metamath.Feferman.ProofCode` defines explicit natural-number codes for those
strings and sequences, the numerical implication and modus-ponens operations,
and the numerical proof predicate `Proof_T`.

Explicit natural-number coding exists. Every candidate formula string and
proof sequence has a natural-number code under its respective encoder.
`decodeFormula` and `decodeProof` are total inverse decoders.
`Proof_T Th p a` is a predicate on proof-sequence code `p` and formula
code `a`. `proof_T_mp` is the external numerical modus-ponens theorem, proved
in Lean.

Primitive recursiveness of the existing `Proof_T` is now proved:
For every `Th : PRTheoryPresentation`, `primrecRel_proof_T Th` proves
`PrimrecRel (Proof_T Th.toTheory)`. It certifies the predicate already defined here; no
weaker predicate was substituted.

That result is external Lean certification. Numerical coding is not arithmetic
representation, and a `PrimrecRel` theorem is not an arithmetic one. This root
defines no arithmetic formula, defines no arithmetic syntax, proves no
PA-internal theorem, and imports no Foundation module.

Arithmetic representation is defined in the separate `Arith` root, the only
root that imports Foundation. `Arith.Feferman.ProofFormula` defines the
arithmetic formula `proofTFormula` for the `Proof_T` of this root and proves
two results about it: standard-natural-number adequacy
(`proofTFormula_nat_iff`), completed in B0b-1, and numeralwise weak
representation (`proofTFormula_weak_representation`), completed in B0b-2.

Numeralwise weak representation fixes a proof code and a formula code as
numerals. It is not a single object-language theorem with free proof and
formula variables. The separate structural representation in
`Arith.Feferman.StructuralProof` proves PA-uniform `mp` closure, and
`Arith.Feferman.Specialization` proves PA-uniform preservation for its
specialization and forward/reverse proof-transfer maps. These results do not
identify the selected `proofTFormula` with the structural graph in nonstandard
models, and Appendix B remains incomplete.

The project has four roots: `PCats`, `RiceShapiro`, `Metamath`, and `Arith`.
`Metamath` imports none of the other three, and neither `PCats` nor
`RiceShapiro` imports `Metamath`; `scripts/syncpcats.sh` runs a source-layer
check for that.

`scripts/syncpcats.sh` checks this root against
`{propext, Classical.choice, Quot.sound}`. That is the envelope it also
enforces on `Arith`, and it is wider than the `{propext, Quot.sound}` it
enforces on `PCats` and `RiceShapiro`.

Among the 117 audited public declarations, exactly 27 list `Classical.choice`:
the nine `PRTheoryPresentation`-family declarations, the four `MPSequence`
`primrec_*` theorems, the thirteen `ProofCode` `primrec_*` theorems, and
`primrecRel_proof_T`. All belong to the primitive-recursiveness certification
layer. They depend on pinned-Mathlib `Primrec` declarations that themselves
list `Classical.choice`. Private declarations are excluded from the
117-declaration audit.

Among the audited public declarations, `#print axioms` lists `Classical.choice`
for no other: not for `proofList_mp`, not for the structural codec, not for
`Proof_T`, and not for `Metamath.Feferman.proof_T_mp`. The direct probes in
`check_metamath_axioms.lean` record the exact axiom dependencies of the
pinned-Mathlib declarations the certificates are built from; some list
`Classical.choice` and some do not.
-/

@[expose] public section
