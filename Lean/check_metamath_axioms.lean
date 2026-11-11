module

public import Metamath

/-!
# Axiom check for `Metamath`

Run with:

`lake env lean check_metamath_axioms.lean`

`scripts/syncpcats.sh` fails the run when this file's output names an axiom
outside `{propext, Classical.choice, Quot.sound}`, or names `sorryAx`. That
envelope is wider than the `{propext, Quot.sound}` enforced on `PCats` and on
`RiceShapiro`; those two checks are separate files over separate roots and are
unchanged.

## Coverage

Every public declaration of both modules of this root is audited below:

* `Metamath.Feferman.MPSequence` — 51 declarations
* `Metamath.Feferman.ProofCode`  — 66 declarations
* total — 117 declarations

A declaration counts as public when its defining module is the file in
question and it is neither internal nor blacklisted by Lean's own criterion,
which excludes recursors and other eliminator machinery. Both lists were
enumerated from the environment rather than written by hand, so a new public
declaration that is not audited here is a discrepancy between these counts and
the modules.

`MPSequence.lean` has five private declarations and `ProofCode.lean` has 12:
`codeUnpair_codePair_aux`, `getD_map_range`, `spreadStep`,
`primrec_spreadStep`, `spreadStep_history`, `unpairStep`,
`primrec_unpairStep`, `unpairStep_history`, `listEncode_eq_foldr`,
`decodeStep`, `primrec_decodeStep`, `decodeStep_history`. Private
declarations are not public and are not listed.

## Where `Classical.choice` appears

Among the 117 audited public declarations, exactly 27 list `Classical.choice`:
the nine `PRTheoryPresentation`-family declarations, the four `MPSequence`
`primrec_*` theorems, the thirteen `ProofCode` `primrec_*` theorems, and
`primrecRel_proof_T`. All belong to the primitive-recursiveness certification
layer, and they depend on pinned-Mathlib `Primrec` declarations that themselves
list `Classical.choice`; the probes at the end of this file record those
dependencies, some of which list it and some of which do not.

It appears nowhere in the computational content. `#print axioms` does not list
`Classical.choice` for `bitSpread`, `codePair`, `codeUnpair`,
`codePair_codeUnpair`, `codeUnpair_codePair`, `codeUnpair_right_le`,
`listEncode`, `listDecode`, either list inverse law, `decodeFormula`,
`decodeProof`, `imp`, `lhs`, `rhs`, `mp`, `Proof_T`, `proof_T_mp`, or
`proofList_mp`.

`#print axioms` reports the axioms of a declaration's type together with those
of its proof term and does not distinguish the two, so nothing here should be
read as a claim about which of the two introduces a given axiom.
-/

@[expose] public section

open Metamath.Feferman

/-! ## MPSequence declarations (51) -/

#print axioms FormulaString
#print axioms IsProofList
#print axioms LineJustified
#print axioms PRTheoryPresentation
#print axioms PRTheoryPresentation.ax_prim
#print axioms PRTheoryPresentation.ctorIdx
#print axioms PRTheoryPresentation.formula_prim
#print axioms PRTheoryPresentation.logicalAxiom_prim
#print axioms PRTheoryPresentation.mk
#print axioms PRTheoryPresentation.mk.injEq
#print axioms PRTheoryPresentation.mk.sizeOf_spec
#print axioms PRTheoryPresentation.toTheory
#print axioms ProofSequence
#print axioms StringPredicate
#print axioms StringPredicate.Holds
#print axioms StringPredicate.ctorIdx
#print axioms StringPredicate.decidableHolds
#print axioms StringPredicate.mk
#print axioms StringPredicate.mk.injEq
#print axioms StringPredicate.mk.sizeOf_spec
#print axioms StringPredicate.test
#print axioms SyntaxPresentation
#print axioms SyntaxPresentation.ctorIdx
#print axioms SyntaxPresentation.formula
#print axioms SyntaxPresentation.formula_imp_iff
#print axioms SyntaxPresentation.logicalAxiom
#print axioms SyntaxPresentation.logicalAxiom_formula
#print axioms SyntaxPresentation.mk
#print axioms SyntaxPresentation.mk.injEq
#print axioms SyntaxPresentation.mk.sizeOf_spec
#print axioms TheoryPresentation
#print axioms TheoryPresentation.ax
#print axioms TheoryPresentation.ax_formula
#print axioms TheoryPresentation.ctorIdx
#print axioms TheoryPresentation.mk
#print axioms TheoryPresentation.mk.injEq
#print axioms TheoryPresentation.mk.sizeOf_spec
#print axioms TheoryPresentation.syn
#print axioms Token
#print axioms impString
#print axioms impTag
#print axioms lhsString
#print axioms lhsString_impString
#print axioms mpList
#print axioms primrec_impString
#print axioms primrec_lhsString
#print axioms primrec_mpList
#print axioms primrec_rhsString
#print axioms proofList_mp
#print axioms rhsString
#print axioms rhsString_impString

/-! ## ProofCode declarations (66) -/

#print axioms FormulaCode
#print axioms ProofSequenceCode
#print axioms Proof_T
#print axioms bitSpread
#print axioms bitSpread.eq_def
#print axioms bitSpread_eq
#print axioms bitSpread_zero
#print axioms codePair
#print axioms codePair_codeUnpair
#print axioms codePair_eq
#print axioms codePair_zero_zero
#print axioms codeUnpair
#print axioms codeUnpair.eq_def
#print axioms codeUnpair_codePair
#print axioms codeUnpair_fst
#print axioms codeUnpair_left_le
#print axioms codeUnpair_right_le
#print axioms codeUnpair_snd
#print axioms codeUnpair_zero
#print axioms decodeFormula
#print axioms decodeFormula_encodeFormula
#print axioms decodeFormula_imp
#print axioms decodeProof
#print axioms decodeProof_encodeProof
#print axioms decodeProof_mp
#print axioms encodeFormula
#print axioms encodeFormula_decodeFormula
#print axioms encodeFormula_injective
#print axioms encodeProof
#print axioms encodeProof_decodeProof
#print axioms encodeProof_injective
#print axioms encodeProof_nil_ne_encodeProof_nil_nil
#print axioms imp
#print axioms imp_inj
#print axioms le_bitSpread
#print axioms lhs
#print axioms lhs_imp
#print axioms listDecode
#print axioms listDecode.eq_def
#print axioms listDecode_injective
#print axioms listDecode_listEncode
#print axioms listDecode_succ
#print axioms listDecode_zero
#print axioms listEncode
#print axioms listEncode_cons
#print axioms listEncode_injective
#print axioms listEncode_listDecode
#print axioms listEncode_nil
#print axioms mp
#print axioms primrec_bitSpread
#print axioms primrec_codePair
#print axioms primrec_codeUnpair
#print axioms primrec_decodeFormula
#print axioms primrec_decodeProof
#print axioms primrec_encodeFormula
#print axioms primrec_encodeProof
#print axioms primrec_imp
#print axioms primrec_lhs
#print axioms primrec_listDecode
#print axioms primrec_listEncode
#print axioms primrec_mp
#print axioms primrec_rhs
#print axioms proof_T_mp
#print axioms rhs
#print axioms rhs_imp
#print axioms primrecRel_proof_T

/-! ## External probes

Pinned-Mathlib declarations that the results above are built from. These are
Mathlib declarations, not project declarations, and are counted in neither
module total. They are listed so that the attribution of `Classical.choice`
rests on output rather than assertion. Some list it and some do not.

The arithmetic supporting the codec is in the second group; none of it lists
`Classical.choice`.
-/

#print axioms Nat.Primrec
#print axioms Primrec
#print axioms Primrec₂
#print axioms Primcodable
#print axioms Primcodable.bool
#print axioms Primcodable.list
#print axioms Primcodable.prod
#print axioms Primrec.id
#print axioms Primrec.fst
#print axioms Primrec.const
#print axioms Primrec.comp
#print axioms Primrec.option_getD
#print axioms Primrec.list_cons
#print axioms Primrec.list_length
#print axioms Primrec.list_append
#print axioms Primrec.list_concat
#print axioms Primrec.list_reverse
#print axioms Primrec.list_head?
#print axioms Primrec.list_getD
#print axioms Primrec.list_take
#print axioms Primrec.list_drop
#print axioms Primrec.list_foldr
#print axioms Primrec.list_map
#print axioms Primrec.nat_casesOn
#print axioms Primrec.nat_strong_rec
#print axioms Primrec.nat_div
#print axioms Primrec.nat_mod
#print axioms Primrec.nat_add
#print axioms Primrec.nat_mul

-- Arithmetic supporting the bit-interleaving codec.
#print axioms Nat.div
#print axioms Nat.mod
#print axioms Nat.div_lt_self
#print axioms Nat.mod_add_div
#print axioms Nat.div_div_eq_div_mul
#print axioms Nat.div_le_self
#print axioms Nat.strong_induction_on
