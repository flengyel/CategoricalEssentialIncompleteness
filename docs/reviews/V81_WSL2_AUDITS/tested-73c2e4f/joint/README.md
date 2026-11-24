# Reconciliation of the two independent v81 readings

Both readers examined the same 25 active TeX files, sealed their own reconstructions at `ae816e93c11712a2b1fe16f99c763a8c934f80dc`, and tested the identical manuscript against the proof revision `73c2e4fa2bc633a3af012b1c4f85a7882018f962`. I compared their separately sealed verdicts and reports after both had finished. They agree on every finding, on its downstream use and on the result of **0 of 2** qualifying clean reports. The comparison records the SHA-256 of both reports, both verdicts and both original reading seals. [First report](../first/report.md) · [Second report](../second/report.md) · [Digests, issues and all 80 matched rows](comparison.json)

| Count | Both readers | Counting convention |
|---|---:|---|
| Mathematical errors | 1 | §1 claims inseparability under hypotheses allowing the one-morphism category. Corollary 3.3 supplies the missing nonzero identity. |
| Ambiguities | 2 | §8.3 leaves the order of the extender quantifiers unclear. Appendix C uses the same letter for an oracle-program index and a partial endomorphism. |
| Lean omissions | 6 | Each missing historical conclusion counts once at its cited hypotheses. They are Bauer–Hanson 6.4, Heller 9.2, Lengyel 21 and corrected 26, and van Dijk–Gietelink Oldenziel 5.19 and 5.20. The six occur in the introduction. The numbered results have independent proofs. |
| Gaps in the mathematical text | 1 | The invalid §1 inference is the same occurrence as the mathematical error. Including the six absent kernel proofs gives seven whole-paper gaps. Each reader found zero mathematical gaps in the 77 numbered proofs. |

Both readers locate Di Paola–Heller item (3) on printed page 595 and count the locator separately. Their source ranges differ in how many surrounding lines they include for that citation and the two uses of `d`. The recorded ranges identify the same occurrences. All **80** numbered rows matched individually on TeX label, source, ledger row and directly named declarations. They comprise 18 theorems, 19 lemmas, 27 propositions, 13 corollaries and three definitions. The transitive axiom lists agreed for all 852 distinct directly named declarations. [First verdict](../first/verdict.json) · [Second verdict](../second/verdict.json) · [Numbered, unnumbered and historical correspondence](../../../../../FORMALIZATION_STATUS_V81.md)

In §8.4, both readers assume an arbitrary finite arity bound, arbitrary unary symbol families with recursive supports through that bound, and an arbitrary natural number as input word. The first reader obtained separate total Boolean deciders for the actual term and formula supports of the literal numerical algebra. The second reader obtained a single total computable function returning both bits on the corresponding unary postfix objects. A further Lean check proves by reflexivity that the first pair of supports equals the second pair for every bound and every coefficient family. All three kernel records use only the project's permitted axioms. The returned gap in the proof of Proposition 8.8 is closed. [First numerical application](../first/proof-comparison.tar.gz) · [Second numerical application](../second/proof-checks.tar.gz) · [Equality of the two carrier descriptions](NumericalSupports.lean) · [Equality check output](NumericalSupports.log)

The comparison can be reproduced from the two distributed packages.

```sh
python3 reconcile.py ../first ../second
```

The full verifier has its own receipt at the tested revision. [Whole-project kernel receipt](../../../../V81_WSL2_LEAN_VERIFICATION_73c2e4f.json.gz)
