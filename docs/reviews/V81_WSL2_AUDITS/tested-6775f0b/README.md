# Manuscript v81 at the Cockett–Hofstra proof commit

The two readers independently reconstructed the manuscript from its 25 TeX files and sealed their findings before comparing their accounts. Both found that the 77 numbered results have Lean proofs at the indicated types. The active correspondence also includes three numbered definitions. The six open historical claims occur in §1. [Tested commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/6775f0b3a5fb668f9390b21440f3f6c57bc65930) · [Manuscript correspondence](../../../../FORMALIZATION_STATUS_V81.md) · [Verification report](../../../V81_WSL2_LEAN_VERIFICATION.md)

| Evidence | Contents |
|---|---|
| [First manuscript reading](first/report.md) and [second manuscript reading](second/report.md) | Hypotheses, quantifiers, source locations, dependencies and independent statement checks in reading order. |
| [First reconciliation](first/reconciliation/reconciliation.md) and [second reconciliation](second/reconciliation/README.md) | All 80 numbered rows, including their 852 distinct explicitly named declarations. Each reader records the additional results inspected through module references. |
| [Cockett–Hofstra source comparison](cockett-hofstra/README.md) | Both directions of Theorem 4.9, including total parameters, the empty input and output powers, the idempotent splitting and preservation of restriction. The archived proof export can be checked in an empty Lean kernel environment. |
| [Targeted verification receipt](targeted.json.gz) | Build and strict elaboration on the pinned checkout, the full current transitive axiom audit, parser tests and manuscript verification. |

The two reports identify the same six missing historical proofs and the same invalid inference in the unrestricted Di Paola–Heller attribution. Counting that inference a second time under proof gaps accounts for the difference between six and seven in the signed reports. Both also identify the ambiguity in the opening of §8.3 and the citation of page 594 where item (3) appears on page 595.
