# Full verification of manuscript v59 and finite-support constructions

The full locked verification workflow passed for the measured source bytes
in commit `8df18834734179186459d3c4c34d4c0cf20b6194`:
**1,798 commands**, including **1,792 strict elaborations**. The run includes
the project build, retained and current statement checks, all selected V46
producer/Checks sources, the parser's six tests, manuscript checks and both
complete transitive axiom audits.

| Check | Result |
| --- | --- |
| Current production modules | 939 |
| Current audited declarations | 28,735 |
| Retained audited declarations | 1,274 |
| Axiom union in each audit | `propext`, `Quot.sound`, `Classical.choice` |
| Measured inputs unchanged during the run and matching the proof commit | 2,436 |
| Clean pinned dependency worktrees at both ends | 16 |
| Imported-source provenance checks | 356 |
| Retained manuscript provenance checks | 4 |
| Wrapper exit status | 0 |

The active manuscript checks cover all 24 TeX files, both copies of the PDF,
the exact source archive, the manifest and the v59 correspondence table.
All 80 numbered mathematical environments (77 results and three definitions)
are unchanged from the reviewed v58. The article changes only version
metadata and the publisher line break in reference [18]. The v58 artifacts
and the concurrent v58 verification record are preserved.

The correspondence remains **70 of 77 results proved**. The four new producer
modules construct prerequisites for Lemma 8.9; they do not complete that
lemma. The seven open results are 8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9.
Theorem 5.3 remains complete. The [construction report](V59_FINITE_SUPPORT_2026-11-14.md)
identifies the remaining positive-leaf assignment, valuation, truth-invariant
and internal-consistency obligations.

The wrapper started from `a9b444ab657e2c5a5a995ccfad627ae7c5102832` with the
new sources uncommitted. Every measured input remained unchanged during the
run. After publication, all 2,436 SHA-256 values were checked against the
local files and their Git blob hashes against the complete tree of
`8df18834734179186459d3c4c34d4c0cf20b6194`. Thus the tested input bytes match
that published revision. This evidence-reporting change alters only
unmeasured documentation.

The [summary JSON](V59_FULL_VERIFICATION_2026-11-14.json) gives the tested
revision, counts and hashes. The [compressed complete record](V59_FULL_VERIFICATION_2026-11-14.json.gz)
contains all commands, exit statuses, durations, command-log hashes, axiom
reports, measured input hashes, proof-commit blob matches and dependency
metadata. Raw logs are retained locally in
`.codex-work/verify-20261114T233919Z-qwJA0i`.

- Source snapshot SHA-256: `a0e41a8be951415c83585f2987c49f755ee8806791c61b2c9ca1b3731d3ed7e8`.
- Original verification JSON SHA-256: `67989224405e75cfe7ab53f0b0813afccc263dfd2d04753c0612d409653b4a95`.
- Compressed complete-record SHA-256: `0362cc7e1adab6411706f7360c0240d72c9162dab9655652a00590db728670f0`.
