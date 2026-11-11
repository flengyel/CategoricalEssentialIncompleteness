# Lean continuation requested for manuscript v57

The requested target is manuscript v57, whose mathematical statements and
proofs are reported by the author to agree with v56. The source archive and
the accompanying instructions for its fifteen additional results were not
available in the checkout or Downloads when this continuation began.
After fetching, `origin/main` was
`de1466ac2fd820ed06931c467083a79f0481f84c`, whose manifest selects v51.
No v57 statement comparison or verification is claimed here.

The checkout was fast-forwarded from `c5d7d0e` to that available main commit.
Before integration, the available v51 source archive was extracted to a
temporary directory and compared with the checkout. SHA-256 checks confirmed
that all 2,195 modified or untracked inputs present before integration were
preserved byte-for-byte. The comparison and preservation records are under
`.codex-work/v57-continuation-20261110/`. This comparison concerns the
available v51 archive, not the missing v57 archive.

## Verifier repair

The four declaration-name capture sites in `scripts/verify.py` have been
replaced by the shared `parse_axiom_reports` function. Both retained and
current audits now capture through the closing quote preceding the report
suffix, preserving terminal and interior apostrophes. An independent check
of the raw report lines rejects skipped, truncated or repeated names.
Unexpected axioms are still rejected against the unchanged permitted set:
`propext`, `Quot.sound`, `Classical.choice`.

`python3 scripts/test_verify_axiom_parser.py` passes five regression tests.
They exercise ordinary names, terminal primes, interior primes, axiom-free
declarations, distinct declarations that would previously collide, rejected
axioms, malformed reports and duplicate reports. The established full
verifier runs these tests and measures their source with its other inputs.

The preserved raw evidence from
`.codex-work/verify-20261109T102738Z-KM4dao/build-logs/` was reparsed without
running Lean or modifying the evidence:

| Raw log | Complete declaration names | Names containing apostrophes | Axiom union |
| --- | ---: | ---: | --- |
| `axiom-audit.log` | 1,274 | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| `current-axiom-audit.log` | 25,781 | 31 | `Classical.choice`, `Quot.sound`, `propext` |

The previous parser recorded 25,752 current names. It lost 31 complete names
and introduced the two truncated names `.eq_1` and `_1`. Reports for names
common to both parses agree. Complete name-to-axiom maps and raw-log hashes
are retained in `axiom-parser-raw-evidence-reparse.json` in the continuation
working directory. These corrected counts describe a reparse of the v48
raw evidence for proof commit `d437827275d64f6500e6a3bca2ee318420d11edd`;
they do not constitute a new Lean verification or a verification of v57.

## Build state and remaining results

The Lean toolchain and dependency manifest are unchanged. All sixteen
dependency worktrees are clean and match their pins. The unfinished
module-system port is preserved. Its development build runs through the
existing lock with `LEAN_NUM_THREADS=1`; module visibility repairs retain
the mathematical definitions, statements and proofs.

The available v51 manuscript-only gate passes. Full verification against
v57 remains pending receipt and integration of that source and completion
of the proof batch. The fifteen requested results remain open: 4.4–4.8,
5.1–5.3, 8.9–8.10, 9.6, 9.8 and 10.7–10.9. No correspondence row has been
marked complete on the basis of the parser repair or a manuscript-only gate.
