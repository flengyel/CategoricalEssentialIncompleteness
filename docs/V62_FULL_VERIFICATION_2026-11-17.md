# Full Lean verification of manuscript v62

All **77 numbered results** have full Lean counterparts at manuscript commit
`5f1485ebba91b4cef68755fef35716a9442af7a3`. The completed serial replay passed
**1,965 commands**, including **1,959 strict elaborations**. It replayed
every selected producer and statement-check source with warnings treated as
errors, built the project and ran both statement and transitive axiom audits.

| Verification | Count |
| --- | ---: |
| Current production modules | 1,068 |
| Current audited declarations | 31,896 |
| Retained audited declarations | 1,274 |
| Inputs matching the proof commit and the wrapper's starting commit | 2,603 |
| Clean pinned dependencies at both ends | 16 |
| Imported-source provenance checks | 356 |
| Retained manuscript provenance checks | 4 |

The earlier replay stopped at command 1,508 because four cached outputs
of the rule-relabelling module differed from their Lake hashes. Rebuilding
the committed source restored all four expected hashes. Checks before and
after this successful replay agreed with the recorded Lake hashes for
81,168 compiled files. [Cache and audit verification](V62_REBUILT_RELABEL_VERIFICATION_2026-11-17.json)

Both audits found exactly the permitted axioms `Classical.choice`,
`Quot.sound` and `propext`. The manuscript gate checked the 24 TeX files,
both PDF copies, the source archive and the selected correspondence.

The WSL wrapper began at `3f826fde8c077ce8005fc03f9d2fd0b8d00d5e3b`.
It saved successful exit statuses for 1,804 commands before the verification
server restarted. It recorded no
final wrapper exit status. Recovery matched its ordered command log and
source inputs, began at command 1,805 and completed the final 161 commands.
An independent check matched every command and log to the pinned verifier
in order and reran its final checks against the saved outputs. All 2,603
input hashes matched the published tree across both segments.

Theorem 5.3 covers the first-order and standalone propositional calculi,
including arbitrary closed slice extensions and the final reduction.
Corollary 10.9 covers the two fork partial-map slices. Their earlier
incremental verifications are recorded separately.
[Theorem 5.3 and the corrected axiom audit](V62_REBUILT_RELABEL_VERIFICATION_2026-11-17.json) ·
[Corollary 10.9](V60_FORK_ASSOCIATED_CATEGORIES_VERIFICATION_2026-11-17.json)

The 77 numbered result statements and three definitions match byte for byte
from v59 through v62. All 77 printed proofs match from v60 through v62.
[Four-edition comparison](V62_STATEMENT_COMPARISON_2026-11-17.json)

The summary gives the input snapshot and archive digests. The compressed
record contains every command, exit status, duration and log hash, the
complete axiom reports, the input hashes and their matching Git blobs.
[Summary](V62_FULL_VERIFICATION_2026-11-17.json) · [Complete record](V62_FULL_VERIFICATION_2026-11-17.json.gz)
