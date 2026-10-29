# Scope correction: the recursion category remains the starting data

Date: 29 October 2026.

Commit 00796a7bbd85359ae09578a625c3eac410aa06d9 incorrectly promoted an
arithmetic-universe comparison to the main research direction and described
the recursion-category constructions as a separate realization route.
This changed both the starting category and the theorem being sought.

The original task is the Di Paola–Heller construction from a given recursion
category, with theories and extensions in its designated computational
domain structure. The comparison note instead starts with the initial
arithmetic universe I and internal arithmetic universes C. Its undecided
proposition lives in I. It constructs no comparison from the given recursion
category, no identification of selected computational domains, and no
correspondence of the intended theory extensions.

Consequently, that note discharges none of the outstanding hypotheses of
the recursion-category construction. The validity of its stated deductions
from Ramesh's results does not remedy this absence of relevance to the task.
The prior mathematical audit checked those deductions but failed to identify
the task-level scope failure before publication.

The root and manuscript READMEs now classify it as a separate comparison.
The continuation again starts with the given recursion category and its
computational theories. No mathematical source or PDF was altered by this
scope correction, and no previously proved recursion-category result was
withdrawn. An application of introspection to the program would require
an actual construction associated with that category and a proved comparison
of the relevant domains and extensions; such a construction is not supplied
by the comparison note.

Verification: documentation-only changes; relative links checked. Publication
retains all mathematical blobs and uses a non-forced expected-head update.
No LaTeX or Lean rebuild is relevant to these changes.
