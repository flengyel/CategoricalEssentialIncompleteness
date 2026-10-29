# Verification: iteration domains and computational cosheaves

Date: 29 October 2026.
Repository baseline: dbd8b1ad803c1436ecf6abdc1c4ef1548f7ab4c1.

## New mathematical artifacts

| Artifact | SHA-256 |
| --- | --- |
| manuscript/iteration_domains_and_cosheaves.tex | e08b643797439c7d98e8a427b497e80a9f560cd734e341fc28a558f61a774701 |
| manuscript/iteration_domains_and_cosheaves.pdf | 3b84757d323dc10443b6088c8f7709184d1aa2e4142decfda69f44d38f1121a9 |

The PDF has 14 pages, uses letter paper, and is 392900 bytes.
Its title and author metadata match the source.

## Checks performed

- Compilation with the command below completed successfully.
- The final TeX log has no warnings, undefined references, or overfull or
  underfull boxes. The no-match status of the log search is expected.
- All 14 pages were rendered with Poppler and inspected. Interrupted or
  truncated intermediate page images were regenerated; the inspected final
  images are complete. No clipped displays, text collisions, or broken
  diagrams were found.
- The full new source was reviewed under the hostile-referee and
  mathematical-writing plugin instructions. Confirmed defects and their
  repairs are recorded in the separate reports.
- Two additional agents performed complementary focused mathematical
  checks. Their reports are in FOCUSED_CHECKS.md. An explicit leaf-tag
  refinement was added to Lemma 5.1, followed by a clean rebuild and
  inspection of the affected pages 8–14.
- Source checking covered the committed supplement, the existing review
  record, the targeted Heller scan pages, the original Lengyel2004 scan,
  version-10 errata passages, and Curry's cosheaf definitions. See
  SOURCE_CHECK.md for the exact scope.

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error iteration_domains_and_cosheaves.tex
~~~

## Unchanged mathematical sources

| Source | SHA-256 |
| --- | --- |
| manuscript/general_recursion_category_construction.tex | 3baa04a2cc03c2e1b50721aa9489b3687e6d7db1547f58c21cb618bbb99b3491 |
| manuscript/domains_hoare_profunctors_essential_incompleteness.tex | 433f8a30df4f6d84e6055ac1d96ec58225e765e9f01354a8fd6794fd0ed226f0 |

Their existing PDF blobs and verification records are retained by building
the update tree on the committed baseline. Neither PDF was rebuilt.
Only the new note, its audit directory, the two navigation READMEs, and
the continuation prompt are included in this update.

No Lean files were changed, and no Lean build or old axiom audit was run.
The reviews and PDF build verify neither machine-level correctness nor
novelty. The new mathematical statements remain paper proofs.
