# Verification

Date: 29 October 2026. Base commit:
`b20c3d89757a692314413e7d83fcf4511a4f3b22`.

## Mathematical checks

- The complete new source was checked under the HostileRefereeGPT
  author-side workflow. No confirmed mathematical blocker remains.
- The coproduct domain order isomorphism proves both implications of the
  signed-extension equivalence and nonvacuity of its base presentation.
- Both functors, their arrow actions, the adjunction hom-set bijection,
  its naturality, unit, and counit were checked.
- The existing one-node proof equations were checked in the current
  committed supplement. One fixed θ works for all extensions.
- Functor reflection and full-endomorphism lifting were checked directly.
  The projection counterexample was checked componentwise, with Heller's
  actual 1990 definition inspected in the scan.
- The signed presentation is not identified with a classical Hilbert
  presentation. The latter construction remains conditional on the
  earlier proved hypotheses.

## Compilation and rendering

From `manuscript/`, the exact final source was compiled with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error inseparable_domains_and_extensions.tex
```

Exit status: 0. Output: 5 pages, 252955 bytes.
The final log contains no LaTeX warnings, unresolved references or
citations, or overfull/underfull box messages. An additional source check
found no missing label targets and no duplicate labels.

All five final pages were rendered with Poppler and visually inspected.
The mathematical displays, proof diagram, references, and margins were
legible, with no clipping or overlap. The mathematical-writing review is
provisional because fresh access to the governing Stanford source failed;
the actual source and rendering checks were completed.

| Artifact | SHA-256 |
| --- | --- |
| `inseparable_domains_and_extensions.tex` | `56f1c3fb3f24ca0c0fea2e47820e13c5237352fa83c92eea9b9052d79820d431` |
| `inseparable_domains_and_extensions.pdf` | `bccb0087214ebdd65640dcfb79fcf8162288602d5a14cd844321be9433b3d684` |

PDF Git blob identifier: `325c2c716661ada29ac8c9ad1718eb9d1e5f2d40`.

## Change scope

The change consists of the new source and PDF, six files in this audit
directory, and updates to the two READMEs and continuation document.
Earlier mathematical sources and PDFs are reused without modification;
their previous verification is not rerun. The base source Git blob
identifiers were matched before preparing the update.

No Lean source was changed or rebuilt. No axiom-audit count is offered as
evidence for the present mathematics. Build auxiliaries and rendered
images are excluded from the repository update.
