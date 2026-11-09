# Version 51: abstract update

The manuscript, README, and [Palomar abstract](PALOMAR_ABSTRACT.txt) use the
approved account of arithmetization, categorical deduction, and essential
incompleteness. The subsequent wording clarifications identify the completed
categories as recursion categories and identify the syntactic construction
for Peano arithmetic. Consistency governs both arithmetic conclusions.

The final text has 186 words and 1391 characters including spaces.
The three copies agree after line wrapping is removed.

Version 51 is selected by `MANUSCRIPT_CURRENT.json` and
`FORMALIZATION_STATUS_V51.md`. The PDF, source ZIP, source guides, and current
Codex instructions have been updated together. The other 20 TeX files, including the introduction, are byte-identical
to version 50; only `abstract.tex` and the
version in `preamble.tex` changed. The correspondence table body is unchanged.
All 62 numbered results and three definitions retain their statements and
proof status. No Lean source was changed.

## Palomar

`docs/PALOMAR_ABSTRACT.txt` is the text to use when preparing the submission
abstract. `docs/CODEX_WSL2_CURRENT.txt` requires that wording in the assembled
metadata and preview. No CEI submission payload or registry entry is present
in the main-branch preparation record, so this update prepares the text; it
does not change live registry metadata.

## Validation

- `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` succeeded:
  73 pages, 821135 bytes. The final log contains no warnings, undefined references,
  missing characters, or overfull or underfull boxes.
- The title page and complete abstract were rendered and inspected.
- `python3 scripts/verify.py --manuscript-only` passed the source, artifact,
  archive, version, and correspondence checks. The archive contains all 22 TeX
  sources and the LaTeX README, with source bytes matching the manuscript.
- The introduction, section and appendix sources, bibliography, mathematical
  statement text, and correspondence table body are unchanged.

This is manuscript-only verification. The prior Lean verification records
remain attached to their tested commits; the Palomar port must be verified
against the current v51 target.

The [verification record](V51_ABSTRACT_VERIFICATION_2026-11-09.json) contains
the hashes and checks. The base commit is
`f647116f3fd0dbd9db479600ff76e67bee8b3d09`.
