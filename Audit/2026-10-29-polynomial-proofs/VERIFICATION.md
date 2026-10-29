# Verification record

Manuscript: *Domains, finite proofs, and essential incompleteness*, Florian Lengyel, 29 October 2026.

## Delivered snapshot

- PDF: 23 pages; self-contained LaTeX source.
- Source SHA-256: `433f8a30df4f6d84e6055ac1d96ec58225e765e9f01354a8fd6794fd0ed226f0`.
- PDF SHA-256: `c78f946513482768edfdc74d6fabe0a70d5ed370ef190c06b23692f20163e831`.
- Both review reports identify the same final source fingerprint.

## Checks performed

- Compiled the exact delivered source with `latexmk -pdf -interaction=nonstopmode -halt-on-error`.
- The final log contains no warnings, undefined references/citations, or overfull/underfull box messages.
- Cross-reference scan found no unresolved internal labels.
- Rendered every final PDF page. Inspected all pages in contact sheets and the Turing and witness/refutation diagrams at full-page scale. No clipping, overlap, missing symbols, or broken diagram labels was found.
- Read the full assembled source and inspected the rendered output for nonmathematical process remarks. The manuscript contains none.
- Removed all four unused appendices and their obsolete references; the main argument has no dependency on them. Removed the stable-union lemma's unused increasing-finite-power clause and the now-uncited Kelly reference.
- The outline follows all thirteen sections and their subsections and identifies the actual dependency branches.
- Applied the Hostile Referee and Mathematical Writing plugins in independent complete-source reviews. Incorporated all required local repairs and checked their resolution against the final source.

## Mathematical scope

The Turing-morphism inseparability theorem has explicit parameter-universality and binary-case assumptions. The finite-proof initial-algebra existence theorem is numerical and uses recursive presentations with at most two premises per rule. The range functor is proved for arbitrary range restriction categories. Trace witnesses and proof/refutation maps are constructed for the numerical propositional presentation, whose consistent c.e. extensions are proved incomplete. General recursion-category logical presentations and an interpretation in Robinson arithmetic remain stated problems. The Hoare and bicomodule comparisons have their own semantic role; the incompleteness proof does not assume representability of weakest liberal preconditions.

No Lean source was changed or checked in this task. No external repository commit or push was performed.
