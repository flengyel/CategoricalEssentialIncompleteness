# Verification

Date: 29 October 2026. Baseline: 896163707ed3eaa61a30f1d881e8a9f18a3ec0c8.

## Changed scope

New manuscript source and PDF, this audit directory, and navigation in the
root README, manuscript README, and continuation prompt. The preceding
three mathematical manuscripts and PDFs remain unchanged. Existing
verification of those sources is reused. No Lean file was changed or run.

## Build and visual inspection

From manuscript/:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error range_completion_three_point_cosheaves.tex
```

Result: success; seven pages. No LaTeX warnings, unresolved references,
overfull boxes, or underfull boxes were reported. The final PDF was rendered
with pdftoppm at 100 dpi; all seven pages were inspected. Text, equations,
the pushout diagram, page numbers, and bibliography are legible and unclipped.

## Final SHA-256 hashes

| Artifact | SHA-256 |
| --- | --- |
| range_completion_three_point_cosheaves.tex | 9323bdf98d24dba3c9de617fc18ff73cb8ce1f579f7417b34cbca5925e3c1397 |
| range_completion_three_point_cosheaves.pdf | 2cc521d2e84cd69a9e95ca1cac575aaf303a1905c49f04fa05bde97742e07243 |

The unchanged predecessor was also checked locally:

| Artifact | SHA-256 |
| --- | --- |
| iteration_domains_and_cosheaves.tex | e08b643797439c7d98e8a427b497e80a9f560cd734e341fc28a558f61a774701 |
| iteration_domains_and_cosheaves.pdf | 3b84757d323dc10443b6088c8f7709184d1aa2e4142decfda69f44d38f1121a9 |

The publication tree is based on the baseline tree and contains only the
explicit new note, audit files, and three navigation updates. Main is
updated with an expected-head check and without force. A final tree
comparison checks the changed paths and the retained mathematical blobs.

## Mathematical verification limits

The exact completion sources, elementary obstruction, diagram operations,
frames, evaluator domains, and case distinction received the focused
checks recorded here. Compilation checks the document, not the proofs.
No new theorem is Lean-formalized, and the older axiom-audit count has no
bearing on this continuation.
