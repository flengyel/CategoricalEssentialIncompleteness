# Logical consequence and essential incompleteness in recursion categories

**Florian Lengyel** · Manuscript v81 · 23 November 2026

[Read the PDF](logical_consequence_and_essential_incompleteness_v81.pdf) · [Download the complete LaTeX source](logical_consequence_v81_source.zip)

The paper has ten sections and five appendices. Appendix E follows seven arguments into their Lean proofs. The correspondence table lists the declarations for all 77 numbered results and three numbered definitions. [Appendix E](latex/appendices/e-reading-lean-proofs.tex) · [Lean correspondence](../FORMALIZATION_STATUS_V81.md#numbered-statements)

## Build the PDF

The source ZIP extracts to `latex/`. From that directory, run

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`. [LaTeX entry point](latex/main.tex) · [Sections and appendices](latex/README.md#files) · [Manuscript terms](NOTICE.md)
