# Verification of version 27

The main document and standalone Appendix A compiled successfully with `latexmk` and pdfLaTeX. The final logs contain no undefined references, undefined citations or overfull boxes. Both the visible version displays and PDF titles identify version 27.

The environment's TeX format and search paths required explicit use of the existing local format and installed TeX/font directories. The final successful build logs are retained. No manuscript change was made to resolve that environment issue.

The manuscript has 78 pages; the standalone appendix has 10. Rendered pages 1, 36–39, 49–50, 66 and 72 of the manuscript and page 1 of the standalone appendix were inspected. The changed displays, references, proof transitions and version displays are legible without clipping or overlap.

The source ZIP has 23 entries, passes its integrity check and contains exactly the final modular source bytes. Eighteen source modules are unchanged. The changed files are the numerical realization, Appendix B, the cosheaf section, the preamble's version metadata, and the source README.

Direct comparisons verify that the numerical first-order proof and following arithmetic code comparison remain unchanged byte for byte; the fork-specific part of Proposition B.2 is unchanged as well. The source checks also preserve the syntactic, arithmetic, Miller, other cosheaf, and remaining appendix sources. The introduction and abstract are unchanged. The standalone Appendix A differs from version 26 only in version metadata.

The hostile, writing, and type/dependency reviews each have an initial report and a closure report. Their scope is this consolidation and its uses. No Lean source was changed or tested.
