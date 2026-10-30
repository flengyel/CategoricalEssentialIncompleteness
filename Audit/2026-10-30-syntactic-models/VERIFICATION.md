# Verification

Date: 30 October 2026.
Baseline: 3be65406b0bb6d3109a41fd3f517ca62fcc5ed8f.

## Mathematical scope

The model interpretation, faithful product representation, extension square,
uniform lifting, reconstructed local-connectedness arguments, effective
observations, and three-point application were checked in the actual
manuscript. Confirmed source and typography defects were resolved.
See the separate hostile and writing reports.

S_T is not asserted locally connected. The target is the product of Pfn
categories indexed by arithmetic models. No soundness assumption, target
Turing universality, effective model construction, or lift of an arbitrary
target separator is used.

## Compilation and rendering

From manuscript/:

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/syntactic-models syntactic_model_range_functors.tex
~~~

The final build succeeds and produces eight pages. The final LaTeX log
has no warnings, unresolved references or citations, overfull/underfull
boxes, or undefined controls. All thirteen explicit labels and their
references resolve; every cited bibliography key is present.

All eight rendered pages were inspected as a contact sheet; the main
section/lifting proof page was also inspected at readable resolution.
The final source uses “diagonal” only for the categorical map. The compiled
PDF was copied byte-for-byte to manuscript/.

## Exact files

| File | SHA-256 |
| --- | --- |
| manuscript/syntactic_model_range_functors.tex | 26f9c2d27564982f9483349a9af1e3d6d3d5a3b6238f6b0628f373a67ee2065b |
| manuscript/syntactic_model_range_functors.pdf | 6bebd8300b8b62172fd6d70cb0f16d634662aa9cdb9e985d5b3033425177cdef |
| manuscript/sources/LOCOct10f.tex | 039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab |

The LOCOct10f source has exactly the supplied source's previously recorded
hash. It was not revised. The necessary mathematical arguments are
included with proofs in the new note.

The update adds the new source and PDF, the unchanged LOC source, and
this audit directory. It updates the root README, manuscript README, and
continuation prompt. Earlier mathematical manuscripts and all Lean files
remain unchanged. Their prior verification is reused; the older Lean
development was not run as a substitute for checking these proofs.
