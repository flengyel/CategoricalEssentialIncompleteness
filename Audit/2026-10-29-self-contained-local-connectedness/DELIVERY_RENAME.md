# Fresh filename and delivery verification

At the author's request, the active source and PDF are renamed to
`manuscript/essential_incompleteness_via_local_connectedness.tex` and
`.pdf`. The preceding basename is removed from the active manuscript
directory, and current links and the build command use the new name.
Historical reports retain the filenames and hashes they reviewed.

The source fetched directly at commit
`806cb6d19c81d178afd128132f8358cae2e60ec6` already has the corrected
sentence. The local PDF checked before this rename has Git blob
`67e2a1aa9178b688162e1c7a239fa4a44d0c030b`, which matches the PDF
entry in that commit's tree. Its extracted text also has the corrected
sentence. These checks do not establish why the author was seeing the
earlier wording; no cause is asserted.

The paper was freshly compiled under the new basename. Page 2 was
inspected at readable resolution and contains:

> Lengyel extended this existence argument by using faithful functors
> that preserve domains, coproducts, zero maps, and iteration, without
> requiring preservation of the near product [6, 7].

The old “These are iteration functors” sentence and the phrase “in the
corrected theorem” are absent from both the source and the fresh PDF.
The exact corrected qualification appears beside citations [6, 7].

From `manuscript/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/delivery-rename \
  essential_incompleteness_via_local_connectedness.tex
```

The fresh PDF has **26 pages**, with no warnings, unresolved references
or citations, or overfull/underfull boxes. It is copied from this build
to the active manuscript directory. The mathematical source is unchanged
from the fully reviewed version, so its proof reviews are reused.

| File | SHA-256 | Git blob |
| --- | --- | --- |
| `essential_incompleteness_via_local_connectedness.tex` | `99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21` | `22ebbc0e8d7f8fcab0627abd661d1639ac17d95e` |
| `essential_incompleteness_via_local_connectedness.pdf` | `469bca05c4c2579b6139ee1a42bf0b7b2bbb3efaa53fc4d78edb36d9e0fb52d5` | `3b756feaa3731c2c7bf39e0573c417b76c275106` |
