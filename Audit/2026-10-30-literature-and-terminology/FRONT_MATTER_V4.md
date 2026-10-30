# Version 4: the purpose of the theorem and the topology of the example

30 October 2026. Focused revision of the abstract, introduction, and the
description of the three-point space in Section 8.

The [Version 4 PDF](../../manuscript/essential_incompleteness_via_local_connectedness_v4.pdf)
([source](../../manuscript/essential_incompleteness_via_local_connectedness_v4.tex))
opens with the purpose of the theorem: a locally connected target permits
an inseparability argument in a source recursion category that need not be
locally connected. Target sections lift to source arrows; the source
Turing morphism yields the inseparable pair. For the model-family functor,
the pair's image is separable in the Boolean target. Thus the abstract
describes transfer of the argument, without asserting an inseparable
target pair.

The revised introduction has six paragraphs:

1. The Di Paola–Heller problem and the purpose of using a locally connected target.
2. The historical setting and the section-lifting mechanism.
3. The non-locally connected syntactic category and its model-family functor.
4. The separate numerical application and logical essential incompleteness.
5. The Sierpiński gluing and the nonnumerical cosheaf application.
6. The roadmap.

The introduction has 471 whitespace-delimited words, down from 765.
Carrier formulas, coding frames, proof objects, and detailed verification
of the three-point construction remain in Section 8 and the appendices.
The restriction-category scope of the nonequivalence assertion is explicit.

The three-point space has opens
\(\varnothing,\{c\},\{a,c\},\{b,c\},\{a,b,c\}\).
Its two open subspaces \(\{a,c\}\) and \(\{b,c\}\) are Sierpiński
spaces; their intersection is the common open singleton \(\{c\}\).
The gluing topology is exactly the listed topology, since openness can
be tested on those two open subspaces. This also explains the cosheaf
diagram and its global pushout. Section 8 now defines the Sierpiński
space explicitly. The standard two-point definition was checked against
[Cambridge's 2019 Category Theory paper, Question 5](https://www.maths.cam.ac.uk/postgrad/part-iii/files/pastpapers/2019/paper_119.pdf);
the gluing identification follows directly from the manuscript's topology.

The writing review used the previously consulted KLR Section 1 excerpt,
especially motivation, connected exposition, and consistent terminology.
A separate mathematical reader checked the source/target roles, the
revised introduction, and the topology description against the actual theorem.
All theorem, proposition, lemma, corollary, and proof environments are
unchanged from Version 3, as are all labels, bibliography entries, and
displayed equations.

The delivered source compiled from the manuscript directory with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=../build/version4 essential_incompleteness_via_local_connectedness_v4.tex
```

The final PDF has 27 pages;
the log has no warnings, undefined references, or overfull/underfull boxes.
Pages 1–2 and 12, containing the revised passages, were inspected at
readable scale. No new whole-paper proof audit or Lean verification was
performed for this exposition change. Hashes are in [DELIVERY_V4.json](DELIVERY_V4.json).
