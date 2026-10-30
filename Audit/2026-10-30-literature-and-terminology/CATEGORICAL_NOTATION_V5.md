# Version 5: categorical notation and cosheaf reference

30 October 2026. Baseline: 422f37f307a61b5e09ace13f44a8b87a239cc594.

The revision identifies the objects of E as functors J -> C_rec and its
morphisms as natural transformations. It defines Y_j = Y(j) and the
morphisms r_i^Y = Y(0 -> i) explicitly. V is introduced as one such
functor, with the sources and targets of both morphisms given alongside
their numerical formulas.

The text then defines R_X inside Par(E, Mono) and states the Turing
property with its object and morphism classes. The Appendix's Turing
statement now explicitly quantifies over objects and arrows of A.
Fullness explains why this property restricts to R_X. The embedding
assertion retains its quantifier over every object of E, as required
for the restriction-splitting equivalence.

The terms “universal computation,” “transitions,” and “structure maps”
have been removed. Objects, morphisms, functors, natural transformations,
and their naturality equations replace the informal descriptions.
The prose uses “functor” and “subfunctor” explicitly. The abstract describes
the extensions by restriction idempotents on the object of formulas.

Curry, *Dualities between cellular sheaves and cosheaves*, J. Pure Appl.
Algebra 222 (2018), 966–993, Definition 2.6, is cited at the cosheaf
definition. The primary preprint arXiv:1607.06942 was read, and the
publisher record confirms the bibliographic data and DOI
10.1016/j.jpaa.2017.06.001. The finite-space equivalence remains proved
directly in the manuscript.

The review checked the object classes, the typing of V and its two
morphisms, the quantified Turing property, and the embedding needed for
the splitting equivalence. Proof changes replace terminology and spell
out naturality equations; they do not assert an additional mathematical
result. This is not a new audit of all proofs.

The exact source compiles to 28 pages with no warnings or overfull/underfull
boxes. The pages containing V, the Turing statement, and the bibliography
were inspected. Current source and PDF hashes appear in DELIVERY_V5.json.
