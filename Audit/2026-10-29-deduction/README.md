# Deduction and essential incompleteness

The mathematical source is [deduction_and_essential_incompleteness.tex](../../manuscript/archive/deduction_and_essential_incompleteness.tex), with its [nine-page PDF](../../manuscript/archive/deduction_and_essential_incompleteness.pdf), dated 29 October 2026.

## Results and dependencies

The note proves:

1. The direct-image functor from the universal definition of range.
2. Preservation of unions by direct image and of Heller stable unions by total inverse image, using the range of a graph.
3. Preservation of an increasing stable union by finite powers, including a fixed parameter factor.
4. Least deductive closure from finitely many partial rule morphisms, a fixed axiom domain, and stable unions of the generated chains.
5. Closure on a selected restriction domain, its fixed-point category of theories, the reflector, and the contravariant theory functor on `Cons`.
6. Computational inseparability from the representation equations for the actual positive and negative domains of a theory, followed by essential incompleteness.
7. The arithmetic realization: jointly c.e. stage relations, their stable unions as ranges, formula and sentence restriction domains, parameterized generalization, numeral substitution recursive jointly in both inputs, and the theorem for a possibly non-c.e. base.

The inequality `b ≤ t` means that `t` extends `b`. The distinguished negative operation is total on the selected domain; no involution equation is imposed. For a non-c.e. base `B`, strong numeralwise definability passes to every consistent c.e. extension `T`, and the categorical theorem is applied directly to the domain representing `T`.

The stable-union citation is Alex Heller, *An existence theorem for recursion categories*, Journal of Symbolic Logic 55(3) (1990), 1252–1268. The definition used here includes the universal condition on agreement of parallel arrows and stability under `1_W ⊠ -`. It is not replaced by the existence of an order-theoretic supremum. The range definition is the universal range definition of Di Paola–Heller (1987), Definition 5.1, and Heller (1990).

The definitions were compared with `Lean/PCats/Ranges.lean`, `Lean/PCats/Unions.lean`, and `Lean/PCats/CountableUnions.lean` in `flengyel/Categorical_Rice_Shapiro` at commit `cb0622c864f50372f5ddc1882a6c66c31144c70e`. Heller's bibliographic entry was checked against the publisher record; the attribution of the stable-union definition was also checked in Lengyel, *Recursion categories of coalgebras*, arXiv:math/0105256, pp. 20–21. No new claim of priority is made.

## Verification

- Complete-source mathematical review: [HOSTILE_REVIEW.md](HOSTILE_REVIEW.md).
- Complete-source writing review against Knuth, Larrabee, and Roberts: [MATHEMATICAL_WRITING_REVIEW.md](MATHEMATICAL_WRITING_REVIEW.md).
- The exact final LaTeX source compiled with `latexmk -pdf -interaction=nonstopmode -halt-on-error`.
- The final log contains no unresolved references, citation warnings, overfull boxes, or underfull boxes.
- All nine rendered pages were visually inspected.
- `git diff --check` passed.
- No Lean source was changed, and no Lean build or axiom audit is claimed for the new construction.

Final source SHA-256: `8b5a92b888bd08bb627e5280442c6fb45dc5172726905b618fe58f72f6ce07c0`.

Final PDF SHA-256: `55dfc6924aded66f7becc4477801c5f7b6f2e09b8afc240e65f94c5611e0d3c9`.

## Continuation

The new note is the mathematical specification for the next formalization step. The existing Lean development has not yet been connected to this range-and-stable-union construction of deduction.

Proceed in dependency order:

1. Reuse or port the exact `IsRange`, `IsUnion`, and `IsStableUnion` interfaces from the cited `PCats` sources, retaining their universal clauses.
2. Formalize the range identities and union calculus of Sections 1–2, including the graph proof of inverse-image stability and the finite-power lemma with parameters.
3. Formalize the rule presentation, generated stages, conditional closure theorem, selected-domain closure, and fixed-point reflector from Section 3.
4. Formalize the typed morphisms of presentations and the contravariant closed-domain functor. Retain `Cons`, not `Con`, for the category name.
5. Connect the representation theorem to the closed theory domain and its negative inverse image. Complementarity is relative to the selected domain `s`; the computational parameter domain has top `1_U`.
6. Construct the numerical stable union from the jointly c.e. relation of stages and prove equality with the actual theorem domain. Generalization has a variable parameter and intermediate formulas lie in `q`; sentence conclusions are selected by `s`.
7. Transfer strong numeralwise definability from a possibly non-c.e. base to each consistent c.e. extension, and apply the categorical theorem to that extension itself.

Do not assume arbitrary countable unions of c.e. domains, treat negation as a strict syntactic involution, or replace the representation hypothesis by a reduction from an arbitrary preselected effectively inseparable pair. The note verifies the closure realization for `Q` and PA; it does not separately prove their numeralwise representability theorem.

The mathematical document contains the statements and proofs. This record contains the review scope and continuation instructions.
