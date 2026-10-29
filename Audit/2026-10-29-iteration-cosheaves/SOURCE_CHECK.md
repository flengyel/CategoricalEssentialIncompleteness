# Source check: iteration, range factorization, and cosheaves

Date: 29 October 2026.

## Repository baselines

- Construction repository: dbd8b1ad803c1436ecf6abdc1c4ef1548f7ab4c1.
- [Lengyel2004 errata](https://github.com/flengyel/errata/tree/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004):
  lengyel2004_repairs_v10.tex, version 10, dated 20 October 2026.
- The previous [Heller source check](../2026-10-29-general-construction/HELLER_SOURCE_CHECK.md)
  was read before using the imported statements.

## Heller (1990)

The supplied scan was inspected, rather than trusting OCR alone.
Targeted printed pages: 1255–1257, 1259, 1262–1263, 1265, and 1267.

| Passage | Checked content | Use in the new note |
| --- | --- | --- |
| §2, p.1255 | Seven semigroup structure maps, their types, monad/decomposition/parameter/word laws | §1 restates the typed data |
| §3, pp.1256–1257 | Isotypical objects and a chosen frame | Formal generated objects and fixed frame; no frame-independence argument imported |
| §§4,9 | Catalogue equation, uniform generation, existence theorem | Context for generated recursion categories; the explicit example proves its evaluator directly |
| §6, p.1262 | Equality/product and division formulas have bad object subscripts; final composite in Proposition 6.2 is ill typed | §2 reconstructs descent and gives the correctly typed quotient |
| §7, pp.1262–1263 | Iteration category uses stable epimorphic finite-length maps, not all countable joins | Theorem 3.1 reconstructs the lemma using total maps on the split domain |
| §10, Example 4 | Partial maps of covariant functor categories | Antecedent for the computational arrow/cosheaf example |
| §10, Example 5, p.1267 | Generated simplicial recursion category with a diagonal having no range | Prior work and obstruction to automatic range inheritance |

In the new notation, the division condition is
(φ×φ)* ran Δ_X ≤ (ψ×ψ)* ran Δ_Y for φ:W→X and ψ:W→Y
with equal restrictions. Its quotient has type X→Y, exact domain
ran φ, and composite with φ equal to ψ.

Only the total-arrow action of Heller's semigroup functor is used.
For a partial endomorphism, the trace construction applies it separately
to the total domain inclusion and total value map. This avoids importing
a partial-arrow action from an untyped reading of the printed proof.

## Lengyel (2004) and version-10 corrections

Original: *More existence theorems for recursion categories*,
Annals of Pure and Applied Logic 125 (2004), 1–41,
DOI 10.1016/S0168-0072(03)00060-5.
The supplied original is scanned; printed pages 14–15 and 38 were inspected.

| Passage | Verified distinction |
| --- | --- |
| Original §2.6, pp.14–15 | Its iteration definition assumes countable strong unions and an operation for total endomorphisms |
| Errata §7.1 | Stable union preservation by inverse image is already proved by a graph/domain-interval argument; the new note credits it |
| Errata §§8–10 | Coalgebra images, finite limits/products, extensivity, unions, and iteration require the stated structural assumptions; underlying products cannot simply be taken as set products |
| Errata §10 | The explicit two-phase coalgebra construction is equivalent to the numerical category |
| Errata §11.2 | Corrected general union calculus explicitly requires product stability |
| Original Theorem 42, p.38; errata Appendix B | Selected-domain factorization and its pullback stability do not by themselves state regularity with every monomorphism selected |

The new §2 supplies the additional weak-choice argument: every total
monomorphism becomes a restriction monomorphism and every full-range total
map coequalizes its kernel pair. It also explains the factoriality alternative.
It does not rebrand the corrected graph pullback or union proofs as new.

The original Theorem 42 attributes the representation result to Rosolini.
Rosolini's original proof was not independently reread in this continuation;
the new note proves the factorization/descent laws it uses.

## Cosheaf source

Justin Michael Curry, *Sheaves, Cosheaves and Applications*,
University of Pennsylvania dissertation (2014), arXiv:1303.3255v2,
[primary PDF](https://arxiv.org/pdf/1303.3255).
Checked §2.1, Definitions 2.1.4–2.1.5 (PDF p.37, printed p.22),
and §2.2.1 (PDF p.41, printed p.26).

These passages fix the covariant variance and coequalizer condition.
The Sierpiński equivalence, computational subcategory, filtered evaluator,
failure of decidable equality, and two-point product counterexample are
proved in the new note itself.

## Limits of this source check

This is a targeted source check, not a complete Heller errata catalogue
or an audit of every result in the original Lengyel paper or the repairs.
No claim of novelty rests on absence from these sources.
