# Mathematical-writing review: general recursion-category construction

The supplement has a coherent construction–application–obstruction structure. The identified editorial repairs have been applied and checked in the frozen source. The Turing-fold section explains the second use of the Turing morphism and separates the constructed partial folds from the remaining domain-union hypothesis. The complete source contains no LLM-facing or revision-process remarks. No editorial blocker remains in the reviewed version.

This report covers *Finite proof algebras in range restriction categories*, dated 29 October 2026, in `general_recursion_category_construction.tex`, and its complete 13-page PDF. Exact fingerprints appear below.

The governing source is Knuth, Larrabee, and Roberts, *Mathematical Writing*: §1, printed pp. 1–6, and §§4–5, printed pp. 9–13, as supplied in `review_sources/knuth-writing-pages-1-10.txt` and `review_sources/knuth-writing-later.txt`. Section 1 points 5, 10–14, 17, 24, and 26 were checked in context. Sections 4–5 allow judgment in definition placement while requiring symbols to be defined before, or close to, their use. The report format and exact-typing conventions are supplementary plugin requirements, not claims about Knuth's wording.

## Current outline

1. **Computational domains and inseparability** (pp. 1–2). Introduces restriction categories, domains, ranges, products, separators, and consistency/completeness. Proposition 1.1 constructs an inseparable pair from the stated parameter universality and binary case distinction.
2. **Initial algebras from domains and partial folds** (pp. 2–4). Defines the restriction functor and its action on total split objects, universal-agreement unions, constructor inverses, and finite stages. Theorem 2.1 proves initiality from two specified unions and gluing of partial folds with exactly the required domain.
3. **Typed constructor maps from a universal object** (pp. 4–6). Lemma 3.1 obtains a restriction inverse from universal ranges. The section defines the partial slice and typed polynomial, gives a sufficient condition for its extension to partial arrows, constructs the coding maps, and proves parameter stability.
4. **Turing morphisms and partial folds** (pp. 6–8). Lemma 4.1 proves parameterized recursion. A typed evaluator is obtained by restricting along the range of the expression diagonal. The polynomial's map that repeats total parameters supplies the program operation. Theorem 4.2 constructs a partial fold; restricting it to the stage union supplies the gluing required by Theorem 2.1.
5. **The uniform numerical instance** (pp. 8–9). Constructs the unions and folds by uniform c.e. procedures and dovetailing. Proposition 5.1 verifies regularity, extensivity, agreement of ranges and regular images, and decidable equality.
6. **A categorical construction of a consistent presentation** (pp. 9–12). States the regular-image, list-recursion, syntax, and proof-algebra hypotheses and defines the logical rules. Lemma 6.1 identifies the least rule-closed domain. Theorem 6.2 proves consistency using finite positive-leaf lists; Corollary 6.3 transfers inseparability to every consistent computational extension.
7. **Presheaf completion and the range obstruction** (pp. 12–13). Credits Heller's example before presenting the selected presheaf construction. Proposition 7.1 proves that a particular externally indexed coproduct lacks a selected restriction range. Problem 7.2 asks for an iteration construction of the finite-stage domain unions, with stability and polynomial preservation, and for categories satisfying the logical hypotheses.

The central question is whether the finite syntax and proof algebras needed for the inseparability argument can be constructed from specified computational structure. The contribution is a conditional categorical construction, a Turing construction of its partial folds, a numerical realization, and a precise obstruction to using a selected presheaf completion without further range analysis. The text does not claim that every recursion category satisfies its hypotheses.

The principal dependencies are explicit. Constructor coding needs universal ranges and a universal object. Finite-stage initiality needs the two domain unions and partial-fold gluing. The Turing construction supplies the gluing for the stated finitary polynomials. Consistency needs regular/extensive total structure, range/image agreement, parameter-stable finite recursion, and decidable atom equality. Essential incompleteness additionally needs an inseparable pair.

## Comparison with the governing source

The table records both retained strengths and findings resolved in the frozen version. Locations use final section numbers and labels.

| Anchor | Difficulty or confirmed strength | Source principle or editorial rationale | Action and final status |
| --- | --- | --- | --- |
| §1 opening | Explains why code objects need a recursion principle before introducing definitions. | Knuth §1, points 12 and 24: motivation and effective openings. | Retained. |
| §2, restriction functor and Theorem 2.1 | Gives source/target before object and arrow actions; separates support, fold equation, and uniqueness in the proof. | Knuth §1, points 10–13; supplementary typing convention. | Retained. |
| §5 opening | “Its objects are c.e. carriers” previously appeared immediately after the definition of `R_rec`, rather than its splitting. | Knuth §1, point 17: unambiguous left-to-right reading. | Replaced by “Objects of A may be identified with c.e. carriers ...”. Checked. |
| §5, regularity proof | `2` previously occurred before its local definition. | Knuth §1, point 11, and §5, printed p. 12. | Replaced the first occurrence by `1+1`. Checked. |
| Theorem 6.2 | “Under the preceding hypotheses” previously referred to several separate assumptions over multiple paragraphs. | Knuth §1, point 5: usually self-contained theorem statements. | The statement now gives the grouped categorical, equality, and initial-algebra hypotheses. Checked. |
| Corollary 6.3 | “Assume additionally” previously left its reference implicit. | Knuth §1, point 5; precise cross-reference. | Now refers explicitly to Theorem 6.2. Checked. |
| §§3 and 5, extensivity and regularity | These standard notions were recalled after their first uses. They were not absent definitions. | Knuth §§4–5 permit contextual placement; the author prefers definitions before use. | Extensivity now precedes its use in §3; regularity precedes Proposition 5.1. Later duplicates removed. |
| §3 parameter polynomial; §6 list functor | Their source and target were recoverable but not explicitly displayed. | Supplementary typing convention and author's explicit preference. | Both are now typed endofunctors with the relevant actions stated. Checked. |
| §4 restriction embeddings | The added section used a synonym without defining it. | Knuth §1, point 11; consistent local terminology. | The synonym is now defined at first use. Checked. |
| §7 selected bottom | Initiality alone does not put `0→X` in the selected class `M`. | Mathematical scope issue, independently confirmed by the mathematical referee. | The membership assumption is explicit. Checked. |
| §§2, 5, and 7, countable gluing | The same restriction was stated twice in advance and then explained at the actual obstruction. | Plugin economy requirement; complementary explanations in Knuth §1, point 11 need not be repetitive. | Earlier denials removed. The distinction remains at the obstruction, updated for the Turing-fold result. |
| §7 Heller attribution | Known failure of ranges is attributed before the specific completion calculation. | Accurate source attribution. | Retained with §10, Example 5, p. 1267. |

## Definition-order and notation audit

- Composition, domains, their order, inverse images, ranges, universal ranges, restriction products, complementarity, inseparability, consistency, and completeness are explicitly introduced in §1. Source conditions for the restriction identities are stated. The range identities now also quantify the relevant domain and arrow types.
- The restriction functor and induced functor on total split objects are typed before their object and arrow actions. Split objects and total-arrow equations are defined locally. Universal-agreement unions and their stability precede Theorem 2.1.
- The partial slice and its total subcategory precede the typed polynomial. Its object action and arrow action are explicit. Extension to partial arrows is a separate assumption with a sufficient condition. This meets the author's principal functor-typing requirement.
- Extensivity and regularity are recalled before their first substantive uses. The numerical restriction category is explicitly distinguished from its splitting. Numerical Boolean equality is written with `1+1` before the later abbreviation `2`.
- The Turing parameter property precedes parameterized recursion. The new section defines restriction embedding, the typed evaluator, its range filter, the notation `K·q`, and the total-parameter map before using them in the fold theorem. Point notation is explained as notation for composites. Naturality is claimed only for total parameter maps, the case the proof uses.
- The list endofunctor, Boolean operations, equality test, atom inclusions, syntax constructors, logical axiom maps, proof polynomial, theorem image, and finite-list evaluation maps precede the arguments that use them. The internal notation in the consistency proof is explicitly explained in terms of arrows and subobjects.
- The selected presheaf class and partial-map category are defined before Proposition 7.1. The extra selected-bottom hypothesis is present. The distinction between `y0` and the empty presheaf is relevant and retained.
- Reused letters occur in explicitly separate constructions. The edits do not replace equality by isomorphism, or partial by total arrows, for stylistic reasons.

No alternative outline is needed. The inserted Turing-fold section follows the typed polynomial construction on which it depends and precedes the numerical and logical applications. The abstract, explanation of the Turing morphism's role, and final problem now match that organization.

## Exact repairs and verification

The most consequential local replacements are recorded here so that their effect can be assessed independently of the editing history. They are already present in the frozen source.

The numerical category paragraph now distinguishes the base category from its splitting:

```latex
Objects of $\mathscr A$ may be identified with c.e. carriers, and
its arrows with partial recursive maps between them.
```

The selected-bottom statement now states its additional hypothesis:

```latex
If $0$ is initial in $\mathscr C$ and every initial map
$0\to X$ belongs to $\mathcal M$, the selected bottom on
$yX$ is $y0\to yX$; $y0$ need not be the empty presheaf.
```

The consistency theorem now begins:

```latex
Let $\R$ be a range restriction category such that
$\mathscr E=\Tot(\operatorname{Split}_r\R)$ is regular and
extensive, restriction ranges agree with regular images, and
finite-list recursion is stable under parameters. Let $U$ have
decidable equality, and let $a,b$ be disjoint restriction domains
on $U$. Suppose that the syntax functor $F_U$ and the rule functor
$P$ defined above have parameter-stable initial algebras, with
syntax object $S$ and proof conclusion map $c:D\to S$.
Then $t_0=\ran(c)$ is consistent:
```

The typed parameter polynomial is displayed as

```latex
P_{K\Sigma}:\mathscr E/(K\boxtimes S)
    \longrightarrow\mathscr E/(K\boxtimes S).
```

The list endofunctor is displayed with both actions:

```latex
L_X:\mathscr E\longrightarrow\mathscr E,
\qquad L_X(Y)=1+X\times Y,\qquad
L_X(f)=1_1+(1_X\times f).
```

The final open problem concerns the finite-stage domain unions. The accompanying explanation distinguishes a fixed-point equation, which determines behavior on every finite stage, from an assertion that the entire domain is generated by those stages. This is substantive negative mathematics and is retained. Earlier repetitive denials of arbitrary countable gluing have been removed.

## Scope and checks

The manuscript source was read completely, including the added Turing-fold section, abstract, theorem statements, final problem, bibliography, and source comments. The final modifications were reread against the assembled source. Paragraphs serve mathematical functions: definition, construction, proof, hypothesis distinction, numerical application, attribution, counterexample, or open problem. The repeated qualifications identified above were removed at their redundant occurrences. Complete-source reading and a textual search found no process or LLM-facing material.

All 13 final PDF pages were inspected. No clipped display, overlapping text, or illegible diagram was observed. The build log has no actual warning, undefined-reference report, or overfull/underfull box; the package-description line containing the word “warning” is not a diagnostic. The parent performed the successful compilation; this reviewer inspected its output and log rather than rerunning it.

The complete mathematical-writing plugin and both supplementary references were consulted, as were the supplied Knuth sections specified above. This reviewer did not independently fetch Heller, Cockett–Lack, or Garner–Lin or rederive every mathematical proof. Heller's exact citation was verified by the parent; the selected-bottom hypothesis was separately checked with the mathematical referee. This report is an editorial review, not a certification of correctness or novelty.

The frozen source and PDF were independently hashed after review:

- Source SHA-256: `3baa04a2cc03c2e1b50721aa9489b3687e6d7db1547f58c21cb618bbb99b3491`
- PDF SHA-256: `f1dd251da1eff19f921f8c0d49489a2c6e24f0c96d0363542d00bfc450f6c550`
