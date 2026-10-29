# Editorial review: Definability over a recursion category

Reviewed source: `manuscript/definability_indexed_predicates.tex`, dated 29 October 2026; the entire source and all five pages of the existing PDF. Governing source: Knuth, Larrabee, and Roberts, *Mathematical Writing*, Section 1 and Sections 4–5, consulted in the supplied Stanford-report text. The mathematical-writing plugin's complete instructions and both supporting references were also read.

The argument has a clear progression from computational domains to representation and inseparability. The main editorial problem is repeated defensive qualification around a comparatively short proof. The note should state its categorical data once, place the chosen-operation discussion with the morphisms that preserve those choices, and promote the arithmetic conclusion to a self-contained statement. The requested categorical description of `j` belongs at its first introduction and in the theorem.

## Current outline and section functions

The central question is how representation of recursive predicates by total computational arrows excludes a computational separator of the theorem and refutation predicates. The contribution is an ordinary categorical formulation using an indexed lattice and its domain embedding, followed by an arithmetic interpretation.

| Existing part | Function and dependencies |
| --- | --- |
| Abstract | Announces computational domains, the indexed predicate lattice, inseparability, and arithmetic essential incompleteness. |
| 1. Computations and their domains | Fixes composition, the recursion category, total arrows and binary products; defines the domain functor `E` and complementary pairs. |
| 2. An indexed lattice of predicates | Motivates the larger predicate functor `P`, introduces `j`, states naturality, and constructs the corresponding poset fibration. Depends on `C` and `E`. |
| 3. Substitution and representation | Defines substitution, the family `c_g`, and the representation relation (Definition 3.1). Then introduces the representation set, an optional selector, and an algebraic description. |
| 4. Inseparability | Defines separators and proves Theorem 4.1 by pulling representation back along the diagonal square. Depends on binary products, the two lattice functors, `j`, and existence of representatives. The final paragraph states a generalization and also lists unused computational structure. |
| 5. Extensions and the numerical interpretation | Corollary 5.1 converts inseparability to failure of coverage by disjoint domain extensions. The powerset example identifies representation with strong numeralwise definability, then derives arithmetic essential incompleteness. |
| 6. Morphisms and chosen operations | Specifies the functor and natural transformation defining a morphism; adds preservation of a selected representation operation. Ends with an undeveloped indexing aside and an adjunction warning. |
| References | Three contextual and structural sources. |

The central prerequisites are already introduced in the right order. The only substantial relocation recommended is to move the optional choice/algebra discussion in Section 3 to Section 6, after the main argument and numerical interpretation.

## Comparison with the governing source

| Manuscript anchor | Actual difficulty | Verified principle or explicit rationale | Recommended action |
| --- | --- | --- | --- |
| Abstract, lines 25–34 | The first three sentences inventory structures before reaching the result; “cover the sentence object” introduces an unexplained geometric phrase. | Knuth §1, points 12–13 and 24: reader motivation, prose that remains intelligible when formulas are skimmed, and a strong opening. | Lead with the implication from representation to inseparability; describe the extension conclusion as failure of the join to be top or state the arithmetic consequence directly. |
| Section 1, lines 58–61 | “No terminal object ... is assumed” repeats the scope already given by “binary products.” | Plugin economy requirement, not a rule attributed to Knuth. | Retain the positive binary-product statement and diagonal; delete the denial. |
| Section 2, lines 104–113 | The componentwise condition is clear, but the categorical type of `j` requested by the author is not stated. | Knuth §1, point 11, and plugin typing convention. | Introduce `j` as a monomorphism in the functor category, and identify its components as bounded-lattice order embeddings. |
| Section 2, lines 125–126 | The factorization explanation uses `k` and the source predicate `p` without giving their types in that sentence. | Knuth §1, points 11 and 17; §§4–5 allow definitions near the point of use but require enough information to follow them. | State `k:Z→X` and `(Z,p)` explicitly. |
| Section 2, lines 131–133 | A general recap and a denial about quantifiers do not contribute to any construction or inference in the note. | Plugin prohibition on proleptic denials and tautological recaps. | Delete this paragraph. The indexed-lattice terminology already states the structure being used. |
| Section 3, lines 160–187 | Three paragraphs delay the theorem with repeated distinctions between arrows, sets, choices and algorithms. The existence/chosen distinction is substantive, but stated more than once. | Knuth §1, points 10–12: connected exposition and useful complementary explanations; plugin requirement to retain substantive distinctions without repeated warnings. | Move the choice construction to Section 6 and state the distinction once through the types of `Rep`, `rho`, and its preservation equation. |
| Section 4, line 196 | The sentence following the separator definition merely restates its quantified domain. | Plugin economy requirement. | Delete it. |
| Theorem 4.1, lines 199–205 | “As in Section 2” hides the precise monomorphism hypothesis of the principal theorem. | Knuth §1, point 5: theorem statements should usually be self-contained. | State the functor types and monomorphism hypothesis explicitly. A reference to the representation definition is sufficient for the named relation. |
| Section 4, lines 244–251 | A useful generalization is embedded in an audit-style list of used and unused ingredients. | Plugin distinction between substantive mathematics and proof-audit commentary. | Retain the generalization as a direct mathematical statement; delete the retrospective ingredient list and redundant description of the domain functor. |
| Section 5, lines 302–315 | The main arithmetic conclusion is buried in running prose, followed by a repeated denial of a c.e. hypothesis on `T`. | Knuth §1, point 5, applied to the advertised main application; plugin economy requirement. | State the arithmetic consequence as a corollary with its hypotheses. Its scope then makes the separate denial unnecessary. |
| Section 5, lines 317–321 | The theory/object denial anticipates a claim the note has not made; the alternative subobject realization is not developed. | Plugin prohibition on defensive disclaimers; mathematical alternatives should have a purpose in the argument. | Remove this paragraph. The explicit theorem/refutation predicates already explain how the theory enters. |
| Section 6, lines 325–326 | “For completeness” weakens the introduction to a genuine definition. | Knuth §1, points 12 and 26; direct editorial preference for a concrete opening. | Begin “A morphism between two such structures consists of ...”. |
| Section 6, lines 351–354 | A chosen Turing indexing operation has no definition in this note; the adjunction warning addresses no theorem stated here. | Knuth §1, point 11; plugin prohibition on speculative warnings. | Omit the undeveloped indexing sentence and adjunction warning. State the forgetful functor for chosen representations directly. |

The proof's typed square and its accompanying equality work well. They give a complementary geometric and algebraic account of the same step, as recommended in Knuth §1, point 11. Retain both. The convention `gf=g∘f`, the distinction between total and partial arrows, and the distinction between strong definability and consistency are also already useful and correctly placed.

## Definition-order and notation audit

- `R`, composition, restriction and totality are introduced in Section 1 before their use. The cited category-theoretic background is appropriate for the intended audience; it need not be turned into a preliminary textbook section.
- `X\boxtimes Y`, projections, pairing, `C=Tot(R)`, and the diagonal are introduced together. The pairing laws displayed are consequences of the named restriction-product structure; they should not be advertised as a complete independent axiom list unless the uniqueness law is included.
- `E(X)`, its order and lattice operations are introduced before `E:C^op→BDLat`. The phrase “these lattices” at line 70 slightly anticipates the join hypothesis; “these ordered sets” or “each `E(X)`” is more exact.
- `BDLat` is explained immediately after its first displayed occurrence. This is acceptable under Knuth §§4–5; moving it earlier is optional, not a necessary correction.
- Complementarity and `Comp(E(X))` are defined before the representation relation. The early numerical sentence is an illustration, not a missing definition.
- `P`, its inverse-image maps, and naturality are adequately defined. Subscripts `E,P` may be omitted after the declared convention; the proof remains typed. The new statement should specify `j:E↪P` in `[C^op,BDLat]` and the component order embeddings.
- The construction of `∫P` has the necessary object, arrow and cartesian-lift descriptions. Give `k:Z→X` and the source `(Z,p)` in the factorization explanation. The induced functor `∫E→∫P` is already well motivated by naturality.
- `U,S,s,p_+,p_-`, then `c_g`, then representation are introduced in order. No new term is required simply to repeat the data. If the author wants “definability structure” as the name of the objects in Section 6, define that name once after Definition 3.1 by naming the full tuple.
- `Rep` and `rho` are correctly typed as sets and functions. Their significance is the difference between existence of witnesses and a chosen family; preserve that distinction at one location.
- `delta`, `a_±`, `gamma`, and `t` are defined immediately before use in the proof. They reduce rather than increase the complexity of the calculation. The diagram endpoints match the displayed equality.
- The powerset choice in Section 5 is valid for this ordinary indexed-lattice formulation. It is not a claim that full PER subobject lattices are powersets; do not add such a warning or replace this example for that reason.
- `bar n` for numerals differs from `bar f` for restrictions, but the argument type makes the usages unambiguous and the numeral convention is explicitly stated. This is not a consequential notation defect.
- “Computably enumerable deductive extension” should be fixed to the author's intended convention: c.e. axiom set, or c.e. deductively closed theory. Either supports the argument, with proof enumeration supplying c.e. deductive predicates in the former case. State the chosen convention once; do not silently change it during editing.
- `F_t`, `E(F)` and `eta` are typed in Section 6. `Comp(E(F)_U)` is understandable from the induced component map, but it can be replaced by the explicit pair `(F(e_+),F(e_-))` in the preservation equation if that improves readability.

## Recommended organization

Keep the six-section order. End Section 3 after the representation condition. Move its paragraphs defining `Rep` and `rho`, and its algebraic-description paragraph, into Section 6 before the preservation equation for `rho`. This puts all material about chosen operations and their morphisms together and brings the main theorem closer to its defining hypothesis. No new subsection hierarchy is needed.

## Prioritized replacement wording

### 1. Categorical type of the domain embedding

Replace the introduction of `j` in Section 2 by:

```latex
Choose a functor $P:\C^{\mathrm{op}}\to\BDLat$ and a monomorphism
\[
 j:E\hookrightarrow P
 \qquad\text{in }[\C^{\mathrm{op}},\BDLat].
\]
Its components $j_X:E(X)\hookrightarrow P(X)$ are injective bounded
lattice homomorphisms, hence order embeddings. An element of $P(X)$
is a \emph{predicate on $X$}.
```

The equivalence between this categorical formulation and the existing componentwise one uses pointwise limits in the functor category and the characterization of monomorphisms in `BDLat` as injective homomorphisms. It should be checked in the mathematical pass, rather than treated as a stylistic synonym without justification.

In Theorem 4.1, replace “and `j:E⇒P` be as in Section 2” by:

```latex
and let $j:E\hookrightarrow P$ be a monomorphism in
$[\Tot(\R)^{\mathrm{op}},\BDLat]$.
```

### 2. The fibration factorization

```latex
For $k:Z\to X$, an arrow $(Z,p)\to(Y,q)$ over $fk$ satisfies
$p\leq(fk)^*q=k^*f^*q$. This is precisely the condition for its
unique factorization over $k$ through the displayed lift.
```

### 3. Existence and chosen representations

Move this material to Section 6 and consolidate it as follows:

```latex
The representation relation defines the set
\[
 \operatorname{Rep}=
 \{(a,g)\in\Comp(E(U))\times\C(U,U):g\text{ represents }a\}.
\]
The representation condition is surjectivity of the projection onto
$\Comp(E(U))$. A choice of representatives is a set-theoretic function
$\rho:\Comp(E(U))\to\C(U,U)$ such that $\rho(a)$ represents $a$.
The axiom of choice supplies such a function from the representation
condition. Each value of $\rho$ is a total computational arrow;
the choice function itself is additional external data.
```

Retain the preservation equation for `rho`. End the section with:

```latex
Forgetting $\rho$ defines a functor from structures with chosen
representatives to structures satisfying the representation condition.
```

This preserves the material distinction without introducing an unproved adjunction or a redundant denial about algorithms.

### 4. The postproof generalization

Replace lines 244–251 by:

```latex
The inseparability conclusion also holds over any category $\C$ with
binary products, equipped with functors $E,P:\C^{\mathrm{op}}\to\BDLat$,
a monomorphism $j:E\hookrightarrow P$, and the substitution and
representation data of Definition~\ref{def:rep}, provided that $E(U)$
is nontrivial.
```

This is substantive negative-dependency information expressed positively as a mathematical generalization. The proof should be checked against this formulation in the mathematical pass.

### 5. Arithmetic conclusion

State the advertised consequence explicitly:

```latex
\begin{corollary}[Essential incompleteness]
Let $T$ be a consistent arithmetical theory in the effective language
above. If every recursive subset of $\mathbb N$ is strongly definable
numeralwise in $T$, then every consistent computably enumerable
deductive extension of $T$ is incomplete.
\end{corollary}
```

Use the existing argument involving the extension's two c.e. domains as its proof. Its statement already specifies the scope of the c.e. assumption.

### 6. Optional abstract repair

```latex
Representation of every complemented computational domain by a total
arrow forces two distinguished predicates to be recursively inseparable
in the numerical model. We formulate the argument over a recursion
category using an indexed bounded distributive lattice of predicates
and a natural monomorphism from its domain functor. The resulting
inseparability theorem excludes disjoint domain extensions whose join
is the top predicate. In arithmetic, it implies that every consistent
computably enumerable extension of a consistent theory strongly defining
all recursive sets numeralwise is incomplete.
```

The first sentence deliberately qualifies recursive inseparability by the numerical model; abstract inseparability concerns complemented computational domains.

## Layout and scope

The existing five-page PDF was rendered and all pages were inspected. Its formulas and diagram are legible, with no visible clipping. Three page breaks interrupt connected material: the domain-functor display at the end of page 1 continues as a sentence on page 2; `c_g` ends page 2 while Definition 3.1 starts page 3; the diagonal square ends page 3 while its justification starts page 4. Reflow after the prose cuts may resolve these without forced page breaks. Check the new PDF before adding spacing commands.

This is a complete editorial pass over the supplied note and existing PDF, grounded in the specified writing source. It is not an independent certification of the mathematics or of the three cited category-theory sources. No changes were made to the note, and no revised source was compiled. The categorical characterization of `j`, the algebraic-presentation scope, and the interpretation of c.e. theories should be resolved in the parallel mathematical review before final wording is accepted.

## Resolution record

The coordinating revision implemented the categorical formulation of `j`, its
component order embeddings and naturality square; made the main theorem's
monomorphism hypothesis explicit; typed the fibration factorization; moved the
choice discussion to Section 6; and removed the repeated qualifications and
undeveloped adjunction aside. The numerical model now declares its recursive
pairing and extensional equality. The arithmetic conclusion is Corollary 5.2,
and the c.e. axiomatization convention is explicit. The abstract now states the
nontriviality premise and the domain-extension conclusion directly.

The revised source was subsequently compiled and all five pages inspected by
the coordinating reviewer. No TeX warnings, undefined references, or overfull
or underfull boxes remained. The main diagonal proof and its diagram now appear
together on page 3. The mathematical review verified the equivalence of the
two formulations of `j`; the source review verified all three references.
