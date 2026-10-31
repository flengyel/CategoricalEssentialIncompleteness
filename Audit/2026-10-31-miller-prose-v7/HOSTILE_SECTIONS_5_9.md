# (A) Kill-shots / hard blockers

No hard blocker was established in the assigned text. Scope: every sentence of v6 §§5–9, source lines 904–1733, was read. The categorical constructions and their appendix proofs were not re-proved in this prose audit.

# (B) Major weaknesses

## B1. Proof conclusions must belong to the sentence object — already repaired by root

- **Anchor:** §8, lines 1261–1268, `\mathrm{Prf}_T` and `c_T`.
- **Claim as written:** “let `\mathrm{Prf}_T` be its carrier of finite proofs from `T` … Reading the final sentence gives a total arrow `c_T:\mathrm{Prf}_T\to S`”.
- **Failure mode:** ambiguous / missing_definition.
- **Evidence:** structural argument. A first-order proof calculus can allow final formulas with free variables; the earlier definition makes `S` the carrier of closed sentences.
- **Repair:** require the last formula of every proof in the carrier to be a sentence. Root reports that this has been implemented in v7, here and in the Miller proof carrier.
- **Impact:** types the conclusion map and its range. Local and fully repairable; no further action if the reported edit remains.

# (C) Minor issues

The following are exact edits against v6. They preserve the definitions and substantive negative claims. Most are local precision or economy repairs, not defects in the theorem statements.

## C1. Type the program, not its numerical index

**Anchor:** §5, lines 912–916. **Mode:** ambiguous; **evidence:** source text; **severity:** minor; **repairability:** direct.

Replace:

```latex
For a typed program index $e:X\rightharpoonup Y$, let $G_e(x,y)$ be its
$\Sigma_1$ output formula. It existentially quantifies a computation trace
over a primitive-recursive trace test. Fix a deterministic programming
system whose graph identities, including functionality, composition,
and parameterization, are provable in $\PA$.
```

with:

```latex
Fix a deterministic programming system whose functionality, composition,
and parameterization identities are provable in $\PA$.
For an index $e$ of a program from $X$ to $Y$, let $G_e(x,y)$ be its
$\Sigma_1$ output formula, defined by existential quantification over
a primitive-recursive computation-trace predicate.
```

An index is numerical data. Its program has the indicated source and target. Moving the fixed system before its graph formula also removes a backward dependency.

## C2. Delete a restatement of the displayed quantifiers

**Anchor:** §5, line 926. **Mode:** redundant exposition; **evidence:** the explicit universal quantifiers in (uniform); **severity:** minor.

Delete:

```latex
The quantifiers belong to the single sentence proved in $T$.
```

Retain the subsequent comparison with pointwise provable equality in lines 942–950; that comparison states a substantive failure of composition. Also delete only the recap at lines 950–951:

```latex
The uniformly quantified equivalence
\eqref{eq:uniform} gives the well-defined composition proved above.
```

The preceding composition proof already establishes this fact.

## C3. Give the restriction idempotent its type

**Anchor:** §5, lines 953–956. **Mode:** missing_definition of the displayed arrow type; **evidence:** source text; **severity:** minor.

Replace:

```latex
Every $\Sigma_1$ formula $C(x)$ represents a partial identity: search for
a witness to $C(x)$ and then return $x$. Write $[C]_T$ for this
restriction idempotent.
Then
```

with:

```latex
For a $\Sigma_1$ formula $C(x)$ on the numerical type $X$, let
$[C]_T:X\rightharpoonup X$ be the partial identity represented by
the program that searches for a witness to $C(x)$ and then returns $x$.
For two such formulas,
```

## C4. State the range agreement being proved

**Anchor:** §5, lines 972–976. **Mode:** ambiguous; **evidence:** the phrases “two output graphs” and “required agreement equation” leave the arrows unnamed; **severity:** minor.

Replace:

```latex
For agreement, a witness to
$R_e(y)$ together with equality of two composite graphs gives equality
of the two output graphs at $y$. Existential elimination in $T$ proves
the required agreement equation. These arguments also show that the
chosen ranges are unchanged under theory extension.
```

with:

```latex
If $g,h:Y\rightharpoonup Z$ satisfy $g[e]_T=h[e]_T$, the equality
of the composite graphs, together with a witness to $R_e(y)$, proves
that the graphs of $g$ and $h$ agree at $y$. Existential elimination
therefore gives
$g\ran([e]_T)=h\ran([e]_T)$.
The same range programs represent ranges over every extension of $T$.
```

“Unchanged” should not identify arrows in two different quotient categories literally. The replacement states preservation of the program construction.

## C5. Replace the malformed implication display for a Turing morphism

**Anchor:** §5, lines 978–988. **Mode:** ambiguous typing; **evidence:** a type signature followed by a colon and an unquantified implication; **severity:** minor.

Replace the block from “The ordinary product” through “`\PA`-provably total” with:

```latex
The product and tagged-coproduct programs supply the restriction
products and coproducts. The universal program defines
$\tau:\omega\times\omega\rightharpoonup\omega$.
For every $f:X\times\omega\rightharpoonup\omega$, formalized
parameterization gives an arrow $r:X\to\omega$ represented by a
$\PA$-provably total program, with $f=\tau(r\times1_\omega)$.
Thus $\tau$ is a Turing morphism.
```

Retain the subsequent isotypical and prodominical conclusions.

## C6. Delete the second definition of `\Pfn`

**Anchor:** §6, lines 993–996. **Mode:** duplicate definition; **evidence:** `\Pfn` is defined at lines 293–294 and its domain/range interpretation is given in the preliminaries; **severity:** minor.

Delete:

```latex
The category $\Pfn$ has sets as objects and partial functions as arrows,
with ordinary composition. Restrictions and ranges are partial identities
on domains of definition and images. Restriction products are Cartesian products;
coproducts are tagged disjoint unions.
```

Start this section with “Fix a model …”. The model interpretation and all its preservation arguments remain.

## C7. Give the faithfulness conclusion directly

**Anchor:** §7, lines 1077–1079. **Mode:** vague expression; **evidence:** “This is a coordinate of `F_T`” refers to a model as if it were a coordinate of a functor; **severity:** minor.

Replace:

```latex
Completeness and downward L\"owenheim--Skolem give a model on carrier
$\N$ in which the two graphs differ. This is a coordinate of $F_T$,
which therefore distinguishes the arrows.
```

with:

```latex
Completeness and downward L\"owenheim--Skolem give
$M\in\mathcal M_T$ in which the two graphs differ. Hence
$F_M([e]_T)\ne F_M([f]_T)$, so $F_T([e]_T)\ne F_T([f]_T)$.
```

## C8. Delete the completed-coordinate recap

**Anchor:** §7.1, lines 1164–1165. **Mode:** redundant exposition; **evidence:** the proof has already established the required identity for every `M`; **severity:** minor.

Delete:

```latex
The same program works at every coordinate, proving the lifting
statement for the entire family.
```

Keep the preceding statement identifying the interpreted program with the unique section.

## C9. Preserve the separator distinction; delete its retrospective slogan

**Anchor:** §7.1, lines 1194–1197. **Mode:** redundant recap; **evidence:** the preceding sentences already distinguish source complements and arbitrary target separators; **severity:** minor.

Keep:

```latex
Lemma~\ref{lem:switch} lifts the sections associated with source
complemented restriction idempotents. An arbitrary target separator
need not come from such an idempotent.
```

Delete:

```latex
This distinction explains how a faithful range functor
can have an inseparable source pair and a separable image pair.
```

The statements about failure of Turing universality and Boolean target domain lattices are substantive and should remain.

## C10. Remove announcements and recaps around the numeral sets

**Anchor:** §8.1, lines 1303–1305 and 1343–1345. **Mode:** empty metacommentary; **evidence:** both sentences announce or recap displayed definitions; **severity:** minor.

Replace:

```latex
Let $T$ be a consistent c.e.\ extension of $\PA$.
The categorical separator contradiction can also be expressed directly
on the parameter object $\N$. Define
```

with:

```latex
For a consistent c.e.\ extension $T$ of $\PA$, define
```

Replace:

```latex
The first equivalence follows from the partial-identity graph equation;
the second is faithfulness. Thus the standard observations can also be
expressed by equations in the faithful representation.
```

with:

```latex
The first equivalence follows from the partial-identity graph equation;
the second follows from faithfulness of $F_T$.
```

## C11. Replace “the effective step” by its mathematical content

**Anchor:** §8.1, lines 1348–1353. **Mode:** vague expression; **evidence:** no single operation has been named “the effective step”; **severity:** minor.

Replace:

```latex
The effective step uses standard numeral instances and the presentation
of $T$ by computably enumerable axioms. The semantic functor exists also
for $T=\operatorname{Th}(\N)$, when $T$ is complete and $S_T$ is the
classical category of partial recursive functions on the formal numerical
types. Thus internal inseparability alone does not imply logical
incompleteness.
```

with:

```latex
The sets $E_T(c)$ are computably enumerable because the axioms of $T$
are computably enumerable. For $T=\operatorname{Th}(\N)$, the functor
$F_T$ still exists and $S_T$ is the classical category of partial
recursive functions on the formal numerical types, but $T$ is complete.
Thus inseparability in $S_T$ alone does not imply incompleteness of $T$.
```

This preserves the essential counterexample and states which hypothesis is used for effectivity.

## C12. Shorten the section roadmap, retaining its mathematical objective

**Anchor:** §9, lines 1367–1375. **Mode:** procedural repetition; **evidence:** the upcoming definitions repeat the advertised steps; **severity:** minor.

Replace the whole opening paragraph with:

```latex
We construct a recursion category $\mathscr R_X$ whose restriction
splitting contains a consistent propositional theory with no complete
consistent extension represented by a restriction idempotent.
The construction uses cosheaves on a three-point space.
```

## C13. Replace “nonnumerical” by the exact assertion

**Anchor:** §9.1, lines 1504–1511. **Mode:** ambiguous terminology; **evidence:** “nonnumerical” is not defined and can suggest stronger claims than restriction nonequivalence; **severity:** minor.

Replace:

```latex
To see that $\mathscr R_X$ is nonnumerical, note that the terminal
object of $\mathcal E$ has five subobjects,
whereas a numerical singleton has two.
```

with:

```latex
The category $\mathscr R_X$ is not restriction-equivalent to the
classical recursion category. Indeed, the terminal object of
$\mathcal E$ has five subobjects, whereas the terminal object of
$\mathcal C_{\mathrm{rec}}$ has two.
```

Replace the last sentence of that paragraph with:

```latex
Proposition~\ref{prop:fork-distinction} gives the subobject calculation.
```

The omitted second clause merely previews the failure of decidable equality. Its definition and proof remain in Appendix A, so no negative mathematical result is removed from the manuscript.

## C14. Type the numerical compiler and state its partial-function equation

**Anchor:** §9.2, lines 1548–1563. **Mode:** omitted arrow type / vague phrase; **evidence:** `s` has no signature and “including their domain tests” substitutes for equality of partial functions; **severity:** minor.

Replace “its inverse `$\operatorname{decode}_2$`” with:

```latex
its inverse $\operatorname{decode}_2:\N\to\N^2$
```

Replace lines 1557–1563 with:

```latex
For a partial recursive map
$F:Z\times\N^2\rightharpoonup\N^2$ with c.e.\ carrier $Z$,
the parameter theorem gives a total recursive map $s:Z\to\N$ such that
\[
 \varphi_{s(z)}
 =\operatorname{encode}_2\circ F(z,-)\circ\operatorname{decode}_2
 :\N\rightharpoonup\N
 \qquad(z\in Z).
\]
Thus $z\mapsto(0,s(z)):Z\to\N^2$ is the required total parameter map.
```

## C15. State naturality of the point interpretation in one equation

**Anchor:** §9.2, lines 1585–1586. **Mode:** unproved local naturality assertion; **evidence:** the component bijections are stated but their interaction with a partial arrow is omitted; **severity:** minor.

After the sentence ending `$\Phi_i\cong U E_i$`, insert:

```latex
Indeed, $fp_y=p_{E_i(f)(y)}$ when $E_i(f)(y)$ is defined, and $fp_y=0$
otherwise.
```

This states both value and domain compatibility without another diagram.

## C16. Type the counterexample to universality at component zero

**Anchor:** §9.2, lines 1595–1597. **Mode:** omitted arrow type; **evidence:** “function on `V_0`” does not name its codomain; **severity:** minor.

Replace:

```latex
For example, the numerical total function
$F(k,z,a,b)=(0,0,z,0)$ on $V_0$ cannot equal
$\tau_0(p,-)$ for a fixed $p\in V_0$.
```

with:

```latex
The total function $F:V_0\to V_0$ given by
$F(k,z,a,b)=(0,0,z,0)$ cannot equal $\tau_0(p,-)$ for any $p\in V_0$.
```

## C17. Replace “proof observations” and type the selected domains

**Anchor:** §9.3, lines 1603–1615. **Mode:** vague heading / omitted signatures; **evidence:** source text; **severity:** minor.

Replace the subsection title with:

```latex
\subsection{Propositional theories and their component theorem sets}
```

Replace “Define the complementary restriction idempotents” with:

```latex
Define complementary restriction idempotents $q_0,q_1:V\rightharpoonup V$ by
```

Replace `Put` immediately before the display defining `d,a,b` with:

```latex
Put $d=\tau\Delta_V:V\rightharpoonup V$ and define
$a,b:V\rightharpoonup V$ by
```

Then remove `d=\tau\Delta_V,\qquad` from the following display.

## C18. Use “component” for the explicitly defined component sets

**Anchor:** §9.3, lines 1713–1724. **Mode:** vague qualifier; **evidence:** all sets are defined through `E_i`; **severity:** minor.

Replace:

```latex
Proposition~\ref{prop:endpoint} makes the observed theorem and refutation
sets c.e.; total inverse image therefore makes $P_{i,t}$
and $N_{i,t}$ c.e.
```

with:

```latex
The component theorem and refutation sets $|t|_i$ and $|\nu^*t|_i$
are c.e.; their inverse images under the total recursive map
$E_i\theta$ are therefore c.e.
```

Replace “inclusions of both observed sets” by “inclusions of both component sets”.

## C19. Delete the unspecified further application

**Anchor:** final paragraph of §9, lines 1727–1733. **Mode:** ambiguous / vague recapitulation; **evidence:** the category, functor, selected pair, and sentence maps are unnamed, and the paragraph adds no statement beyond the cited corollary plus inverse-image preservation; **severity:** minor in this expository context; **repairability:** deletion.

Delete:

```latex
The observation argument also applies to another recursion category
whose restriction splitting admits a functor to $\mathcal K$
preserving restrictions, zeros, and binary joins of restriction
idempotents, and sending the selected pair to a recursively inseparable pair. A sentence object,
negation map, and total map satisfying the inequalities of
Corollary~\ref{cor:domain-incompleteness} then give the corresponding
observed theorem and refutation sets.
```

This is a generic announcement of an application, not an additional proved result required downstream.

# (D) Cross-section consistency failures

## D1. Formal numerical types versus their underlying sets in `\operatorname{Pair}(\mathrm{Rec})`

- **Anchor:** §8.1, lines 1313–1323, compared with §9.3, lines 1698–1703 and 1722–1724.
- **Claim as written:** the first definition takes objects `(X,A,B)` with `X` a numerical type and uses `(\omega,P_T,N_T)`; the later theorem uses `(\N^2,P_{i,t},N_{i,t})`.
- **Failure mode:** inconsistent_use.
- **Evidence:** typed comparison. The manuscript explicitly distinguishes the formal type `\omega` from the set `\N` at lines 907–908.
- **Repair:** in the final theorem replace the assignment by

```latex
 t\longmapsto(\omega\times\omega,P_{i,t},N_{i,t})
```

and replace “identity maps on `$\N^2$`” by “the identity of `$\omega\times\omega$`”. In the last proof paragraph replace “the identity of `$\N^2$`” by the same expression. The statement that the carriers `P_{i,t},N_{i,t}` are subsets of `\N^2` remains correct and should stay.
- **Severity:** minor; **impact:** consistent object typing; **repairability:** direct.

## D2. Definition and assertion retained after deletions

The proposed deletion in C6 relies on the first definition of `\Pfn` in §2. The deletion in C13 removes only a forward preview: the definition and proof of failure of decidable equality remain in Appendix A. The substantive distinctions between uniform and pointwise provability, source and target separators, and c.e. theories and `\operatorname{Th}(\N)` are retained.

# (E) Acceptance conditions, non-negotiable

1. Keep the sentence-ending condition in both proof carriers so their conclusion maps have codomain `S`. Without it, the typed proof-object definition remains ambiguous.
2. Keep the distinction between formal numerical types and their set-theoretic carriers consistent in the two `\operatorname{Pair}(\mathrm{Rec})` statements.
3. Replace the range-agreement paraphrase by the typed equality in C4, or an equally explicit proof.
4. Do not remove the negative mathematical claims listed in D2 while shortening their surrounding prose.
5. Compile the exact revised source after integration and check references affected by relocated or deleted text. This report does not claim compilation or Lean verification.

# (F) Not checked / uncertainty log

The complete assigned prose was read in source order, with first occurrences checked against the rest of the manuscript where needed. The review inspected Heller's primary 1990 text, beginning with the introduction and §§1–2 (printed pp.1252–1255). Heller's explicit declarations of functors, structural maps, and the distinction between binary products and a terminal object informed the recommended precision. These are applications to the present text, not claims that Heller formulated an editorial checklist. The mathematical-writing source's rules on connected exposition and introducing symbols before use support C1, C3–C5, C14–C17; the economy judgments are independent editorial choices.

The arguments in §§5–9 were checked for local typing and whether the prose stated the inference being used. This was not a fresh proof of every appendix theorem, a literature-priority review, or a Lean audit. Citations to Montagna, Di Paola–Montagna, Bernardi, and the failure-of-composition paper were not independently reread in this pass. The existing construction of the three-point-space Turing morphism was not revalidated here.

Strongest confirmed issue: the proof-carrier conclusion type, reported repaired by root. Strongest remaining confirmed issue: formal types versus carriers in the final pair-functor statement. Strongest suspected unconfirmed blocker: none identified. Most important unchecked item: the full appendix proof of the nonnumerical Turing morphism. A recommendation on mathematical acceptance would depend on that material; final recommendation: unknown. No rejection of the assigned arguments is warranted by the local prose findings alone.

## Integration check of working v7

The working source `manuscript/essential_incompleteness_via_local_connectedness_v7.tex` was read after integration. Findings B1, C1–C19, and D1 are resolved, either by the proposed text or an equivalent precise formulation. The sentence proof carriers now explicitly consist of finite derivation trees with sentence conclusions; modus ponens and generalization are specified. The formal pair-functor object is now `\omega\times\omega`, while its carrier subsets remain subsets of `\N^2`. No integration defect was found in §§5–9.

The newly added Appendix B.4 was also checked. The finite-tree evaluation proof is valid in `\operatorname{Tot}(\operatorname{Split}(\mathcal E_a))`: testing valid-tree membership first gives exactly the required source domain, and induction on a valid finite tree establishes termination and name-independent values of the algebra evaluation. Outside that carrier the membership computation diverges for every name. The rule-instance pullbacks and the sentence pullback have the stated semidecidable carriers. Generalization has no open-assumption side condition because the nonlogical assumptions are sentences.

Two local typing corrections were sent to root for Proposition `prop:first-order-proof-initial`:

1. `d_T:\mathsf{Der}_T\to\mathsf F` is an object of the slice, not the algebra structure map. State that the slice object `(\mathsf{Der}_T,d_T)`, equipped with the root-adjoining map
   `\delta_T:\mathsf H_T(\mathsf{Der}_T,d_T)\to(\mathsf{Der}_T,d_T)`, is an initial algebra.
2. The range restriction idempotent of `c_T` belongs to `\operatorname{Split}(\mathrm{Rec})` or `\operatorname{Split}(\mathcal E_a)`, respectively, not to the total category `\mathcal D`. Name this ambient restriction category in the concluding sentence.

These are repairs of the statement's arrow types; they do not change the proved construction. Both corrections were subsequently verified in the actual working v7 source: the proposition explicitly defines `\delta_T` and asserts its initiality in `\mathcal D/\mathsf F`; it places the range of `c_T` in `\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono})` or `\operatorname{Split}(\mathcal E_a)`, respectively. The two findings are resolved. No outstanding defect remains from this integration check. The earlier scope exclusions concerning the full three-point-space Turing construction and Lean remain in force.
