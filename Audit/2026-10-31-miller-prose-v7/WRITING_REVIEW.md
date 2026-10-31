# Complete-source editorial review for Version 7

Final review, 31 October 2026: **Local connectedness in recursion categories and essential incompleteness**, Version 7, `manuscript/essential_incompleteness_via_local_connectedness_v7.tex`. I read the revised source throughout, including the new Appendix B.3–B.4. All eighteen recommendations below have been implemented, either directly or by an equivalent revision. The additional typing and wording issues found in the new proof-object material have also been repaired and the repairs checked in the source. No editorial repair remains open in this report. This is an editorial conclusion, not a certification of all mathematical claims.

The original review concerned Version 6, `output/pdf/essential_incompleteness_via_local_connectedness_v6.tex` (2,789 lines). Its exact recommendations and 176-block inventory are retained below as a record of that review; their line references and quoted wording describe the old snapshot, not unresolved defects in Version 7. No manuscript edits were made by this reviewer. The pass applies the current **mathematical-writing:revise-mathematical-prose** cloud skill, including its complete-source economy requirements.

The theorem statements and computational arguments are substantially more economical than the surrounding previews. The useful cuts are repeated announcements, repeated statements of the paper's setting, and conclusions that merely name the equality just proved. The negative mathematical assertions are mostly necessary: they distinguish uniform provability from pointwise provability, a represented separator from a name-dependent one, and preservation of a partial function from preservation of Turing universality. They should remain.

## Actual outline

| Location | Mathematical function |
| --- | --- |
| Abstract; §1 Introduction | State the lifting criterion, its counterexample, and the Miller, syntactic, arithmetic, and cosheaf applications. |
| §1.1 Related work | Compare the categorical antecedents and identify the Miller/Bauer–Hanson input. |
| §2.1 Partial maps and restriction idempotents | Define restrictions, compatibility, inseparability, ranges, and restriction splitting. |
| §2.2 Products, coproducts, and local connectedness | Define the structures and functors used by the theorem, including a product-preservation counterexample. |
| §2.3 Recursion categories | Define the source structure and Turing morphisms. |
| §3.1 The local-connectedness construction | Construct target sections and prove Theorem `thm:local-lifting`. |
| §3.2 A sufficient condition for lifting | Derive source lifts from disjoint joins. |
| §3.3 From inseparable restriction idempotents to incompleteness | Prove Corollary `cor:domain-incompleteness`; explain restriction splitting. |
| §4 opening | Define binary names and the precise index property of the Miller sequence. |
| §4.1 Computation independent of the binary name | Prove the compactness lemma; construct `E_a`, its Turing morphism, and the fixed-name range functors; apply §3 to the diagonal pair. |
| §4.2 Strict cuts of the Miller sequence | Construct the ordinary recursive reduction to the two strict cuts; prove inseparability and separation after every fixed-name interpretation. |
| §4.3 A theory of real closed fields | Construct the axiom and proof domains; prove essential incompleteness for extensions with `E_a`-semidecidable axioms using §3.3. |
| §5 The syntactic recursion category | Construct `S_T` and distinguish uniform from pointwise provability. |
| §6 Interpretation in models | Construct `F_M` and verify its preservation properties. |
| §7 A faithful family and theory extension | Construct `F_T`, verify the target properties and faithfulness, and give the theory-extension square. |
| §7.1 Lifting in the syntactic category | Construct the switches and apply the main theorem; explain the source/target difference in separation. |
| §8 Essential incompleteness of arithmetic | Construct numerical theorem domains and persistent finite-computation inclusions; apply §3.3. |
| §8.1 Numeral instances and theory extension | Construct the pair functor and standard observations; delimit internal inseparability through `Th(N)`; compare Bernardi. |
| §9 opening | Construct the cosheaf/functor example, its universal object, and recursion subcategory. |
| §9.1 Local connectedness and lifting | Apply the general theorem and identify the nonnumerical invariant. |
| §9.2 Evaluation functors | Prove endpoint preservation and universality; give the component-zero counterexample. |
| §9.3 Propositional theories and component theorem sets | Construct the propositional theory and prove internal and observed incompleteness. |
| A.1 Cosheaves and functor categories | Prove the cosheaf equivalence and the regular/extensive structure; distinguish categorical subobjects from subsets at each open. |
| A.2 Partial maps, ranges, and connected restriction idempotents | Prove the partial-map structure and local connectedness. |
| A.3 A universal object and a frame | Construct embeddings and the chosen isomorphisms. |
| A.4 A Turing morphism | Construct and prove universality, including equality of domains. |
| A.5 The recursion category and its splitting | Prove the splitting equivalence, non-equivalence to the classical category, and failure of decidable equality. |
| B.1 The syntax algebra | Construct finite formula trees and prove initiality. |
| B.2 The proof object and its range | Construct finite proof trees and prove leastness and consistency. |
| B.3 The universal property of the proof object | Form the pullback matching the premises of modus ponens; characterize the derivation object as an initial algebra in the slice over formulas. |
| B.4 First-order derivations and sentence proofs | Construct the initial algebra of all-formula Hilbert derivations, then obtain sentence proofs by pullback and the theorem domain by range. |
| C Necessity of section lifting for inseparability | Construct and verify the counterexample, including the particular missing lift. |

The general argument depends only on §2. The Miller and syntactic applications verify its hypotheses separately. Both logical applications then use §3.3. The cosheaf construction has its own explicitly proved categorical and syntactic prerequisites. This order should be retained.

## Source comparison

I consulted the official Stanford copy of Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1 and the relevant discussions in §§4–5 and 31–32: <https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf>. The encouragement to connect formulas with prose (§1, points 10–13), qualify definition placement (§§4–5), and preserve self-contained theorem statements (§1, point 5) argues against indiscriminate cutting. The example of cutting empty introductory prose in §32 is **Leslie Lamport's handout**, not advice to attribute personally to Knuth. These observations support the specific edits below; the paragraph inventory and report format are independent editorial methods.

I also read Heller's *An Existence Theorem for Recursion Categories* (1990) throughout in the supplied primary text. Relevant models are his direct introduction of ranges and sections in §6 (printed pp. 1261–1262), the progression from a Turing datum to its development in §8 (pp. 1263–1264), and the proof-directed introduction of the catalogue in §9 (pp. 1265–1266). His explanations identify the operation a construction performs. The recommendations use that directness, not his personal introductory asides or his occasional compression of proof obligations.

| Location | Finding | Applicable source/rationale | Action |
| --- | --- | --- | --- |
| Introduction, first two paragraphs | The first paragraph states the criterion and the second states it again with hypotheses. | §1 points 12–13 and 24; Lamport's §32 example. | E01 combines the premise and construction once, retaining the sufficient condition and counterexample. |
| Introduction, syntactic paragraph | Source non-local-connectedness is stated twice in six lines. | Sentence-level economy. | E02 removes the first repetition and retains the exact cited assertion. |
| §2 opening; §3.1 opening; Appendix A opening | These announce the subject already specified by the heading and adjacent mathematical paragraph. | Lamport §32; Heller's direct definition-led passages. | E03, E05, E15 remove the announcements. |
| §3.3 opening | “One must connect…” and “states the required connection” announce an obligation without stating it. | §1 points 10–13. | E06 states the inverse-image relation proved by the corollary. |
| §5 final sentence on primed systems | The preceding paragraph has already proved the well-defined uniform composition. | Current skill's economy requirement. | E07 deletes only the retrospective repetition; the primed/unprimed distinction remains. |
| §§6–8 | The definition of `Pfn`, a type recap after an explicitly typed display, and a paraphrase of an immediately preceding equivalence are repeated. | §1 points 10–11 allow complementary explanation, not merely renaming the same display. | E08 and E10–E12 remove repetitions while preserving the model and observation constructions. |
| End of §7 | The mathematical source/target distinction is important, but the opening and closing sentences restate it. | §1 points 11 and 17. | E09 retains the three concrete reasons and removes the verbal frame. |
| §9 opening | Four sentences narrate the order of construction already enacted in the following paragraphs. | Heller §§8–9; Lamport §32. | E14 states the construction and its purpose in two sentences. |
| A.4 last proof paragraph; B.2 after the schemes; Appendix C opening | Repeated proof conclusion, tautological identification, and indirect announcement. | Sentence economy; no mathematical quantifier or type is removed. | E16–E18 make the specified local cuts. |

## Definitions and distinctions to retain

The main definitions precede their use. Compatibility has now been defined after restriction order. The Turing-morphism parameter maps, source and target of the coproduct comparison, and the possibly partial source lift are explicit. The Miller representation defines both the oracle domain and numerical outputs; equality of domains is essential and is not expendable prose. `Rec^p`, `J_p`, `K_p`, and `I_p` are defined before the theorem is applied. The real-closed-field extension class is stated through `E_a`-semidecidable axiom sets and must not be replaced by an unqualified assertion about all extensions.

Retain the following passages, even though they use negative wording:

- The difference between uniform provable graph equality and separate proofs at standard inputs (§5). It identifies a different quotient construction and a published composition failure.
- The whole-model interpretation of computation traces and the fact that numerals need not be their carrier labels (§§6–7). These prevent a genuine confusion between standard and nonstandard computations.
- The first-digit separator's dependence on the name and the failure of `J_p tau_a` to retain universality (§4.2). These are conclusions of the example, not anticipatory disclaimers.
- The `T = Th(N)` example (§8.1), with the small cut in E13. It proves the stated limitation of internal inseparability.
- The examples showing that products and subobjects of cosheaves are not computed by taking their values at the whole space (A.1).
- The component-zero failure of Turing universality (§9.2), non-equivalence to the classical restriction category (A.5), and all of Appendix C.

I found no editorial-process or model-facing prose in the source. No theorem hypothesis, theorem conclusion, formula, or citation needs deletion for this prose pass. No revised outline is warranted.

## Original recommendations — implemented in Version 7

Line references identify the reviewed v6 snapshot. The quoted anchors and LaTeX labels remain the primary identifiers. All items E01–E18 are implemented. E01–E02, E09, E13–E14, E16, and E18 use equivalent wording rather than every proposed word; the stated editorial purposes are satisfied. In particular, the qualification on c.e. axioms in E13 and the theory scope in E14 remain explicit.

### E01 — Introduction, lines 53–72

Replace the first two paragraphs, from “We prove recursive inseparability…” through “preserves products, and reflects zero maps.”, with:

```latex
Theorem~\ref{thm:local-lifting} establishes recursive inseparability
in a recursion category through a range functor to a split locally
connected target satisfying weak choice and inverse-image preservation
of binary joins. The target provides sections associated with
complementary source restriction idempotents. If these sections lift
to source arrows, a Turing morphism gives an inseparable source pair.
The functor need not preserve restriction products.

Joins of source arrows with disjoint domains suffice for lifting
(Proposition~\ref{prop:disjoint-joins}). Without lifting the conclusion
can fail even for a faithful range functor preserving products and
reflecting zero maps
(Appendix~\ref{app:lifting-counterexample}).
```

This is an introductory summary, not a replacement for the self-contained theorem statement. The paragraph that first defines “range functor” formally remains unchanged.

### E02 — Introduction, lines 103–114

Replace the first six lines through “equality of their partial graphs.” with:

```latex
For a consistent computably enumerable (c.e.) extension $T$ of Peano
arithmetic ($\PA$), the syntactic category $S_T$ of Montagna and
Di Paola--Montagna identifies programs when $T$ proves one universally
quantified sentence asserting equality of their partial graphs
\cite{Montagna,DPM}.
```

Retain the following sentence “These categories are not locally connected…” and the rest of that paragraph.

### E03 — §2 opening, lines 181–182

Delete this paragraph:

```latex
We work in restriction categories \cite{CockettLack} and express the
recursion-category structure using binary restriction products.
```

The introduction's related-work subsection and §2.2 already state this setting with the cited equivalence. The formal restriction-category definition retains its own citation.

### E04 — §3 opening, lines 336–339

Delete the paragraph beginning “We prove an inseparability criterion…” and ending “source arrows required by the diagonal argument.” The introduction already explains this proof plan; the subsection immediately introduces the summand idempotents used by the construction.

### E05 — §3.1, line 343

Delete only:

```latex
The following argument supplies the needed sections.
```

Begin the paragraph with “For a coproduct $Y+Z$, let…”.

### E06 — §3.3 opening, lines 512–515

Replace the paragraph with:

```latex
Inseparability of theorem and refutation domains follows when their
inverse images under a total sentence map contain an inseparable pair.
```

The corollary immediately supplies the precise hypotheses, including inverse-image preservation of joins and consistency.

### E07 — §5, end of the primed-systems paragraph, lines 950–951

Delete only:

```latex
The uniformly quantified equivalence
\eqref{eq:uniform} gives the well-defined composition proved above.
```

The preceding composition paragraph proves this. Retain the full account and citation for the failure of the primed composition.

### E08 — §6 opening, lines 993–996

Replace the paragraph beginning “The category $\Pfn$ has sets…” with:

```latex
In $\Pfn$, restriction products are Cartesian products and coproducts
are tagged disjoint unions.
```

The objects, arrows, restrictions, and ranges have been defined in §2. The remaining sentence fixes the structural interpretation used in the model construction.

### E09 — End of §7, paragraph beginning “The local-connectedness theorem uses Turing universality…”, lines 1188–1197

Replace the paragraph with:

```latex
The image $F_T(\tau)$ is not universal in $\mathcal D_T$: at each
model coordinate, countably many program parameters cannot enumerate
all partial functions on its countable numerical carrier. The target
restriction lattices are Boolean, so every image of a disjoint source
pair has a separator. Lemma~\ref{lem:switch} lifts the sections
associated with complementary source restriction idempotents;
an arbitrary target separator need not be the image of such an
idempotent.
```

### E10 — §8, lines 1242–1243

Delete only:

```latex
We now represent theorems by restriction idempotents in order to apply
Corollary~\ref{cor:domain-incompleteness}.
```

The paragraph begins with the existing “Work in $\operatorname{Split}(\mathrm{Rec})$…”.

### E11 — After equation `eq:arithmetic-domain-inclusions`, line 1280

Delete:

```latex
These are inequalities of restriction idempotents in $\operatorname{Split}(\mathrm{Rec})$.
```

The paragraph establishing the splitting and the definitions of all four idempotents already fix the types.

### E12 — After equation `eq:faithful-observation`, lines 1344–1345

Retain the explanation of the two equivalences, but delete its final sentence:

```latex
Thus the standard observations can also be
expressed by equations in the faithful representation.
```

### E13 — §8.1, paragraph beginning “The effective step uses…”, lines 1348–1353

Delete its first sentence:

```latex
The effective step uses standard numeral instances and the presentation
of $T$ by computably enumerable axioms.
```

Begin the remaining paragraph with “The semantic functor exists also for…”. Keep the `Th(N)` counterexample and the conclusion about internal inseparability. The finite-computation dependence has already been proved and explained twice in §8.

### E14 — §9 opening, lines 1367–1375

Replace the introductory paragraph with:

```latex
We construct a recursion category from computably enumerable
presentations of cosheaves on a three-point space. Its restriction
splitting contains the sentence and proof objects for the propositional
theory constructed below.
```

The exact incompleteness conclusion remains in Theorem `thm:cosheaf-observation`, and the category definitions follow immediately.

### E15 — Appendix A opening, lines 1739–1742

Delete the paragraph beginning “We prove the structural claims…” and ending “$\mathscr R_X$ a recursion category.” The appendix title and its five subsection titles already identify these constructions, and §9 provides the forward references at their points of use.

### E16 — Final paragraph of the proof of `thm:fork-turing`, lines 2239–2241

Replace:

```latex
This proves equality of domains and values in component $0$. Since $c\times1_V$ is total, the componentwise domain
and value equalities prove $\tau(c\times1_V)=F$ in $\mathcal A$.
```

with:

```latex
Since $c\times1_V$ is total, these componentwise equalities of domains
and values give $\tau(c\times1_V)=F$ in $\mathcal A$.
```

The preceding forward and reverse domain arguments remain unchanged.

### E17 — Appendix B.2, line 2424

Delete only:

```latex
These are the component instances of the three logical schemes.
```

The displayed definitions already identify the three schemes, and the next paragraph uses them to define proof leaves.

### E18 — Appendix C opening, lines 2534–2537

Replace the paragraph with:

```latex
The conclusion of Theorem~\ref{thm:local-lifting} can fail without
section lifting, even when the range functor is faithful, preserves
restriction products, and reflects zero arrows.
```

## Scope

This is a complete-source editorial pass, not a new certification of correctness or novelty. The entire v6 source and revised v7 source, including the appendices and source comments, were reviewed. I consulted the current cloud skill, Heller's supplied primary text, and the official Stanford writing source. I did not modify, compile, render, commit, or push the manuscript, and performed no Lean formalization. The accepted prose cuts preserve the stated mathematical qualifications. The bibliography has no new editorial defect identified in this pass; its mathematical attributions are not being re-certified here. The new proof-object material is discussed explicitly after the historical inventory.

## Paragraph-function inventory

The inventory below classifies every prose-containing blank-line-delimited source block in the reviewed v6. It is a historical inventory, annotated by recommendations now implemented in v7. Adjacent theorem statements and first proof paragraphs are sometimes one source block; they are marked accordingly. Displays within a paragraph are included with that paragraph. Headings, the preamble, and bibliography entries are not counted as prose paragraphs. The first-text anchors distinguish blocks even after line numbers change. “Orientation” denotes a transition explaining the mathematical task; the specific redundant cases were identified above. The new B.3–B.4 material is classified in the final review below.

| Block | v6 line | Function | First-text anchor / action |
| --- | ---: | --- | --- |
| P001 | 23 | Result summary | We prove a range-functor criterion for recursive inseparability in a recursion category, with l… |
| P002 | 32 | Result summary | Miller's sequence yields a recursion category of partial numerical functions computed independe… |
| P003 | 41 | Result summary | We also construct faithful model interpretations of the syntactic recursion categories associat… |
| P004 | 53 | Problem / principal result or application | We prove recursive inseparability in a recursion category by using a range functor into a local…; **E01** |
| P005 | 62 | Problem / principal result or application | Theorem~[reference] states the criterion. The target is split, satisfies weak choice, and has i…; **E01** |
| P006 | 74 | Problem / principal result or application | The principal application uses a sequence $a:\N\to[0,1]$ constructed by Miller [reference]. We … |
| P007 | 92 | Problem / principal result or application | This example gives a theory of real closed fields with constants $c_n$ and the strict rational … |
| P008 | 103 | Problem / principal result or application | The syntactic recursion categories of Montagna and Di Paola--Montagna give an application with …; **E02** |
| P009 | 115 | Problem / principal result or application | The numerical instance of the criterion gives a fixed recursively inseparable pair. Finite comp… |
| P010 | 128 | Mathematical roadmap | After the preliminaries, Section~[reference] proves the general criterion and its incompletenes… |
| P011 | 139 | Compare and attribute sources | Di Paola and Heller proposed inseparability of theorems and refutable sentences as part of a ca… |
| P012 | 149 | Compare and attribute sources | Di Paola and Heller introduced dominical categories as a setting for recursion theory [referenc… |
| P013 | 160 | Compare and attribute sources | Di Paola and Heller proved recursive inseparability in dominical recursion categories satisfyin… |
| P014 | 169 | Compare and attribute sources | Miller constructed a sequence that enumerates every real in $[0,1]$ computable uniformly from i… |
| P015 | 181 | Orient construction or proof | We work in restriction categories [reference] and express the recursion-category structure usin…; **E03** |
| P016 | 186 | Define / construct; justify stated properties | Composition is written $gf=g\circ f$, so $f$ is applied first. A \emph{restriction category} is… |
| P017 | 210 | Define / construct; justify stated properties | Restriction idempotents on $X$ are ordered by $a\le b$ when $ba=a$. Their meet is composition, … |
| P018 | 226 | Define / construct; justify stated properties | For $f:X\rightharpoonup Y$ and a restriction idempotent $a$ on $Y$, the \emph{inverse image} of… |
| P019 | 242 | Define / construct; justify stated properties | A restriction idempotent $e$ on $X$ \emph{splits} if $e=mr$ for a total $m:A\to X$ and $r:X\rig… |
| P020 | 256 | Define / construct; justify stated properties | A \emph{binary restriction product} $X\times Y$ has total projections $\pi_1:X\times Y\to X$ an… |
| P021 | 273 | Define / construct; justify stated properties | Binary \emph{restriction coproducts} are categorical coproducts with total injections $i_0:X\to… |
| P022 | 282 | Define / construct; justify stated properties | A \emph{range functor} $F:\mathcal C\to\mathcal D$ is a covariant functor preserving restrictio… |
| P023 | 301 | Define / construct; justify stated properties | A restriction idempotent $a$ on $X$ is \emph{connected} if, for restriction idempotents $b,c$ o… |
| P024 | 318 | Define / construct; justify stated properties | A restriction category with binary restriction products and zeros is \emph{prodominical} if $f\… |
| P025 | 323 | Define / construct; justify stated properties | A \emph{Turing morphism} on $U$ is an arrow $\tau:U\times U\rightharpoonup U$ such that, for ev… |
| P026 | 336 | Orient construction or proof | We prove an inseparability criterion using a range functor into a split locally connected categ…; **E04** |
| P027 | 343 | Define / construct; justify stated properties | The following argument supplies the needed sections. For a coproduct $Y+Z$, let $\varepsilon_0=…; **E05 (first sentence)** |
| P028 | 350 | State result and begin proof | Let $\mathcal A$ be a restriction category with ranges, restriction zeros, and binary restricti… |
| P029 | 369 | State result and begin proof | Let $\mathcal A$ be a locally connected split restriction category with ranges, restriction zer… |
| P030 | 405 | Proof | For arbitrary $u,v:W\rightharpoonup X+X$ with $pu=pv$, split their common restriction idempoten… |
| P031 | 413 | Proof | Weak choice supplies a section $s$. The equations $ps=\bar s$ and $psp=p$ imply $\bar s=\ran(p)… |
| P032 | 421 | Proof | For $a=c'$ and $b=c$, the section is total because $c'\vee c=1_X$. The equality $p(sc)=c=p(i_1c… |
| P033 | 426 | State result and begin proof | Let $\mathscr R$ be a prodominical recursion category with ranges and binary restriction coprod… |
| P034 | 454 | Proof | Applying $F$ to the source equation $b\tau\Delta_Ug=\ell_cg$ gives \[ \chi_{U,U}^{-1}F(b\tau\De… |
| P035 | 477 | State result and begin proof | Let $\mathcal C$ be a restriction category with restriction zeros and binary restriction coprod… |
| P036 | 499 | Proof | Put $\Gamma=Fc$ and $\Gamma'=Fc'$. Preservation of composition and coproduct injections gives $… |
| P037 | 512 | Orient construction or proof | Theorem~[reference] supplies an inseparable pair in its source recursion category. To obtain in…; **E06** |
| P038 | 517 | State result and begin proof | Let $\mathcal C$ be a restriction category with restriction zeros and binary joins of restricti… |
| P039 | 547 | Interpret consistency and completeness equations | For a sentence object $S$, a negation map $\nu$, and a restriction idempotent $t$ representing … |
| P040 | 556 | Transfer inseparability to restriction splitting | An inseparable pair on an object of $\mathscr R$ remains inseparable in $\operatorname{Split}(\… |
| P041 | 564 | Orient construction or proof | We apply the criterion to computations whose domains and values are independent of the binary n… |
| P042 | 570 | Define / construct; justify stated properties | Fix a recursive bijection $\langle-,-\rangle:\N^2\to\N$ and an acceptable enumeration $(\Phi_e^… |
| P043 | 588 | Define / construct; justify stated properties | Miller's construction gives a sequence $a\in Q$ with the following property: if a program $d$ c… |
| P044 | 603 | State result and begin proof | There is one oracle program which, from $p\in P_z$ and numerical inputs $e,n$, computes the par… |
| P045 | 626 | Proof | For fixed $e,n,m$, let \[ H_{e,n,m}=\{q\in2^{\N}:\Phi_e^q(n)\mathord\downarrow=m\}. \] Finite h… |
| P046 | 640 | Define / construct; justify stated properties | For the fixed sequence $a$, let $\mathcal E_a$ have the objects generated from $\N$ by binary C… |
| P047 | 648 | State result and begin proof | The category $\mathcal E_a$ is a locally connected recursion category with ranges, binary restr… |
| P048 | 669 | Proof | For every input $x$, the singleton partial identity $1_{\{x\}}$ is recursive. It is connected, … |
| P049 | 678 | Proof | Lemma~[reference] puts $\tau_a$ in $\mathcal E_a$. Let $f:X\times\N\rightharpoonup\N$ be repres… |
| P050 | 693 | Define / construct; justify stated properties | For $p\in P_a$, let $\mathrm{Rec}^{p}$ be the recursion category on the same numerical objects,… |
| P051 | 711 | Construct data and apply a theorem | If complementary source domains $c,c'$ partition a numerical object $X$, run their two membersh… |
| P052 | 732 | Define / construct; justify stated properties | Define \[ L_a=\{n:a(n)<\tfrac12\},\qquad R_a=\{n:a(n)>\tfrac12\}. \] Their partial identities b… |
| P053 | 742 | State result and begin proof | There is an ordinary total recursive map $h:\N\to\N$ such that \[ h^{-1}(L_a)=A_0,\qquad h^{-1}… |
| P054 | 767 | Proof | Equip $Q$ with the metric \[ d(z,w)=\sum_{n\geq0}2^{-n-1}\|z(n)-w(n)\|. \] For a nonempty box r… |
| P055 | 797 | Proof | Uniform compilation supplies a total recursive $h$ such that program $h(e)$, with oracle $p$, c… |
| P056 | 808 | State result and begin proof | The domains $1_{L_a},1_{R_a}:\N\rightharpoonup\N$ are inseparable in $\mathcal E_a$. Neverthele… |
| P057 | 828 | Distinguish notions / counterexample / failed implication | In particular, $J_p\tau_a$ is not a Turing morphism in the target. Indeed, $h^{-1}(C_p)$ is a $… |
| P058 | 837 | Define / construct; justify stated properties | Call a subset $D$ of a numerical object \emph{$\mathcal E_a$-semidecidable} when its partial id… |
| P059 | 853 | State result and begin proof | Let $a$ be a Miller sequence with property~[reference], and let $T_a$ be the theory~[reference]… |
| P060 | 886 | Proof | For $n\in L_a$, the sentence $c_n<1/2$ is an axiom of $T_a$. For $n\in R_a$, the axiom $1/2<c_n… |
| P061 | 906 | Define / construct; justify stated properties | Let $T$ be a consistent classical theory in the language of arithmetic containing $\PA$. Write … |
| P062 | 918 | Define / construct; justify stated properties | The category $S_T$ has these formal types as objects and typed indices modulo the equivalence r… |
| P063 | 931 | Proof | For a program operation $\operatorname{comp}$ implementing composition, $\PA$ proves  G_{\opera… |
| P064 | 942 | Distinguish notions / counterexample / failed implication | The pointwise relation defining the primed systems is different: two programs are identified wh…; **E07 (last sentence)** |
| P065 | 953 | Define / construct; justify stated properties | Every $\Sigma_1$ formula $C(x)$ represents a partial identity: search for a witness to $C(x)$ a… |
| P066 | 978 | Proof | The ordinary product and tagged-coproduct programs supply the restriction products and coproduc… |
| P067 | 993 | Define / construct; justify stated properties | The category $\Pfn$ has sets as objects and partial functions as arrows, with ordinary composit…; **E08** |
| P068 | 998 | Define / construct; justify stated properties | Fix a model $M\models T$. Interpret numerical types recursively by \[ X_M=\|M\|\quad(X=\omega),… |
| P069 | 1015 | State result and begin proof | For every $M\models T$, [reference] defines a covariant functor $F_M:S_T\to\Pfn$ preserving res… |
| P070 | 1029 | Proof | The definedness predicate $\exists y\,G_e(x,y)$ gives the interpreted function's domain. Simila… |
| P071 | 1043 | Define / construct; justify stated properties | Let $\mathcal M_T$ be the set of all structures for the language of arithmetic with underlying … |
| P072 | 1051 | Define / construct; justify stated properties | Define the product category \[ \mathcal D_T=\prod_{M\in\mathcal M_T}\Pfn. \] An object is a fam… |
| P073 | 1064 | State result and begin proof | The functor $F_T$ is faithful and preserves restrictions, zeros, binary restriction products an… |
| P074 | 1081 | Proof | A restriction idempotent in $\mathcal D_T$ is a family of partial identities on subsets. Its sp… |
| P075 | 1089 | Proof | A partial monomorphism has injective coordinate functions: test its defining property on single… |
| P076 | 1097 | Distinguish notions / counterexample / failed implication | For consistent computably enumerable $T\supseteq\PA$, the source $S_T$ is not locally connected… |
| P077 | 1103 | Define / construct; justify stated properties | For an inclusion $T\subseteq T'$ of consistent theories, define \[ Q_{T,T'}:S_T\to S_{T'},\qqua… |
| P078 | 1129 | State result and begin proof | Let $c,c'$ be complementary restriction idempotents on $X$ in $S_T$. There is a total arrow $s:… |
| P079 | 1160 | Proof | In each $M\models T$, the interpretations of $C,C'$ partition $X_M$. The interpreted program se… |
| P080 | 1168 | State result and begin proof | For every consistent $T\supseteq\PA$, the functor $F_T$ satisfies the lifting hypothesis of The… |
| P081 | 1188 | Distinguish notions / counterexample / failed implication | The local-connectedness theorem uses Turing universality in its source. The target $\mathcal D_…; **E09** |
| P082 | 1201 | Define / construct; justify stated properties | Let $\mathrm{Rec}$ be the classical recursion category on the formal numerical types, with part… |
| P083 | 1207 | Construct data and apply a theorem | Use the universal program of Section~[reference], whose computation and parameterization identi… |
| P084 | 1242 | Define / construct; justify stated properties | We now represent theorems by restriction idempotents in order to apply Corollary~[reference]. W…; **E10 (first sentence)** |
| P085 | 1253 | Define / construct; justify stated properties | Let $S$ be the recursive set of codes of closed arithmetic sentences. Negation and numeral subs… |
| P086 | 1271 | Proof | The finite computation proofs of $\alpha(\bar n)$ for $n\in A$ give $a\le\theta^*t_{\PA}$. For …; **E11 (last sentence)** |
| P087 | 1282 | State result and begin proof | The theorem and refutation sets of every consistent computably enumerable extension of $\PA$ ar… |
| P088 | 1303 | Define / construct; justify stated properties | Let $T$ be a consistent c.e.\ extension of $\PA$. The categorical separator contradiction can a… |
| P089 | 1328 | Define / construct; justify stated properties | For a restriction idempotent $c=[C]_T$ on $\omega$, define the subset of the standard natural n…; **E12 (last sentence)** |
| P090 | 1348 | Distinguish notions / counterexample / failed implication | The effective step uses standard numeral instances and the presentation of $T$ by computably en…; **E13 (first sentence)** |
| P091 | 1355 | Compare and attribute sources | Bernardi's earlier method uses precomplete equivalence relations. In the numerical case, precom… |
| P092 | 1367 | Orient construction or proof | We construct a recursion category $\mathscr R_X$ whose restriction splitting contains a consist…; **E14** |
| P093 | 1377 | Define / construct; justify stated properties | For a topological space $X$, let $\mathcal O(X)$ be the category of open sets and inclusions. A… |
| P094 | 1441 | Define / construct; justify stated properties | Define an object $V:J\to\mathcal C_{\mathrm{rec}}$ of $\mathcal E$ by the following objects $V_… |
| P095 | 1467 | State construction result with proof reference | Theorem~[reference] constructs a Turing morphism $\tau:V\times V\rightharpoonup V$ in $\mathcal… |
| P096 | 1476 | State construction result with proof reference | Every object $Y$ of $\mathcal E$ admits a total map $m:Y\to V$ in $\mathcal A$ with a partial i… |
| P097 | 1487 | Construct data and apply a theorem | For an object $Y$ of $\mathcal E$ and an element $y\in Y_0$, take the subfunctor with component… |
| P098 | 1515 | Define / construct; justify stated properties | Let $\mathcal K=\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono})$. This is the… |
| P099 | 1531 | State result and begin proof | The covariant functors $E_j$ preserve restrictions, zeros, ranges, binary restriction products … |
| P100 | 1548 | Proof | Use the recursive bijection $\operatorname{encode}_2:\N^2\to\N$, its inverse $\operatorname{dec… |
| P101 | 1566 | Define / construct; justify stated properties | For $i\in\{1,2\}$, let $H_i:J\to\mathcal C_{\mathrm{rec}}$ have component $\{*\}$ at $i$ and em… |
| P102 | 1594 | Distinguish notions / counterexample / failed implication | The functor $E_0$ does not preserve this Turing morphism's universality. For example, the numer… |
| P103 | 1605 | Construct data and apply a theorem | Let $\zeta:V\to V+V$ be the coproduct isomorphism of Lemma~[reference]: it selects the summand … |
| P104 | 1638 | Define / construct; justify stated properties | We construct a theory in classical propositional logic from the disjoint restriction idempotent… |
| P105 | 1687 | State result and begin proof | Fix $i\in\{1,2\}$. For every consistent theory $t$ extending $t_0=\ran(c)$ on $S$ in $\mathcal … |
| P106 | 1713 | Proof | The atom map $E_i\theta:\N^2\to S_i$ is total recursive. Proposition~[reference] makes the obse… |
| P107 | 1722 | Proof | If $t\le t'$, monotonicity gives inclusions of both observed sets, so the identity of $\N^2$ is… |
| P108 | 1727 | State generalization and its prerequisites | The observation argument also applies to another recursion category whose restriction splitting… |
| P109 | 1739 | Orient construction or proof | We prove the structural claims about $\mathcal E$, $\mathcal A$, and $\mathscr R_X$ made in Sec…; **E15** |
| P110 | 1746 | Define / construct; justify stated properties | Write $D=\{c\}$, $L=\{a,c\}$, and $R=\{b,c\}$ for the nonempty proper opens of $X$. Morphisms o… |
| P111 | 1750 | State result and begin proof | Restriction to $D,L,R$ defines an equivalence $\operatorname{CoSh}(X,\mathbf{Set})\simeq\mathbf… |
| P112 | 1776 | Define / construct; justify stated properties | For an object $Y$ of $\mathcal E$, the pushout has a quotient presentation on the tagged carrie… |
| P113 | 1785 | Distinguish notions / counterexample / failed implication | Products and subobjects are taken in $\mathcal E$. In particular, the cosheaf associated with $… |
| P114 | 1804 | Define / construct; justify stated properties | A \emph{regular epimorphism} is a coequalizer of a pair of arrows. A category is \emph{regular}… |
| P115 | 1820 | State result and begin proof | The categories $\mathcal C_{\mathrm{rec}}$ and $\mathcal E=\mathcal C_{\mathrm{rec}}^J$ have fi… |
| P116 | 1837 | Proof | For a total arrow $f:Y\to Z$, enumerate $Y$ and its computed values to enumerate $f(Y)$. The fa… |
| P117 | 1853 | Proof | Limits and tagged finite coproducts in $\mathcal E$ are formed componentwise. Their universal m… |
| P118 | 1871 | Proof | The three objects of $\mathcal E$ \[ H_0=(1\leftarrow1\to1),\qquad H_1=(1\leftarrow0\to0),\qqua… |
| P119 | 1886 | Proof | Finally, for a map $Y\to A+B$, the inverse images of the two tags form c.e.\ subfunctors $Y^A,Y… |
| P120 | 1895 | State result and begin proof | The category $\mathcal A=\operatorname{Par}(\mathcal E, \operatorname{Mono})$ is a split prodom… |
| P121 | 1926 | Proof | The restriction $\bar f$ is the partial identity on $D_f$. The restriction axioms reduce compon… |
| P122 | 1940 | Proof | The component images $f_j((D_f)_j)$ form a c.e.\ subfunctor $I_f\subseteq Z$. Its partial ident… |
| P123 | 1951 | Proof | For a total $u:W\to Z$, the projection $D_f\times_Z W\to W$ has component image $u_j^{-1}(f_j((… |
| P124 | 1968 | Proof | Suppose that $p:Y\rightharpoonup Z$ is a partial monomorphism and let $D_p$ be its domain subfu… |
| P125 | 1982 | State result and begin proof | The category $\mathcal A$ is locally connected.   Let $Y$ be an object of $\mathcal E$. For $y\… |
| P126 | 1998 | Proof | Suppose that partial arrows $f,g:Y\rightharpoonup Z$ agree after composition with every connect… |
| P127 | 2010 | Define / construct; justify stated properties | Let $V$ be the object of $\mathcal A$ defined in [reference]. A \emph{total restriction embeddi… |
| P128 | 2016 | State result and begin proof | Every object of $\mathcal E$ has a total restriction embedding into $V$.   Let $Y$ be an object… |
| P129 | 2035 | Define / construct; justify stated properties | For an object $Y$ of $\mathcal E$, let $Y^\#$ have at component $j$ the nonempty finite words o… |
| P130 | 2050 | Define / construct; justify stated properties | Fix a recursive pairing bijection $\pi:\N^2\to\N$ and recursive tuple bijections $\gamma_n:\N^n… |
| P131 | 2056 | State result and begin proof | There are isomorphisms in $\mathcal E$ $V\cong V\times V$, $V\cong V+V$, and $V\cong V^\#$.   F… |
| P132 | 2067 | Proof | For the coproduct isomorphism, write $k=2q+t$ with $t\in\{0,1\}$. Send a tuple with first coord… |
| P133 | 2073 | Proof | For the word isomorphism, decode $k$ as the nonempty word $(k_1,\ldots,k_n)$. Decode $z,a,b$ by… |
| P134 | 2088 | Orient construction or proof | We construct a Turing morphism $\tau:V\times V\rightharpoonup V$ in $\mathcal A$ by giving a mo… |
| P135 | 2092 | Define / construct; justify stated properties | Fix recursive bijections $\operatorname{encode}_n:\N^n\to\N$, with recursive inverses $\operato… |
| P136 | 2109 | State result | The object $V$ of $\mathcal A=\operatorname{Par}(\mathcal C_{\mathrm{rec}}^J, \operatorname{Mon… |
| P137 | 2128 | Proof | For $i=1,2$, let $T_i\subseteq V_i\times V_i$ be the c.e.\ set on which the numerical computati… |
| P138 | 2136 | Proof | At component $0$, write the program and input as \[ P=(k,p_0,p_1,p_2)\in V_0, \qquad x=(\ell,x_… |
| P139 | 2164 | Proof | If $(P,x)\in T_0$, then \[ (r_i^V P,r_i^V x)=((k,p_i),(\ell,x_i))\in T_i. \] Thus $T=(T_0,T_1,T… |
| P140 | 2180 | Proof | Now let $F:Y\times V\rightharpoonup V$ be any partial arrow. Choose its representation by a c.e… |
| P141 | 2204 | Proof | Define the component maps of $c:Y\to V$ by  c_i(y_i)&=(0,s_i(y_i)) &&(i=1,2),\\ c_0(y)&=(0,s_0(… |
| P142 | 2218 | Proof | At component $i\in\{1,2\}$, equations [reference] and [reference] show that $\tau_i(c_i(y_i),v_…; **E16 (last sentences)** |
| P143 | 2245 | State result and begin proof | Let $\mathscr R_X$ be the full subcategory of $\mathcal A$ whose objects are obtained from $V$ … |
| P144 | 2265 | Proof | Restrictions and ranges of arrows between objects of $\mathscr R_X$ are endomorphisms of object… |
| P145 | 2272 | Proof | For a restriction idempotent $e$ on an object $Y$ of $\mathscr R_X$, write $m_e:D_e\to Y$ and $… |
| P146 | 2290 | Proof | The same construction gives a functor from the restriction splitting of $\mathrm{Rec}$ to $\mat… |
| P147 | 2304 | Define / construct; justify stated properties | \emph{Decidable equality} on $V$ means a morphism $\epsilon:V\times V\to1+1$ in $\mathcal E$ wh… |
| P148 | 2308 | State result and begin proof | The recursion category $\mathscr R_X$ is not equivalent, as a restriction category, to the clas… |
| P149 | 2326 | Proof | Suppose that $\epsilon$ decides equality on $V$. The functor $1+1$ is constant and sends both n… |
| P150 | 2338 | Orient construction or proof | Let $\mathcal E=\mathcal C_{\mathrm{rec}}^{J}$, where $J=(1\leftarrow0\to2)$, and let $\mathcal… |
| P151 | 2349 | Define / construct; justify stated properties | Fix recursive encodings of finite rooted ordered trees and of finite tuples of natural numbers,… |
| P152 | 2368 | Define / construct; justify stated properties | The covariant functor $P:\mathcal E\to\mathcal E$ is defined by \[ P(Z)=V+Z+(Z\times Z),\qquad … |
| P153 | 2378 | State result and begin proof | The algebra $\iota:P(S)\to S$ is initial in the category of $P$-algebras in $\mathcal E$: for e… |
| P154 | 2393 | Proof | Write $z_i=Z(0\to i):Z_0\to Z_i$ for $i=1,2$. Naturality of $\alpha$ says that applying $z_i$ a… |
| P155 | 2407 | Define / construct; justify stated properties | Let $a,b$ be disjoint restriction idempotents on $V$ in $\mathcal A$. Let $A,B\subseteq V$ be t…; **E17 (last sentence)** |
| P156 | 2426 | Define / construct; justify stated properties | A proof at component $j$ is a finite rooted ordered tree with the following node data and concl… |
| P157 | 2438 | Define / construct; justify stated properties | Let $\mathrm{Prf}_j$ be the set of codes of these trees. Tree shape, formula syntax, and premis… |
| P158 | 2448 | Define / construct; justify stated properties | For $i=1,2$, replace formula parameters by their images under $\sigma_i$, positive or negative … |
| P159 | 2468 | State result and begin proof | For disjoint restriction idempotents $a,b$ on $V$ in $\mathcal A$, the syntax and proof objects… |
| P160 | 2491 | Proof | Each leaf supplies a proof of its axiom instance. Given proofs of $\alpha$ and $\alpha\Rightarr… |
| P161 | 2502 | Proof | For consistency, fix a component $j$ and suppose two proofs $p,q\in\mathrm{Prf}_j$ conclude $\v… |
| P162 | 2513 | Proof | The three logical schemes are true under this assignment. For the first, a true $\alpha$ makes … |
| P163 | 2526 | Proof | Consequently $T_j\cap\nu_j^{-1}(T_j)=\varnothing$ for every $j$. Restriction idempotents, inver… |
| P164 | 2534 | Distinguish notions / counterexample / failed implication | Consider the statement obtained from Theorem~[reference] by dropping its lifting hypothesis. We…; **E18** |
| P165 | 2539 | Define / construct; justify stated properties | Fix an acceptable numbering $(\varphi_e)_{e\in\N}$ of the ordinary partial recursive functions … |
| P166 | 2555 | Define / construct; justify stated properties | The objects of $\mathcal C_K$ are the formal numerical types generated from $\N$ by binary prod… |
| P167 | 2565 | Define / construct; justify stated properties | On $\N$, the arrows are precisely the functions \[ f_{e,a}(x)\simeq  \varphi_e(x),&x\in W_a^K,\… |
| P168 | 2578 | State result and begin proof | The category $\mathcal C_K$ is a prodominical recursion category with binary restriction coprod… |
| P169 | 2591 | Proof | Let $f:X\rightharpoonup Y$ and $g:Y\rightharpoonup Z$ have ordinary partial recursive extension… |
| P170 | 2605 | Proof | Cartesian products and tagged copairings preserve the arrow class: their domains are respective… |
| P171 | 2613 | Proof | The set $f(D_f)$ is c.e.\ relative to $K$: enumerate $D_f$ and run $f_0$ on its elements. The p… |
| P172 | 2624 | Proof | Define $\tau_K:\N\times\N\rightharpoonup\N$ by \[ \tau_K(\langle e,a\rangle,x)\simeq f_{e,a}(x)… |
| P173 | 2653 | Proof | The inclusion $F$ is faithful and preserves restrictions, zeros, ranges, binary restriction pro… |
| P174 | 2661 | Proof | Use the total recursive isomorphism \[ b:\N\longrightarrow\N+\N,\qquad b(2n)=i_0(n),\quad b(2n+… |
| P175 | 2692 | Proof | The set $A$ is not recursive. Fix any index $a_*$. Choose an ordinary total recursive function … |
| P176 | 2716 | Proof | Finally, the arrows $i_1 1_A$ and $i_0 1_{A^c}$ belong to $\mathcal C_K$: they have the total r… |

## Final continuous reading of Version 7

The cuts preserve the progression from definitions to the general theorem, then the Miller, syntactic, arithmetic, and cosheaf applications. The introduction now states the criterion once with its hypotheses and keeps the principal Miller application prominent. Section openings proceed to their mathematical objects. The explanations retained between displays supply a reason, a type, a construction, or a distinction needed by the argument. No gap in the prose arose from the accepted cuts. The original outline remains appropriate, with the two proof-object subsections added above.

The final source also resolves notation and typing problems beyond the original prose recommendations: the free-semigroup extension uses `\widehat f`, avoiding conflict with functor-arrow notation; the pair object is explicitly `\omega\times\omega`; and the splitting-equivalence argument states its range-preservation check. These are local improvements to what the source says, not claims of a new independent proof audit.

### Added proof-object material

| Anchor | Function and definition order | Final finding |
| --- | --- | --- |
| B.3 `app:proof-initial`, opening through the definition of `\mathsf H` | Defines the tagged axiom object and its conclusion map, then the premise-matching pullback and its consequent map, then the endofunctor on the slice. | Every new object and map is introduced before its use. The pullback explains precisely what it means for two premise proofs to match modus ponens. |
| B.3 `prop:fork-proof-initial` and proof | States the algebra structure, its initiality equations, and the commuting square; proves existence and uniqueness by finite-tree recursion. | The slice carrier and algebra structure are distinguished. The explicit equations connect the diagram to proof evaluation. The componentwise recursion and naturality paragraphs have distinct mathematical functions. |
| B.3 final paragraph | Distinguishes the fibers of the proof map from the range of that map. | Retain it: distinct derivations of the same conclusion are elements of the proof object, while the range expresses existence of a derivation. This answers the user's proof-object question. |
| B.4 `app:first-order-proofs`, opening through `\mathsf H_T` | Specifies the two ambient total categories, the Hilbert calculus, formula and axiom carriers, rule-instance maps, matching-premise pullbacks, and induced endofunctor. | The order is coherent. The sentence assumption on nonlogical axioms explains why unrestricted generalization is legitimate. |
| B.4 `prop:first-order-proof-initial` and proof | Defines the root-adjoining algebra, gives initiality, selects sentence conclusions by pullback, and identifies the theorem range in the partial-map ambient. | The proposition makes the initial-algebra claim for all-formula derivations. It does not claim that the sentence-proof subobject is itself initial for that endofunctor. The domain check for `\mathcal E_a` is retained. |
| Introduction, §§4.3, 8, and 9 cross-references | Connect the applications' proof objects to the appendix characterizations. | The main applications now call their elements derivation trees and read their root conclusions; their terminology agrees with the appendix. |

The new portions consist of definitions and constructions, universal-property statements, proofs, and the final proof-object/range distinction. They introduce no process commentary or unsupported statement of significance. The explicit rule operations and two pullback diagrams answer the diagram/equation question without changing the incompleteness hypotheses. Their contribution is a characterization of the proof objects used in the applications; the report makes no independent priority claim for it.

### Issues raised during this review and their resolution

| Earlier wording or issue | Implemented repair, checked in final source |
| --- | --- |
| B.4 initially called the map `d_T:\mathsf{Der}_T\to\mathsf F` an initial algebra, conflating a slice object with its algebra structure. | The source now names `\delta_T:\mathsf H_T(\mathsf{Der}_T,d_T)\to(\mathsf{Der}_T,d_T)` and asserts initiality of this algebra. |
| The theorem-range sentence followed a construction in a total category without naming the partial ambient. | It now explicitly takes the range in `\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono})` or `\operatorname{Split}(\mathcal E_a)`, respectively. |
| §§4.3 and 8 retained “last/final sentence” terminology after changing from proof sequences to derivation trees. | Both passages now read the root conclusion. |
| B.3 “Both are morphisms” followed an intervening reference to the two children of a node. | The sentence now names the maps `\ell` and `m`. |

These were actual issues in intermediate v7 text and are now resolved. The original recommendations and inventory above should not be read as contradicting this final status. No further concrete editorial repair was identified on the final reading. This conclusion does not certify all existence, initiality, or computability claims independently of the mathematical reviews.

Production note: the parent agent reports that the final Version 7 compiles to 35 pages and is undergoing rendering. I did not perform that compilation or visual inspection. No Lean work was performed in this pass.
