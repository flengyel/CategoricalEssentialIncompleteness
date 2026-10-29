# Outline of *Deduction and essential incompleteness in recursion categories*

Version examined: 29 October 2026; repository commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. This outline describes the nine-page note in its existing order. Section and result numbers refer to that version.

The central question is how partial morphisms, ranges, and stable unions yield deductive closure, and under what additional representation hypothesis the resulting theories are essentially incomplete.

## 1. Domains and ranges

**Function:** establish the ambient partial-map structure and the direct- and inverse-image operations.

- Fix a locally small $P$-category $\mathscr R$ with restriction zeros and binary restriction products. State the composition convention, restriction identities, total maps, and product identities.
- Define the ordered set $\operatorname{Dom}(X)$ of restriction idempotents and the interval $E_q$ below a chosen domain.
- Describe recursion categories as the intended examples and state the Turing-morphism property.
- **Definition 1.1:** define range by its universal agreement property.
- **Lemma 1.2:** prove leastness, ranges of domains, range composition, and restriction of ranges.
- Define the covariant functor $E_!: \mathscr R\to\mathbf{Pos}$ by ranges of composites. Define inverse image $f^*(d)=\overline{df}$.
- Prove the partial-map relation $f_!(e)\le d\iff e\bar f\le f^*(d)$ and the adjunction $f_!\dashv f^*$ for total $f$.

## 2. Stable unions and inverse image

**Function:** prove the operations on domains needed for closure and separation.

- **Definition 2.1:** state Heller's universal definition of union and its stability under near products.
- **Lemma 2.2:** prove preservation of unions by multiplication by a fixed domain and by direct image; prove preservation of stable unions by total inverse image using a graph and its range.
- Assuming finite stable unions, obtain bounded distributive lattices of domains and define $E:\operatorname{Tot}(\mathscr R)^{\mathrm{op}}\to\mathbf{BDLat}$ by inverse image.
- **Lemma 2.3:** prove that finite near-product powers, with optional parameter factors, preserve stable unions of increasing chains.

## 3. Deductive closure and theories

**Function:** construct deductive closure and define theories as its fixed points.

- Choose $U$, a domain $q$, fixed axioms $\ell\le q$, and finitely many supported partial rule morphisms $r_i:P_i\boxtimes U^{\boxtimes n_i}\to U$ (or their unparameterized versions).
- Define the operation of a rule on a domain by $R_i(a)=\operatorname{ran}(r_i(1_{P_i}\boxtimes a^{\boxtimes n_i}))$.
- Form the increasing stages $a_0=\ell\vee a$ and $a_{k+1}=a_k\vee\bigvee_iR_i(a_k)$.
- **Theorem 3.1:** if each generated stage chain has a stable union, its union is the least rule-closed domain containing $\ell\vee a$ and defines an extensive, monotone, idempotent functor $c_q:E_q\to E_q$.
- For a selected domain $s\le q$, define and prove the closure property of $c_s(a)=s c_q(a)$.
- **Definition 3.2:** define $\mathsf{Th}_c$ as the full subposet of fixed points of $c_s$; an extension of $b$ is a fixed point $t$ with $b\le t$.
- Exhibit the reflector $L:E_s\to\mathsf{Th}_c$ left adjoint to the inclusion.

### 3.1. Morphisms of presentations

**Function:** organize these closures and their fixed points functorially.

- Define $\mathsf{Cons}$ in a fixed ambient $\mathscr R$. Its objects are presentations; its arrows are supported morphisms satisfying $c_s f^*\le f^*c_{s'}$.
- Check identities and composition.
- Define $\mathsf{Th},\mathcal E:\mathsf{Cons}^{\mathrm{op}}\to\mathbf{Pos}$ by inverse image, and the natural inclusion $i:\mathsf{Th}\Rightarrow\mathcal E$.
- Distinguish the inequality for closure from equality.

## 4. Representation and essential incompleteness

**Function:** introduce an additional representation hypothesis, derive inseparability, and exclude complete consistent extensions.

- Supply $\nu:U\to U$ with $\bar\nu=s$ and $s\nu=\nu$; put $t^-=\overline{t\nu}$.
- Define consistency by $t\wedge t^-=0_U$ and completeness by $t\vee t^-=s$.
- Define complementary pairs, relative complementary pairs, separators, and computational inseparability in the domain lattice.
- Supply total $\sigma:U\boxtimes U\to U$ with $s\sigma=\sigma$ and put $f_g=\sigma(g\boxtimes1_U)$ for total $g:U\to U$.
- **Definition 4.1:** require that each complementary pair $(e_+,e_-)$ on $U$ have a total $g$ satisfying $f_g^*b=\pi_2^*e_+$ and $f_g^*b^-=\pi_2^*e_-$.
- **Theorem 4.2:** in a nontrivial object, this representation condition implies computational inseparability of $b,b^-$. Pull a hypothetical separator back along $\delta=\sigma\Delta_U$, reverse its two components, represent the resulting pair, and use the square $f_g\langle1_U,g\rangle=\delta g$ to force $0_U=1_U$.
- **Theorem 4.3:** a complete consistent closed extension $t\ge b$ would itself separate $b,b^-$; hence every consistent closed extension is incomplete.
- Prove that representation is inherited by consistent extensions using distributivity and complementary lower bounds.

## 5. The arithmetic realization

**Function:** interpret the categorical data in partial recursive maps and verify the required unions.

- Define $\mathscr R_{\mathrm{rec}}$ with objects $\mathbb N^k$ for $k\ge1$ and partial recursive maps, equal as partial functions. Identify its near products, recursive pairing, and universal evaluator.
- Identify restriction idempotents with partial identities on c.e. sets, and ranges with partial identities on images.
- **Proposition 5.1:** a uniformly c.e. family has a stable union, obtained as the range of a projection restricted to the family relation.
- Give a counterexample to existence of unions for arbitrary increasing countable families of c.e. domains.

### 5.1. Effective deduction

**Function:** identify the constructed closure with ordinary arithmetical derivability.

- Choose effective formula and sentence coding, the corresponding domains $q,s$, and a Hilbert calculus with recursive logical axiom instances.
- Realize modus ponens and parameterized generalization as partial recursive rule morphisms; take nonlogical axioms to be sentences.
- Prove uniform c.e. enumerability of the generated stages by recursive index transformation and iteration.
- Use finite proof-tree height to identify $c_s(1_A)$ with the partial identity on sentence consequences of a c.e. axiom set $A$.
- Identify fixed points with c.e. deductively closed sentence theories, including the theorem sets of $Q$, PA, and their c.e. extensions.

### 5.2. Representation and arbitrary base theories

**Function:** connect the representation condition with strong numeralwise definability and obtain the arithmetic corollary.

- Realize $\nu$ by syntactic negation on sentence codes.
- Enumerate one-variable formulas and construct a jointly total recursive numeral-substitution morphism $\sigma(u,n)$.
- Define strong numeralwise definability by positive and negative provability for members and nonmembers, respectively.
- Identify complementary c.e. pairs with recursive sets and their complements. Under consistency, use constant representatives $g(x)=u$ to obtain the exact equations of Definition 4.1.
- **Corollary 5.2:** if a consistent arithmetic base $B$ strongly defines every recursive set numeralwise, every consistent c.e. extension $T$ is incomplete, with no enumerability assumption on $B$. Transfer the numeralwise definitions from $B$ to $T$, represent the theorem domain of $T$, and apply Theorem 4.3 with both categorical base and extension equal to that domain.

## Main dependencies and supplied data

| Result or construction | Required inputs | Role in later argument |
|---|---|---|
| Domain functor $E$ | Restriction products, ranges, finite stable unions | Supplies distributive domain lattices and inverse image preserving finite lattice operations along total maps. |
| Closure $c_q,c_s$ (Theorem 3.1) | Supported finite-arity rules and stable unions of their generated chains | Produces the class of closed domains called theories. |
| $\mathsf{Cons}$ and $\mathsf{Th}$ (§3.1) | Presentations and closure-continuous supported morphisms | Organizes theory domains and inverse image; the proofs in §4 take place in one fixed presentation. |
| Inseparability (Theorem 4.2) | Nontrivial $U$, $\nu$, total $\sigma$, consistency, and Definition 4.1 | Excludes complementary separators. The proof uses inverse image, products, and the representation equations. |
| Essential incompleteness (Theorem 4.3) | Theorem 4.2 and $b\le t$ with $t$ closed and consistent | A complete $t$ would give a forbidden separator. |
| Arithmetic corollary (Corollary 5.2) | Effective syntax and deduction, joint recursive substitution, and strong numeralwise definability in $B$ | Produces a categorical instance for each consistent c.e. extension $T$. |

The note states the existence of a Turing morphism when describing recursion categories; its proofs do not derive Definition 4.1 from that morphism. The data $q,s,\ell,r_i,\nu,\sigma$ are supplied to the abstract construction. The note contains no separate construction named a definability algebra and no claim of Kelly enrichment. Its arithmetic section verifies a conditional representation statement; it does not prove the representability theorem for $Q$ or PA.
