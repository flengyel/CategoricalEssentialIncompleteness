# Version 12: theorems and proof outlines

This report distills *Local connectedness in recursion categories and essential incompleteness*, version 12, dated 31 October 2026, at manuscript commit `cceacb7725c0dd057caeff0579e90afb3f7ae00c`. It accompanies the [continuation prompt for the introduction review](../CONTINUATION_INTRODUCTION_REVIEW.md). The author has accepted this version's abstract.

The report covers all 34 numbered lemmas, propositions, theorems, and corollaries, together with the unnumbered constructions needed to understand their relation. It records typed data, conclusions, proof outlines, and dependencies. Detailed functor assignments and full proofs remain in the cited manuscript files. Results invoked from the literature are identified separately from arguments supplied by the paper. This report does not replace reading the manuscript or constitute Lean verification.

## The argument and its branches

Theorem 3.3 constructs an inseparable pair in a source recursion category by using a range functor and lifting specified sections from a locally connected target. Corollary 3.5 states the algebraic implication used for incompleteness. The logical constructions supply theories, their deductively closed theorem sets, and reductions from the inseparable pair. A complete consistent extension in the relevant computability class would give a separator, contradicting that pair's inseparability.

| Branch | What is established | Essential additional input |
|---|---|---|
| Miller, §4 | A recursion category, a failure of preservation of inseparability, and a consistent real-closed-field theory with the stated incompleteness property. | Compactness of the representation set, Miller's index property, the reduction to the two cut-index sets, and uniform semidecidability from all representations. |
| Syntactic categories, §§5–7 | Inseparability in $S_T$, a faithful family of model functors, and compatibility with theory extension. | PA-provable computation identities, model interpretation, completeness, and section lifts. This conclusion is about the category, not incompleteness of the external theory $T$. |
| Arithmetic, §8 | Recursive inseparability of theorem and refutation sets for every consistent c.e. extension of PA. | The numerical recursion category, finite computation proofs, and c.e. finite derivations. |
| Cosheaves, §9 | A recursion category distinct from the category of partial recursive functions; compatible propositional theories; essential incompleteness of the two endpoint theories. | The structure in Appendix A, the syntax and derivation algebras in Appendix B, and endpoint evaluation. |
| Counterexample, Appendix C | The lifting hypothesis of Theorem 3.3 cannot be omitted. | Partial functions with oracle-enumerable domains and ordinary partial recursive extensions. |

The source of Theorem 3.3 already has a Turing morphism. Using Corollary 3.5 to prove incompleteness requires separately specified logical data; the corollary does not construct a theory from every restriction idempotent. The distinction matters in $S_T$: when $T$ is the complete theory of the standard natural numbers, $S_T$ still has inseparable pairs. The logical incompleteness arguments instead use the reductions and computability assumptions established in §§4, 8, and 9.

## Source files

| Results | Source |
|---|---|
| Definitions | [§2](../manuscript/local_connectedness/sections/02-categorical-preliminaries.tex) |
| 3.1–3.5 | [§3](../manuscript/local_connectedness/sections/03-sections-and-inseparability.tex) |
| 4.1–4.5 | [§4](../manuscript/local_connectedness/sections/04-miller-sequences.tex) |
| 5.1, 6.1, 7.1–7.3 | [§5](../manuscript/local_connectedness/sections/05-syntactic-recursion-category.tex), [§6](../manuscript/local_connectedness/sections/06-interpretation-in-models.tex), [§7](../manuscript/local_connectedness/sections/07-faithful-family-and-theory-extension.tex) |
| 8.1 | [§8](../manuscript/local_connectedness/sections/08-essential-incompleteness-of-arithmetic.tex) |
| 9.1–9.3 | [§9](../manuscript/local_connectedness/sections/09-three-point-space.tex) |
| A.1–A.10 | [Appendix A](../manuscript/local_connectedness/appendices/a-three-point-cosheaves.tex) |
| B.1–B.4 | [Appendix B](../manuscript/local_connectedness/appendices/b-finite-syntax-and-proofs.tex) |
| C.1 | [Appendix C](../manuscript/local_connectedness/appendices/c-section-lifting.tex) |

## Common categorical notation

Composition is $gf=g\circ f$. For a morphism $f:X\rightharpoonup Y$, its restriction idempotent is $\bar f:X\rightharpoonup X$, and $f$ is total when $\bar f=1_X$. For a restriction idempotent $a$ on $Y$, put $f^*a=\overline{af}$. Restriction idempotents satisfy $a\le b$ when $ba=a$; their meet is composition. Disjoint $a,b$ satisfy $ab=0$, and they are complementary if also $a\vee b=1$. A disjoint pair is inseparable when it has no enlargement to a complementary pair.

A range functor preserves restrictions, ranges, restriction zeros, and binary restriction coproducts. It therefore preserves binary joins of restriction idempotents. For a range functor $F:\mathcal C\to\mathcal D$ and objects $X,Y$ of $\mathcal C$, write $\chi_{X,Y}:FX+FY\to F(X+Y)$ for the canonical coproduct isomorphism.

The source recursion categories are prodominical and isotypical, have binary restriction products, and have a Turing morphism $\tau:U\times U\rightharpoonup U$: for every object $X$ and morphism $f:X\times U\rightharpoonup U$, there is a total $r:X\to U$ with $f=\tau(r\times1_U)$.

## §3. From sections to inseparability and incompleteness

### Lemma 3.1 — `lem:connected-alternative`

**Statement.** Let $\mathcal A$ have ranges, restriction zeros and binary restriction coproducts, and suppose inverse images preserve binary joins of restriction idempotents. If $a$ is a connected restriction idempotent on $X$ and $f:X\to Y+Z$ is total, then $\varepsilon_0fa=fa$ or $\varepsilon_1fa=fa$, where $\varepsilon_0=1_Y+0_Z$ and $\varepsilon_1=0_Y+1_Z$.

**Proof.** The summand idempotents are disjoint and cover $Y+Z$. Pulling them back and restricting to $a$ gives
$$
a=af^*\varepsilon_0\vee af^*\varepsilon_1.
$$
Connectedness makes one summand zero. The other equals $a$, and the restriction identity yields the asserted factorization through a summand.

### Proposition 3.2 — `prop:local-switch`

**Statement.** Suppose $\mathcal A$ is split and locally connected, has ranges, restriction zeros and binary restriction coproducts, satisfies weak choice, and has inverse images preserving binary joins. For disjoint restriction idempotents $a,b$ on $X$,
$$
p=\nabla_X(a+b):X+X\rightharpoonup X
$$
is a partial monomorphism with a unique section $s:X\rightharpoonup X+X$, and $ps=\bar s=a\vee b$. For complementary $c,c'$, the section of $\nabla_X(c'+c)$ is total and satisfies $sc=i_1c$, $sc'=i_0c'$.

**Proof.** First test partial monicity on total morphisms into $X+X$. Lemma 3.1 assigns each connected domain to a summand; equality after $p$, together with $ab=0$, then gives equality after $\bar p=a+b$. Local connectedness detects equality. For arbitrary partial morphisms $u,v$ with $pu=pv$, split their common composite domain and reduce to the total case. Weak choice supplies a section. Its defining equations imply $\bar s=\operatorname{ran}(p)=a\vee b$; partial monicity proves uniqueness and the two switching equations.

### Theorem 3.3, Range-functor lifting — `thm:local-lifting`

**Statement.** Let $\mathscr R$ be a recursion category with ranges and binary restriction coproducts. Let $\mathcal A$ satisfy all the hypotheses of Proposition 3.2, and let $F:\mathscr R\to\mathcal A$ be a range functor. Fix a Turing morphism $\tau:U\times U\rightharpoonup U$, an isomorphism $b:U\to U+U$, and assume $F(1_U)\ne0$. For every complementary pair $c,c'$ on $U$, let $s_c:FU\to FU+FU$ be the section of $\nabla_{FU}(Fc'+Fc)$. Assume there is $\ell_c:U\rightharpoonup U+U$ with
$$
F\ell_c=\chi_{U,U}s_c.
$$
Then the restriction idempotents
$$
a_0=(b\tau\Delta_U)^*(1_U+0_U),\qquad
a_1=(b\tau\Delta_U)^*(0_U+1_U)
$$
are inseparable in $\mathscr R$.

**Proof.** Suppose $c,c'$ separate $a_0,a_1$. Put $u=b^{-1}\ell_c$. The Turing property gives a total $g:U\to U$ with $\tau(g\times1_U)=u\pi_2$; precomposition with $\langle1_U,g\rangle$ yields $\tau\Delta_Ug=ug$. After applying $F$, this identifies the diagonal computation with the section that exchanges the two complementary domains. If $E=Fg$, $\Gamma=Fc$, and $\Gamma'=Fc'$, the separator inequalities force $E^*\Gamma=E^*\Gamma'$. These idempotents have meet zero and, by totality and join preservation, join $1_{FU}$. This contradicts $F(1_U)\ne0$.

**Qualifications.** Faithfulness and preservation of restriction products are not hypotheses. The target is a restriction category with the stated structure; it need not be a recursion category. The lifting assumption is essential, as Proposition C.1 shows.

### Proposition 3.4 — `prop:disjoint-joins`

**Statement.** Let $\mathcal C$ have restriction zeros and binary restriction coproducts. Suppose parallel morphisms with disjoint restriction idempotents have joins in the restriction order. For complementary $c,c'$ on $X$,
$$
\ell_c=(i_1c)\vee(i_0c'):X\rightharpoonup X+X
$$
is total and satisfies $\ell_cc=i_1c$, $\ell_cc'=i_0c'$. For a range functor $F:\mathcal C\to\mathcal A$ into a target satisfying Proposition 3.2, $\chi_{X,X}^{-1}F\ell_c$ is the required section.

**Proof.** The join's upper-bound equations give the two restrictions. Since its restriction contains $c\vee c'=1_X$, it is total. Its image agrees with the section of Proposition 3.2 after both $Fc$ and $Fc'$. Their copairing has range $1_{FX}$, so the range agreement law gives equality.

### Corollary 3.5 — `cor:domain-incompleteness`

**Statement.** Let $\mathcal C$ have restriction zeros and binary joins of restriction idempotents preserved by inverse image along total morphisms. Let $a,b$ be inseparable restriction idempotents on $U$, let $\theta:U\to S$ and $\nu:S\to S$ be total, and suppose a restriction idempotent $t_0$ on $S$ satisfies
$$
a\le\theta^*t_0,\qquad b\le\theta^*\nu^*t_0.
$$
For every restriction idempotent $t\ge t_0$ with $t\nu^*t=0_S$, the pair $t,\nu^*t$ is inseparable. In particular, $t\vee\nu^*t\ne1_S$.

**Proof.** A complementary pair $e,e'$ separating $t,\nu^*t$ would pull back along $\theta$ to a complementary pair separating $a,b$. Preservation of meets, zero and joins, and totality of $\theta$, give complementarity. Monotonicity gives the separator inequalities. If $t\vee\nu^*t=1_S$, the disjoint pair $t,\nu^*t$ would itself be a separator.

**Logical use.** The corollary is an algebraic statement about specified morphisms and restriction idempotents. In §§4, 8 and 9, the manuscript separately constructs theories or compatible families of theories, identifies their deductively closed theorem sets, and takes partial identities on those sets. Then extension gives $t_0\le t$, consistency gives $t\nu^*t=0$, and completeness would give $t\vee\nu^*t=1$. These identifications require the concrete syntax, proof construction and computability hypotheses. They do not identify an arbitrary restriction idempotent with a theory. Inseparability on an original object is unchanged by the fully faithful inclusion into the category obtained by splitting restriction idempotents.

## §4. Miller sequences and essential incompleteness

### Fixed data and cited existence result

Fix a recursive pairing $\langle-,-\rangle:\mathbb N^2\to\mathbb N$, an acceptable enumeration $(\Phi_e^p)$ of partial numerical oracle computations, and a recursive enumeration $(q_j)$ of the rationals. Put $Q=[0,1]^{\mathbb N}$ and
$$
\rho:2^{\mathbb N}\to Q,
\qquad
\rho(p)(n)=\sum_{j\geq0}p(\langle n,j\rangle)2^{-j-1},
\qquad
P_z=\rho^{-1}(\{z\}).
$$
Every $P_z$ is nonempty and compact. A Miller sequence $a\in Q$ has the following index property: if $\Phi_d^p$ is total for every $p\in P_a$ and
$$
|q_{\Phi_d^p(k)}-r|<2^{-k}
\quad\text{for all }p\in P_a, k\in\mathbb N,
$$
for one $r\in[0,1]$, then $a(d)=r$. The rational approximations may vary with $p$; the real $r$ is fixed. Existence is cited from Miller, Theorem 6.3 and its following paragraph; Bauer–Hanson, §2.1 and Theorem 2.2, give the binary-representation formulation used here. The manuscript does not reprove this existence theorem.

### Lemma 4.1 — computation uniform over a representation set — `lem:miller-unanimity`

**Data and hypotheses.** For each $z\in Q$, define $\tau_z:\mathbb N^2\rightharpoonup\mathbb N$ by
$$
\tau_z(e,n)=m
\quad\Longleftrightarrow\quad
(\forall q\in P_z)\;\Phi_e^q(n)\mathord\downarrow=m.
$$

**Conclusion.** One oracle computation, with numerical inputs $e,n$ and any oracle $p\in P_z$, computes exactly $\tau_z$. Its values and domain of definition are independent of the chosen $p$.

**Proof mechanism.** For a finite binary sequence $\sigma$, the image $\rho([\sigma])$ is an effectively specified finite union of closed dyadic boxes. From $p$, enumerate the cylinders with $z\notin\rho([\sigma])$; their union is $2^{\mathbb N}\setminus P_z$. Halting computations enumerate
$H_{e,n,m}=\{q:\Phi_e^q(n)\downarrow=m\}$.
Search, in parallel over $m$, for a finite cover of Cantor space by cylinders from these two open sets. Compactness makes success equivalent to $P_z\subseteq H_{e,n,m}$. Nonemptiness of $P_z$ makes the successful output unique.

**Dependencies and scope.** Uses compactness, effective cylinder operations, and semidecidability of strict rational inequalities. The Miller index property is not used: the lemma holds for every $z\in Q$.

### Proposition 4.2 — the recursion category $\mathcal E_a$ — `prop:miller-category`

**Data and hypotheses.** Objects are those generated from $\mathbb N$ by binary Cartesian products and tagged disjoint unions, with fixed recursive codings. A morphism $f:X\rightharpoonup Y$ is a partial function computed by one oracle computation with exactly the same values and domain for every $p\in P_a$. Equality is equality of partial functions.

**Conclusion.** $\mathcal E_a$ is a locally connected recursion category with ranges, binary restriction coproducts, finite compatible joins, and weak choice. Its Turing morphism is $\tau_a:\mathbb N\times\mathbb N\rightharpoonup\mathbb N$.

**Proof mechanism.** Recursive operations supply composition, products, coproducts, and restrictions. Dovetailing supplies range partial identities and compatible joins; the returned value and definedness are independent of the representation. Singleton partial identities are connected and detect distinct morphisms. An injective morphism has a computable partial inverse by preimage search, proving weak choice. Lemma 4.1 supplies $\tau_a$. For every $f:X\times\mathbb N\rightharpoonup\mathbb N$, the oracle parameter theorem supplies a total recursive $c:X\to\mathbb N$ with
$$
f=\tau_a(c\times1_{\mathbb N}).
$$
The recursive codings make the category isotypical.

**Dependencies and scope.** Uses Lemma 4.1 and the parameter theorem. This category construction also works with any $z\in Q$ in place of $a$; the Miller property enters the cut reduction below.

### Categorical inseparability used in §4

For $p\in P_a$, the identity interpretation of partial functions defines
$$
J_p:\mathcal E_a\to\mathrm{Rec}^p,
\qquad
I_p:\mathrm{Rec}^p\to\mathcal K_p
       =\operatorname{Split}(\mathrm{Rec}^p).
$$
Here $\mathrm{Rec}^p$ has the same numerical objects and all partial $p$-recursive functions; $I_p$ is the full inclusion into the restriction splitting. The category $\mathcal K_p$, presented by $p$-c.e. carriers and partial $p$-recursive functions, satisfies the target hypotheses of Theorem 3.3. Complementary source domains $c,c'$ admit the total switching morphism
$\ell_c=(i_1c)\vee(i_0c'):X\to X+X$.
Thus $I_pJ_p$ satisfies the lifting hypothesis of Theorem 3.3. That theorem makes the partial identities on
$$
A_i=\{e:\tau_a(e,e)\downarrow=m
              \text{ for some }m\equiv i\pmod2\},
\qquad i=0,1,
$$
inseparable in $\mathcal E_a$.

### Lemma 4.3 — reduction to the two cut-index sets — `lem:miller-cut-reduction`

**Data and hypotheses.** Let $a$ have the Miller index property and set
$$
L_a=\{n:a(n)<1/2\},\qquad R_a=\{n:a(n)>1/2\}.
$$

**Conclusion.** There is a total recursive $h:\mathbb N\to\mathbb N$ such that
$h^{-1}(L_a)=A_0$ and $h^{-1}(R_a)=A_1$.

**Proof mechanism.** Finite halting-cylinder approximations show that
$$
U_e^i=\{z:\tau_z(e,e)\downarrow=m
              \text{ for some }m\equiv i\pmod2\}
$$
are disjoint effectively open subsets of $Q$. Weighted sums of distances to effectively specified finite unions of closed boxes give computable continuous functions $g_e^i:Q\to[0,1]$ positive exactly on $U_e^i$. Consequently
$$
r_e(z)=\frac12+\frac{g_e^1(z)-g_e^0(z)}4
$$
is below, respectively above, $1/2$ exactly on $U_e^0$, respectively $U_e^1$. The parameter theorem produces an index $h(e)$ for approximations to $r_e(\rho(p))$. The Miller property gives $a(h(e))=r_e(a)$, proving both inverse-image equalities.

**Dependencies and scope.** Uses Lemma 4.1's definition, effective compactness calculations, the parameter theorem, and the Miller index property. The reduction itself does not use inseparability; Theorem 3.3 supplies inseparability of its source pair.

### Corollary 4.4 — inseparability and representation-dependent separators — `cor:miller-cuts-inseparable`

**Data and hypotheses.** Use $a,L_a,R_a$ and $\mathcal E_a$ above. Strict inequalities make $1_{L_a},1_{R_a}:\mathbb N\rightharpoonup\mathbb N$ morphisms of $\mathcal E_a$.

**Conclusion.** These restriction idempotents are inseparable in $\mathcal E_a$. For every fixed $p\in P_a$, however,
$$
C_p=\{n:p(\langle n,0\rangle)=0\}
$$
is a $p$-decidable separator of the underlying sets $L_a,R_a$.

**Proof mechanism.** A complementary separating pair in $\mathcal E_a$ would pull back along $h$ to one separating $A_0,A_1$. This contradicts Theorem 3.3. Reading the first binary digit proves the separator assertion. At coordinates equal to $1/2$, the permitted choice of expansion permits the decided set to vary with the representation.

**Dependencies and scope.** Uses Lemma 4.3 and the preceding application of Theorem 3.3. A single computation produces a separator from each representation, but it does not compute one fixed separating set from all representations.

### The functors $J_p$ do not preserve this inseparable pair or the chosen Turing morphism

**Data and hypotheses.** Fix $p\in P_a$. The functor $J_p:\mathcal E_a\to\mathrm{Rec}^p$ is faithful and preserves restrictions, ranges, restriction zeros, binary restriction coproducts, restriction products, and finite compatible joins.

**Conclusion.** The images of $1_{L_a},1_{R_a}$ are separable in $\mathrm{Rec}^p$, and $J_p(\tau_a)$ is not a Turing morphism there. The target nevertheless has a Turing morphism for partial $p$-recursive functions.

**Proof mechanism.** The set $C_p$ gives the first conclusion. If $J_p(\tau_a)$ were a Turing morphism, Theorem 3.3 applied to $I_p$ and the $p$-recursive switching morphisms would make $1_{A_0},1_{A_1}$ inseparable in $\mathrm{Rec}^p$. Their $p$-decidable separator $h^{-1}(C_p)$ contradicts this.

**Dependencies and scope.** Uses Theorem 3.3, Lemma 4.3, and Corollary 4.4. The assertion concerns preservation of a specified Turing morphism, not existence of some Turing morphism in the target.

### Theorem 4.5 — essential incompleteness of the real-closed-field theory — `thm:miller-incompleteness`

**Data and hypotheses.** In the language of ordered fields with constants $(c_n)_{n\in\mathbb N}$, let $T_a$ have a recursive axiomatization of real closed ordered fields and the axioms
$$
q<c_n\quad(q<a(n)),\qquad c_n<q\quad(a(n)<q),
\qquad q\in\mathbb Q, n\in\mathbb N.
$$
Its model $(\mathbb R,(a(n))_n)$ proves consistency. Its axiom set is $\mathcal E_a$-semidecidable, meaning that its partial identity belongs to $\mathcal E_a$. Let $T\supseteq T_a$ be consistent with an $\mathcal E_a$-semidecidable axiom set.

**Conclusion.** The partial identities on the theorem and refutation sets of $T$ are inseparable in $\operatorname{Split}(\mathcal E_a)$. In particular, $T$ is incomplete.

**Proof mechanism.** The recursive set $S$ of sentence codes and the $\mathcal E_a$-semidecidable set $\mathrm{Prf}_T$ of finite derivations with sentence conclusions are objects of the splitting. The conclusion map $c_T:\mathrm{Prf}_T\to S$ is total; its range $t_T$ is the partial identity on the theorem set. Negation $\nu:S\to S$ makes $\nu^*t_T$ the partial identity on the refutation set. For
$$
\theta:\mathbb N\to S,
\qquad\theta(n)=\ulcorner c_n<1/2\urcorner,
$$
the axioms yield
$$
1_{L_a}\leq\theta^*t_{T_a},\qquad
1_{R_a}\leq\theta^*\nu^*t_{T_a}.
$$
The full inclusion into the splitting retains inseparability of $1_{L_a},1_{R_a}$. Extension gives $t_{T_a}\leq t_T$, and consistency gives $t_T\nu^*t_T=0$. Corollary 3.5 therefore gives inseparability of $t_T,\nu^*t_T$, hence $t_T\vee\nu^*t_T\ne1_S$.

**Dependencies and scope.** Uses Corollaries 4.4 and 3.5. Proposition B.4 characterizes the finite derivation construction by an initial algebra followed by restriction to sentence conclusions. The extension class is exactly the one stated: one oracle computation must semidecide the same axiom set from every binary representation of $a$. Ordinary consistency and deductive closure belong to the theories; their theorem sets then determine partial identities. An arbitrary restriction idempotent is not asserted to define a theory.

### Source relationships

- Joseph S. Miller, *Degrees of unsolvability of continuous functions*, J. Symbolic Logic 69 (2004), 555–584, Theorem 6.3 and the following paragraph: the sequence existence and index property. [Author manuscript](https://people.math.wisc.edu/~jsmiller8/Papers/continuous.pdf).
- Andrej Bauer and James E. Hanson, *The Countable Reals*, arXiv:2404.01256v3, §2.1 and Theorem 2.2: the binary-representation formulation of Miller's sequence. Their use of the sequence is in parameterized realizability. [Version 3](https://arxiv.org/html/2404.01256v3).
- Section 4 supplies the recursion-category construction, the reduction to $L_a,R_a$, the functor counterexample, and the incompleteness theorem summarized above. These are descriptions of the manuscript's content, not claims of priority.

## §§5–7. Syntactic recursion categories and model interpretation

### Lemma 5.1 — `lem:arithmetized-evaluation`

**Statement.** For the chosen deterministic computation coding, let $G(e,x,y)$ be the $\Sigma_1$ graph formula. There are $u\in\mathbb N$ and primitive-recursive functions $\operatorname{s},\operatorname{comp}:\mathbb N^2\to\mathbb N$ such that PA proves functionality of $G$ and the universal closures of
$$
\begin{aligned}
G_u(\langle e,x\rangle,y)&\leftrightarrow G(e,x,y),\\
G(\operatorname{s}(e,a),x,y)&\leftrightarrow G(e,\langle a,x\rangle,y),\\
G(\operatorname{comp}(f,e),x,z)&\leftrightarrow
\exists y\,[G(e,x,y)\land G(f,y,z)].
\end{aligned}
$$
For every fixed $e$, there is an index $k_e$ whose PA-provable graph is $p=\operatorname{s}(e,a)$; PA proves that this graph defines a total function.

**Proof and dependency.** The manuscript invokes Montagna's formalized enumeration, composition and parameterization properties. PA-provable coding bijections transfer them to the chosen pairing. An index for the primitive-recursive specialization function gives $k_e$. The manuscript does not reprove the trace-coding results.

### Construction of $S_T$ following Lemma 5.1

Fix a consistent extension $T\supseteq\mathrm{PA}$. The objects are formal terms generated by $\omega$, binary product and binary coproduct. Each term $X$ has a numerical carrier $|X|$ and a specified recursive bijection $\gamma_X:|X|\to\mathbb N$. Every hom-set is a quotient of $\mathcal I(X,Y)=\mathbb N$, with
$$
e\equiv_T f\quad\Longleftrightarrow\quad
T\vdash\forall x\forall y\,[G_e(x,y)\leftrightarrow G_f(x,y)].
$$
Composition is induced by $\operatorname{comp}$. The PA-provable graph equations prove independence of representatives, identity and associativity. For a $\Sigma_1$ predicate $C$, witness search gives a partial identity $[C]_T$, and
$$
[C]_T\le[D]_T\quad\Longleftrightarrow\quad
T\vdash\forall x\,[C(x)\to D(x)].
$$
Restrictions and ranges of $[e]_T$ are represented by $\exists y\,G_e(x,y)$ and $R_e(y)=\exists x\,G_e(x,y)$, respectively. To prove range agreement, equality of composite graphs is restricted to $R_e$; functionality of $G_e$ identifies their intermediate output. Pairing and tagged copairing give restriction products and coproducts. Lemma 5.1 supplies the Turing morphism $\tau_T=[u]_T$ and total parameter maps $[k_e]_T$. Recursive coding bijections give isotypicality, and product with zero is zero. Thus $S_T$ is a prodominical recursion category with ranges and binary restriction coproducts.

The functor $\Pi_T:S_T\to S_T^{\mathrm{set}}$, $X\mapsto|X|$, $[e]_T\mapsto[e]_T^{\mathrm{set}}$, is an equivalence with the indicated unprimed Montagna–Di Paola–Montagna presentation: it is essentially surjective and bijective on each hom-set. The comparison uses the same graph formulas and numerical codings. The primed, pointwise-provability systems are excluded by the separately cited composition-failure result.

### Proposition 6.1 — `prop:model`

**Statement.** For every model $M\models T$, interpret each object term as a set $X_M$, using $|M|$ for $\omega$, Cartesian products and tagged coproducts. The PA-provable coding identities induce bijections $\gamma_X^M:X_M\to|M|$. Define
$$
F_M(X)=X_M,\qquad
F_M([e]_T)(x)=y
\Longleftrightarrow
M\models G_e(\gamma_X^M(x),\gamma_Y^M(y)).
$$
This is a covariant functor $F_M:S_T\to\mathbf{Pfn}$, preserving restrictions, zeros, ranges, binary restriction products and coproducts, and finite joins of restriction idempotents.

**Proof.** PA-provable functionality gives partial functions, and $T$-provable graph equivalence gives independence of representatives. The interpreted composition equation and coding bijections prove the functor laws. Existential quantification gives domains and images; conjunction, disjunction and false predicates give meets, joins and zeros. The graph equations for pairing and tagging give products and coproducts.

**Qualification.** The index $e$ is standard and is interpreted as its numeral. Quantified traces and intermediate values range over the entire model, including nonstandard elements.

### Theorem 7.1 — `thm:faithful`

**Statement.** Let $\mathcal M_T$ be the set of arithmetic structures with carrier $\mathbb N$ satisfying $T$, and put $\mathcal D_T=\prod_{M\in\mathcal M_T}\mathbf{Pfn}$. The functor
$$
F_T:S_T\to\mathcal D_T,\qquad
F_T(X)=(X_M)_M,\quad F_T([e]_T)=(F_M[e]_T)_M
$$
is faithful and preserves the operations listed in Proposition 6.1. The target is split and locally connected, satisfies weak choice, and has inverse images preserving binary joins. Moreover, $F_T(1_\omega)\ne0$.

**Proof.** Completeness and downward Löwenheim–Skolem give a countable model of $T$, transported to the carrier $\mathbb N$. If two source morphisms are unequal, the negation of their uniform graph-equality sentence is consistent with $T$; a model with carrier $\mathbb N$ separates their interpretations. All preservation properties are coordinatewise. Subsets split restriction idempotents. Partial identities on one singleton at one coordinate, zero elsewhere, are connected and detect every morphism. Testing partial monicity on one-coordinate singleton objects shows that coordinate functions are injective; their partial inverses give weak choice. Inverse images preserve unions coordinatewise.

### Theory extension following Theorem 7.1

For consistent $T\subseteq T'$, the quotient functor
$$
Q_{T,T'}:S_T\to S_{T'},\qquad X\mapsto X,\quad[e]_T\mapsto[e]_{T'}
$$
preserves the displayed categorical operations and the chosen Turing morphism. Restriction of families defines $\pi_{T,T'}:\mathcal D_T\to\mathcal D_{T'}$, and
$$
\pi_{T,T'}F_T=F_{T'}Q_{T,T'}.
$$
This equality holds on objects and morphisms because both sides interpret the same graph formula in the same models. Identity and composition laws for theory inclusions follow directly.

### Lemma 7.2 — `lem:switch`

**Statement.** For complementary restriction idempotents $c,c'$ on $X$ in $S_T$, there is a total $s:X\to X+X$ with $sc=i_1c$, $sc'=i_0c'$. Under the coproduct identification, $F_Ts$ is the unique section required by Proposition 3.2.

**Proof.** Choose $\Sigma_1$ representatives $C,C'$. Their disjointness and coverage are provable in $T$. Search simultaneously for witnesses and output the tag selected by the first successful search. PA verifies halting exactly on $C\lor C'$; under disjointness it verifies the exact graph. Thus $T$ proves totality and the switching equations. Interpretation in each model gives the inverse of the partial injection $\nabla(F_Mc'+F_Mc)$.

### Corollary 7.3 — `cor:pair`

**Statement.** For every consistent $T\supseteq\mathrm{PA}$, $F_T$ satisfies the lifting hypothesis of Theorem 3.3. Fix $U=\omega$, a Turing morphism $\tau:U\times U\rightharpoonup U$ in $S_T$, and an isomorphism $b=Q_{\mathrm{PA},T}(b_0):U\to U+U$ obtained from $S_{\mathrm{PA}}$. The two summand inverse images under $b\tau\Delta_U$ are inseparable. Their images under every consistent theory-extension functor $Q_{T,T'}$ are the pair defined in the same way in $S_{T'}$, and remain inseparable.

**Proof.** Theorem 7.1 and Lemma 7.2 verify Theorem 3.3. The quotient functor preserves the pair's defining operations. It is identity on objects and surjective on hom-sets, so a Turing factorization of a preimage yields a factorization of every target morphism. Hence the image of any specified Turing morphism remains a Turing morphism, and Theorem 3.3 applies over $T'$.

**Qualifications.** These results do not require $T$ to be c.e.; the cited failure of local connectedness is stated for consistent c.e. extensions. The model functor does not preserve the Turing property: a fixed countable model supplies only countably many functions obtained by parameters in its carrier, whereas its partial-function category contains uncountably many. Also, every disjoint pair in the target restriction lattice has a separator, since those lattices are Boolean. Lifting the specified sections does not imply that arbitrary target separators lift.

## §8. Essential incompleteness of arithmetic

### Corollary 8.1 — `cor:arithmetic`

**Statement.** The theorem and refutation sets of every consistent computably enumerable extension $T\supseteq\mathrm{PA}$ are recursively inseparable. Consequently every such extension is incomplete.

**Construction and proof.** Let $\mathrm{Rec}$ have the object terms of §5 and their ordinary partial recursive functions as morphisms, with extensional equality. Its restriction idempotents are partial identities on c.e. subsets; complementary ones correspond to recursive subsets. The inclusion $J_{\mathrm{rec}}:\mathrm{Rec}\to\mathbf{Pfn}$ is a range functor. A recursive partition gives a total recursive switching map, so the lifting hypothesis holds.

Let $d=\tau_{\mathrm{rec}}\Delta_\omega$. Its even-output and odd-output sets
$$
A=\{n:d(n)\downarrow\text{ is even}\},\qquad
B=\{n:d(n)\downarrow\text{ is odd}\}
$$
are recursively inseparable by Theorem 3.3. Let $\alpha(x),\beta(x)$ be their $\Sigma_1$ graph formulas. For each $n\in A$ or $n\in B$, the finite halting computation gives a PA-proof of the corresponding numeral instance. PA-provable functionality gives $\mathrm{PA}\vdash\forall x\,\neg(\alpha(x)\land\beta(x))$.

In $\operatorname{Split}(\mathrm{Rec})$, let $S$ be the recursive set of arithmetic sentence codes, $\nu:S\to S$ negation, and $\theta:\mathbb N\to S$, $\theta(n)=\ulcorner\alpha(\bar n)\urcorner$. The c.e. set of finite derivations from $T$ has a total conclusion map $c_T:\mathrm{Prf}_T\to S$, whose range $t_T$ is the partial identity on the theorem set. The proof-object characterization is supplied separately by Appendix B. Finite computation proofs give
$$
1_A\le\theta^*t_{\mathrm{PA}},\qquad
1_B\le\theta^*\nu^*t_{\mathrm{PA}},\qquad
t_{\mathrm{PA}}\le t_T.
$$
Consistency gives $t_T\nu^*t_T=0$. Corollary 3.5 proves inseparability and rules out completeness. On the recursive carrier $S$, a complementary pair of c.e. domains is recursive, yielding the stated recursive inseparability of the sets.

### Further comparisons in §8

For consistent c.e. $T$, put $P_T=\{n:T\vdash\alpha(\bar n)\}$ and $N_T=\{n:T\vdash\neg\alpha(\bar n)\}$. These are disjoint c.e. supersets of $A,B$, hence recursively inseparable. They enlarge under theory extension. The assignment $T\mapsto(\omega,P_T,N_T)$, using identity maps on theory inclusions, is a functor to $\operatorname{Pair}(\mathrm{Rec})$, whose morphisms are total recursive functions preserving the two specified subsets.

For a restriction idempotent $c=[C]_T$ on $\omega$, the observation
$$
E_T(c)=\{n\in\mathbb N:T\vdash C(\bar n)\}
$$
is c.e., independent of the representative, monotone, and preserves finite meets, top and bottom. If $\kappa_n:\omega\to\omega$ is the constant morphism with value the numeral $n$, then
$$
n\in E_T(c)\Longleftrightarrow c\kappa_n=\kappa_n
\Longleftrightarrow F_T(c)F_T(\kappa_n)=F_T(\kappa_n).
$$
The graph equation proves the first equivalence; faithfulness proves the second. No preservation of joins is claimed for $E_T$.

For the complete theory $T=\operatorname{Th}(\mathbb N)$, standard interpretation is an isomorphism $S_T\cong\mathrm{Rec}$: equality of classes is exactly truth of the uniform graph-equivalence sentence, hence equality of standard partial functions. Thus $S_T$ has inseparable pairs although $T$ is complete. **Inseparability in $S_T$ alone does not imply incompleteness of the external theory $T$.** The proof of Corollary 8.1 instead uses the numerical category, c.e. proof sets, and the displayed reductions to PA-provability and refutability.


## §9. The cosheaf recursion category and propositional theories

Let $X=\{a,b,c\}$ have opens $\varnothing,\{c\},\{a,c\},\{b,c\},X$, and let $J=(1\leftarrow0\to2)$. The category $\mathcal C_{\mathrm{rec}}$ has c.e. subsets of finite powers of $\mathbb N$ as objects and functions computed by partial recursive functions total on their source carriers as morphisms, with extensional equality. Put
$$
\mathcal E=\mathcal C_{\mathrm{rec}}^J,
\qquad
\mathcal A=\operatorname{Par}(\mathcal E,\operatorname{Mono}).
$$
A morphism of $\mathcal A$ is a natural transformation defined on a c.e. subfunctor of its source. Its restriction and range are partial identities on its domain and component-image subfunctors, respectively. Define $V\in\mathcal E$ by
$$
V_0=\mathbb N^4,\quad V_1=V_2=\mathbb N^2,
\quad r_1^V(k,z,a,b)=(k,a),\quad r_2^V(k,z,a,b)=(k,b).
$$
The full subcategory $\mathscr R_X\subseteq\mathcal A$ has the objects obtained from $V$ by the specified binary products, coproducts, and nonempty-word formation. The formulas and derivations used below are constructed in $\mathcal E$, identified with $\operatorname{Tot}(\mathcal A)$.

**Proposition 9.1 (`prop:endpoint`).** For $j=0,1,2$, component evaluation gives a covariant functor
$$
E_j:\mathcal A\longrightarrow\mathcal K,
\qquad
\mathcal K=\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono}),
$$
preserving restrictions, zeros, ranges, binary restriction products and coproducts, and finite joins of restriction idempotents. For $i=1,2$, $E_i\tau:\mathbb N^2\times\mathbb N^2\rightharpoonup\mathbb N^2$ is a Turing morphism, where $\tau$ is the morphism of Theorem A.7. Componentwise pullbacks and images prove the structural assertions; the numerical parameter theorem proves the Turing property. The following unnumbered argument exhibits a total function $V_0\to V_0$ that cannot be specialized from $E_0\tau$: naturality forces its first endpoint output to ignore an input coordinate that the displayed counterexample uses. Thus the Turing-property assertion is restricted to endpoints 1 and 2.

**Theorem 9.2 (`thm:cosheaf-observation`).** Theorem 3.3 applied to the full inclusion $\mathscr R_X\hookrightarrow\mathcal A$ gives inseparable restriction idempotents $a,b:V\rightharpoonup V$, with domain subfunctors $A,B\subseteq V$. Let $S\in\mathcal E$ be the formula functor of Proposition B.1, $\theta:V\to S$ its atom constructor, $\nu:S\to S$ its negation constructor, and $t_0:S\rightharpoonup S$ the partial identity on the base theorem subfunctor from Theorem B.2. Let $T\subseteq S$ be a compatible family of consistent c.e. deductively closed extensions of that base family, and let $t_T:S\rightharpoonup S$ be its partial identity. Then $t_T,\nu^*t_T$ are inseparable in $\mathcal A$. For each $i\in\{1,2\}$,
$$
P_{i,T}=(E_i\theta)^{-1}(T_i),
\qquad
N_{i,T}=(E_i\theta)^{-1}(\nu_i^{-1}(T_i))
$$
are disjoint recursively inseparable c.e. subsets of $\mathbb N^2$, containing $A_i,B_i$, respectively; the theory with theorem set $T_i$ is incomplete. The assignment $T\mapsto(\omega\times\omega,P_{i,T},N_{i,T})$, with identity morphisms on the underlying object for inclusions, defines a covariant functor from the poset of these families to $\operatorname{Pair}(\mathrm{Rec})$.

The categorical conclusion follows from Corollary 3.5 using
$$
a\le\theta^*t_0,\qquad b\le\theta^*\nu^*t_0,
\qquad t_0\le t_T,\qquad t_T\nu^*t_T=0.
$$
For the endpoint conclusions, Proposition 9.1 permits a separate application of Theorem 3.3 in the full numerical recursion category generated by $\mathbb N^2$, proving recursive inseparability of $A_i,B_i$. A separator of $P_{i,T},N_{i,T}$ would separate that fixed pair. Completeness of $T_i$ would make $P_{i,T},N_{i,T}$ complementary c.e. sets, hence recursive. The argument does **not** infer inseparability merely from preservation of ranges by $E_i$.

**Corollary 9.3 (`cor:cosheaf-essential-incompleteness`).** For $i=1,2$, the consistent propositional theory with theorem set $(D_{t_0})_i$ is essentially incomplete: every consistent extension in the same language with a c.e. axiom set is incomplete. Its proof takes the c.e. deductive closure $U\subseteq S_i$ of such an axiom set, replaces the base family’s $i$th component by $U$, and leaves the other components unchanged. The resulting family is compatible because the base theorem sets form a subfunctor and $U$ contains the old $i$th component. Theorem 9.2 applies. No corresponding claim for component 0 is made.

## Appendix A: existence and structure of the cosheaf example

**Proposition A.1 (`prop:fork-cosheaves`).** Restriction to $\{c\},\{a,c\},\{b,c\}$ defines
$$
\operatorname{CoSh}(X,\mathbf{Set})\simeq\mathbf{Set}^J.
$$
The quasi-inverse assigns $A\amalg_C B$ at $X$ to the diagram $A\leftarrow C\to B$, and the empty set at $\varnothing$. The only nonredundant cover condition is the displayed pushout; its universal property supplies the morphism assignment and the natural isomorphisms. For the effective diagrams in $\mathcal E$, the value at $X$ has a quotient presentation with a c.e. generated equivalence relation. Products and subobjects used later belong to $\mathcal E$; their associated cosheaf values at $X$ need not be setwise products or injections.

**Propositions A.2–A.4 (`prop:fork-total`, `prop:fork-structure`, `prop:fork-local`).** Both $\mathcal C_{\mathrm{rec}}$ and $\mathcal E$ have finite limits and finite coproducts. The category $\mathcal E$ is regular and extensive; monomorphisms and regular images are componentwise injections and c.e. images. The partial-map category $\mathcal A$ is split and prodominical, has binary restriction products and coproducts, weak choice, and ranges satisfying agreement. Finite unions of domain subfunctors give joins; inverse images along arbitrary partial morphisms preserve binary meets and finite joins. Ranges commute with products and are stable under pullback along total morphisms. Finally, $\mathcal A$ is locally connected.

The proofs construct the numerical limits and image factorizations, obtain numerical sections of surjections by search, and verify descent and naturality componentwise. Extensivity uses inverse images of coproduct tags. Partial-map composition is computed on its exact component domains; the range and agreement laws follow from component images. A partial monomorphism has injective components on its domain; recursive preimage search gives a natural partial inverse. Connected restriction idempotents are supplied by the finite subfunctor generated by one component-0 element and by singleton subfunctors concentrated at an endpoint. They detect the domains and values of all component partial functions.

**Lemma A.5 (`lem:fork-dominance`).** Every $Y\in\mathcal E$ admits a total restriction embedding $m:Y\to V$ with partial inverse $m^\dagger:V\rightharpoonup Y$, satisfying $m^\dagger m=1_Y$ and $mm^\dagger=\overline{m^\dagger}$. Recursive injections of the three carriers into $\mathbb N$ give injective natural components; their c.e. images and inverse-search maps provide the partial inverse.

**Lemma A.6 (`lem:fork-frames`).** There are isomorphisms in $\mathcal E$
$$
V\cong V\times V,\qquad V\cong V+V,\qquad V\cong V^\#.
$$
Coordinatewise pairing constructs the first. The parity of the shared first coordinate chooses a coproduct summand for the second. For the third, that coordinate encodes a nonempty word and its length, while the other coordinates encode tuples of the same length. The formulas commute with both structure morphisms of $J$, and the inverses are recursive. The preceding unnumbered construction defines $(-)^\#:\mathcal A\to\mathcal A$; its total part gives the free internal semigroup on each $Y\in\mathcal E$ by finite multiplication of word entries.

**Theorem A.7 (`thm:fork-turing`).** There is $\tau:V\times V\rightharpoonup V$ in $\mathcal A$ such that every $F:Y\times V\rightharpoonup V$, for arbitrary $Y\in\mathcal A$, factors as
$$
F=\tau(c\times1_V)
$$
for a total $c:Y\to V$. At either endpoint, $\tau_i$ evaluates the numerical index in the parameter’s second coordinate. At component 0, the parameter contains indices for all three components. Evaluation is admitted only when all three computations terminate and their outputs satisfy the two naturality equations. This gives a c.e. domain subfunctor. To specialize a given $F$, first choose numerical partial functions with domains exactly its three component domains, then apply the parameter theorem. Assemble the specialized indices into a natural $c$. Naturality of $F$ makes the compatibility tests succeed on its domain, and termination of the component-0 evaluator prevents additional domain elements. The conclusion includes equality of domains, not only agreement of values when both sides are defined.

**Proposition A.8 (`prop:fork-recursion`).** The full subcategory $\mathscr R_X$ specified above is a recursion category. Its inclusion in $\mathcal A$ is a range functor, and
$$
\operatorname{Split}(\mathscr R_X)\simeq\mathcal A
$$
as restriction categories. Lemma A.6 gives isotypicality; the binary structure is inherited; Theorem A.7 and fullness give the Turing property. Restrictions, ranges, and coproduct operations remain in the full subcategory. The splitting functor sends a restriction idempotent $e$ to its domain subfunctor $D_e$, and sends $f:(Y,e)\rightharpoonup(Z,d)$ to $r_d f m_e:D_e\rightharpoonup D_d$, where $m_e:D_e\to Y$, $r_e:Y\rightharpoonup D_e$ split $e$. The inverse hom-set map is $g\mapsto m_d g r_e$. Lemma A.5 supplies essential surjectivity.

**Corollary A.9 (`cor:fork-karoubi`).** Every idempotent of $\mathcal A$ splits, and the inclusion extends to
$$
\operatorname{Kar}(\mathscr R_X)\simeq\mathcal A.
$$
For $p:Y\rightharpoonup Y$ with $p^2=p$, its component images form a c.e. subfunctor $I_p\subseteq Y$, and $p$ fixes those images. Its image inclusion $m_p:I_p\to Y$ and its corestriction $r_p:Y\rightharpoonup I_p$ satisfy $m_pr_p=p$, $r_pm_p=1_{I_p}$. Send $(Y,e)$ to $I_e$ and $f$ to $r_d f m_e$; the same inverse hom-set construction and Lemma A.5 prove equivalence. Restriction preservation uses the stated restriction $\bar f e$ in the full Karoubi envelope. This image-splitting argument, rather than restriction splitting alone, justifies use of the full Karoubi envelope.

**Proposition A.10 (`prop:fork-distinction`).** The recursion category $\mathscr R_X$ is not equivalent as a restriction category to $\mathrm{Rec}$, and $V$ has no decidable equality in $\mathcal E$. For the first assertion, the unnumbered numerical splitting equivalence
$$
\mathsf Q_{\mathrm{num}}:\operatorname{Split}(\mathrm{Rec})
\simeq\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono})
$$
is constructed explicitly using recursive carrier encodings. A restriction equivalence would then yield $\mathcal E\simeq\mathcal C_{\mathrm{rec}}$. Their terminal objects have five and two subobjects, respectively. For the second assertion, a putative equality morphism $V\times V\to1+1$ must be natural. Two different component-0 tuples having the same first endpoint image force incompatible equality values. The assertion concerns a natural equality morphism; it does not deny decidable equality on the separate numerical carriers.

## Appendix B: formulas, derivations, and theorem sets

**Proposition B.1 (`prop:fork-syntax-initial`).** The formula functor $S\in\mathcal E$ is generated componentwise by atoms labeled in $V_j$, negation, and implication. For
$$
P:\mathcal E\to\mathcal E,\qquad P(Z)=V+Z+(Z\times Z),\qquad P(f)=1_V+f+(f\times f),
$$
the constructor morphism $\iota:P(S)\to S$ is initial among $P$-algebras. The proof evaluates finite formula trees in any algebra $\alpha:P(Z)\to Z$. Induction gives termination on the recursive formula carrier, the algebra equation, naturality under relabeling, and uniqueness. Thus the universal property is established in $\mathcal E$, not merely in the separate categories of sets.

**Theorem B.2 (`thm:fork-proof-presentation`).** Given disjoint restriction idempotents $a,b:V\rightharpoonup V$ in $\mathcal A$, with domain subfunctors $A,B$, construct proofs in the specified three-scheme Hilbert calculus with additional positive axioms $\theta_j(x)$ for $x\in A_j$, negative axioms $\nu_j\theta_j(y)$ for $y\in B_j$, and modus ponens. Finite valid proof codes form $\mathrm{Prf}\in\mathcal E$; their conclusion maps form $c:\mathrm{Prf}\to S$. The range $t_0=\operatorname{ran}(c):S\rightharpoonup S$ is the partial identity on the least c.e. subfunctor containing the axioms and closed under modus ponens, and
$$
a\le\theta^*t_0,\qquad b\le\theta^*\nu^*t_0,
\qquad t_0\nu^*t_0=0_S.
$$
Finite parsing and semidecision of the atomic labels make the proof carriers c.e.; relabeling preserves proofs and conclusions. Induction on trees proves deductive closure and leastness. The one-node proofs give the inequalities. For consistency, two alleged proofs of opposite formulas use finitely many positive atomic labels. Assigning those labels truth and all other labels falsity makes all leaves of both proofs true because $A_j\cap B_j=\varnothing$; Boolean soundness gives a contradiction. These valuations are external componentwise arguments, not asserted natural morphisms $V\to1+1$.

**Proposition B.3 (`prop:fork-proof-initial`).** The derivation object has an explicit universal property. Let $\lambda:\mathrm{Ax}\to S$ collect tagged instances of the three logical schemes and the positive and negative axioms. For $q:Q\to S$, let $M(Q,q)$ be the pullback of $q\times q:Q\times Q\to S\times S$ along
$$
\mu:S\times S\to S\times S,
\qquad\mu(\alpha,\beta)=(\alpha,\alpha\Rightarrow\beta),
$$
and let $\kappa_q:M(Q,q)\to S$ return $\beta$. Then
$$
\mathsf H:\mathcal E/S\to\mathcal E/S,
\qquad
\mathsf H(Q,q)=(\mathrm{Ax}+M(Q,q),[\lambda,\kappa_q])
$$
is an endofunctor. The morphism $\delta:\mathsf H(\mathrm{Prf},c)\to(\mathrm{Prf},c)$ adjoining a leaf or a modus-ponens root is initial. Pullback uniqueness gives the functor laws. For any algebra $\eta:\mathsf H(Q,q)\to(Q,q)$, finite-tree evaluation defines the unique $u:\mathrm{Prf}\to Q$ with $qu=c$ and $u\delta=\eta\mathsf H(u)$. Computability, naturality, and the equations follow by induction. This characterizes the derivations with their conclusion map; it does not define every restriction idempotent to be a theory.

**Proposition B.4 (`prop:first-order-proof-initial`).** Fix a recursively coded first-order language and a theory $T$ whose nonlogical axioms are sentences. Work in $\mathcal D=\mathcal C_{\mathrm{rec}}$ when the axiom set is c.e., or in $\mathcal D=\operatorname{Tot}(\operatorname{Split}(\mathcal E_a))$ when it is $\mathcal E_a$-semidecidable, using the carrier presentation specified in §4. Let $\mathsf F$ be the formula carrier and $\mathsf S\hookrightarrow\mathsf F$ the sentence subobject. In the fixed sound and complete Hilbert calculus, the rule-instance objects $R_0,R_1,R_2$ describe axiom leaves, generalization, and modus ponens. Their premise and conclusion morphisms are
$$
p_k:R_k\to\mathsf F^k,\qquad q_k:R_k\to\mathsf F.
$$
For $q:Q\to\mathsf F$, form $B_k(Q,q)=R_k\times_{\mathsf F^k}Q^k$. The sum of these pullbacks, with its conclusion morphism, defines $\mathsf H_T:\mathcal D/\mathsf F\to\mathcal D/\mathsf F$. Finite derivation trees and their root conclusions form an initial $\mathsf H_T$-algebra $(\mathsf{Der}_T,d_T)$. The pullback along $\mathsf S\hookrightarrow\mathsf F$ gives the sentence-proof morphism $c_T:\mathrm{Prf}_T\to\mathsf S$; its range in the corresponding partial-map category is the partial identity on the theorem set of $T$.

The proof uses finite syntactic checking and finitely many semidecidable axiom-membership tests to obtain the derivation carrier. Tree evaluation proves initiality. In the Miller category, evaluation first semidecides the valid-tree carrier, then evaluates with values independent of the binary representation, so it has the required domain and uniformity. Closedness of a formula is recursive, giving the sentence-proof pullback. This is an existence result in the two specified categories; it is not an existence theorem for arbitrary restriction categories. Generalization needs no additional assumption-side condition because all nonlogical assumptions are sentences.

## Appendix C. Failure without section lifting

### Proposition C.1 — `prop:missing-lift`

**Statement.** There is a prodominical recursion category $\mathcal C_K$ with ranges and binary restriction coproducts and a faithful range functor $F:\mathcal C_K\to\mathbf{Pfn}$ preserving restriction products and reflecting zero morphisms, for which all hypotheses of Theorem 3.3 except section lifting hold. The designated diagonal pair is separable. Some parallel morphisms with disjoint domains have no common upper bound, although finite joins of restriction idempotents exist.

**Construction.** Let $K=\{e:\varphi_e(e)\downarrow\}$. Objects are numerical carriers generated from $\mathbb N$ by products and tagged coproducts. A morphism is a partial function with $K$-c.e. domain and an ordinary partial recursive extension. Equality is extensional. Total morphisms are exactly ordinary total recursive functions. On $\mathbb N$, every morphism has the form
$$
f_{e,a}(x)\simeq\varphi_e(x)\quad\text{for }x\in W_a^K,
$$
with actual domain $W_a^K\cap\operatorname{dom}(\varphi_e)$. The functor $F$ forgets no underlying set or partial-function data.

**Structural proof.** Composition has an ordinary partial recursive extension and $K$-c.e. domain $D_f\cap f_0^{-1}(D_g)$. Restrictions, products and copairings remain in the class. Images are $K$-c.e., so their partial identities are ranges and satisfy range agreement. Recursive codings make the category isotypical; products with zero are zero. The morphism
$$
\tau_K(\langle e,a\rangle,x)\simeq f_{e,a}(x)
$$
has an ordinary partial recursive extension and a $K$-c.e. domain. Ordinary specialization of both an extension index and an oracle-domain index produces a total recursive parameter map, proving the Turing property. The target $\mathbf{Pfn}$ satisfies the structural hypotheses of Theorem 3.3.

**Separation and failed lift.** Put $p(q)\simeq\varphi_{\pi_0(q)}(q)$, and let $A=\{q:p(q)\downarrow\text{ is even}\}$. This ordinary c.e. set is decidable relative to $K$. The even-output domain of $\tau_K\Delta$ lies in $A$, and the odd-output domain lies in $A^c$. Hence the two partial identities $1_A,1_{A^c}$, both present in $\mathcal C_K$, separate the designated pair. A reduction from $K$ proves that $A$ is not recursive. The unique target section of $\nabla(1_{A^c}+1_A)$ returns the second tag on $A$ and the first tag on $A^c$; it is total but not recursive and therefore has no source lift. Finally, any common upper bound of $i_1 1_A$ and $i_0 1_{A^c}$ would be this same total switching function, so no such bound exists.


## Source dependencies and scope

Miller's sequence existence and index property, and Bauer–Hanson's binary-representation formulation, are cited inputs. Montagna supplies the formalized computation-coding properties used in Lemma 5.1. The cited failure of local connectedness of the syntactic categories and the composition failure in the primed systems are also external inputs. The bibliography and the introduction's related-work subsection identify the roles of Di Paola–Heller, Heller, Rosolini, Cockett–Lack, Cockett–Hofstra, Bernardi, and Lengyel with the cited corrections. A review of the introduction must verify the particular historical or comparative claim it makes; this synopsis does not establish priority.

The report was assembled from separate reviews of the categorical/arithmetic arguments, the Miller section, and the cosheaf and derivation constructions, then checked against the version 12 theorem labels. The current manuscript remains distinct from the version 5 Lean baseline.
