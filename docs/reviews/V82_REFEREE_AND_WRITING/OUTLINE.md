# Outline of *Logical consequence and essential incompleteness in recursion categories*

Manuscript v82 at `d87dbbce62140fb2ef72775890ac201c5afa8341`. Section numbers and opening pages follow the printed contents. The order, including the arithmetic subsections nested inside §8, follows the [LaTeX inputs](../../../manuscript/latex/main.tex). The [correspondence](../../../FORMALIZATION_STATUS_V82.md) identifies statements in the formal development.

## Abstract, p. 1

Let $\mathscr C=\operatorname{Split}(\mathscr R)$ for a recursion category $\mathscr R$, and let $\mathcal D=\operatorname{Tot}(\mathscr C)$. Assume the regularity, coproduct, partial-inverse, syntax and derivation hypotheses stated in the abstract. Take disjoint subobjects $i_a:A\hookrightarrow X$ and $i_b:B\hookrightarrow X$ in $\mathcal D$. In the language with object $X$ of nullary predicate symbols, let $\theta_X:X\to S_X$ form atomic sentences and let $\nu_X:S_X\to S_X$ form negations. Let $T_{a,b}$ be the deductive closure of $\operatorname{im}(\theta_X i_a)\vee\operatorname{im}(\nu_X\theta_X i_b)$. If $T_{a,b}$ is consistent, every consistent deductively closed extension in the same language is incomplete if and only if no complementary subobjects $c,d$ of $X$ satisfy $a\le c$ and $b\le d$. Sections 4–5 prove the classification and its slice formulation. Sections 8–10 give three realizations with different hypotheses on their extensions.

## 1. Introduction, p. 4

The introduction states the two equivalences and the diagonal comparison used in the examples.

- [**1.1 (Related work)**](../../../manuscript/latex/sections/01-introduction.tex#L159) places these results in the literature. The argument of Di Paola–Heller 8.15 gives inseparable diagonal domains when the Turing object has nonzero identity. Their theorem assumes sections for every morphism and compatible binary coproducts. The v82 proof comparison records the sum-valued universal morphism and the coproduct laws the checked argument uses. Section 3 isolates the lift their argument requires in a comparison with another category. Bernardi uses precomplete equivalence relations. Montagna and Di Paola–Montagna supply syntactic precedents for §6. Murwanashyaka–Pakhomov–Visser encode disjoint c.e. sets by finite equivalence-class sizes and characterize essential undecidability by recursive inseparability. Section 4 constructs a free theory on internal subobjects. Heller and Lengyel concern existence of recursion categories. Van Dijk–Gietelink Oldenziel describe Joyal's arithmetic-universe proofs. Cockett–Hofstra relate Turing categories to partial combinatory algebras by splitting idempotents. Cockett's results on inseparable domains and provability predicates supply further comparisons.

## 2. Categorical preliminaries, p. 6

- [**2.1 (Partial maps and restriction idempotents)**](../../../manuscript/latex/sections/02-categorical-preliminaries.tex#L3) treats domains of partial maps as restriction idempotents and defines their order and splitting.

- [**2.2 (Products, coproducts, and local connectedness)**](../../../manuscript/latex/sections/02-categorical-preliminaries.tex#L110) fixes products, restriction coproducts and local connectedness.

- [**2.3 (Recursion categories)**](../../../manuscript/latex/sections/02-categorical-preliminaries.tex#L185) gives the Turing property used throughout. For a partial map $f:W\times U\rightharpoonup U$, a total parameter map $g:W\to U$ satisfies $f=\tau(g\times1_U)$.

## 3. Diagonal comparison and complementary conditionals, p. 9

- [**3.1 (The comparison theorem)**](../../../manuscript/latex/sections/03-sections-and-inseparability.tex#L19) defines $h=b\tau\Delta_U:U\rightharpoonup U+U$ and its two summand domains $a_0,a_1$. For the functor $F$ of Theorem 3.1, let disjoint domains $P,N$ on $FU$ contain $F(a_0),F(a_1)$ respectively. A partial conditional with summand inverse images $N,P$ and a lift in the source yield a total $g:U\to U$ with $(Fg)^*P=(Fg)^*N=0$. If $F(1_U)\ne0$ and this inverse image preserves $P\vee N$, then $P\vee N\ne1_{FU}$.

- [**3.2 (Complementary conditionals)**](../../../manuscript/latex/sections/03-sections-and-inseparability.tex#L108) supplies source conditionals from joins of disjoint morphisms or from specified sections. Appendix C shows why the lift matters.

## 4. Internal theories and essential incompleteness, p. 11

- [**4.1 (Theories and their interpretation)**](../../../manuscript/latex/sections/03a-internal-theories.tex#L3) identifies the theorem subobject $t\hookrightarrow S$ as the image of finite sentence derivations and its refutation subobject as $\nu^*t$.

- [**4.2 (Incompleteness from semantic consistency)**](../../../manuscript/latex/sections/03a-internal-theories.tex#L149) applies §3 to the interpreted theorem and refutation domains under the disjointness, lifting and nonzero hypotheses.

- [**4.3 (Inseparability in the source)**](../../../manuscript/latex/sections/03a-internal-theories.tex#L209) proves that a total $f:X\to S$ carrying inseparable domains into the theorem and refutation domains rules out completeness of any consistent closed extension.

- [**4.4 (Generation and logical translations)**](../../../manuscript/latex/sections/03b-internal-adjunctions.tex#L1) gives the least deductive closure and the adjunction between generation after direct image and inverse image under a translation.

- [**4.5 (Change of the ambient category)**](../../../manuscript/latex/sections/03b-internal-adjunctions.tex#L188) compares deduction under a change of ambient category.

- [**4.6 (Free first-order theories and inseparability)**](../../../manuscript/latex/sections/03b-internal-adjunctions.tex#L323) proves the free first-order adjunction (Theorem 4.7) and the classification in the abstract (Corollary 4.8). A complementary separator gives a Boolean valuation and hence a complete consistent extension. Conversely, pulling back the theorem and refutation subobjects of such an extension along $\theta_X$ gives a separator.

## 5. Theory extensions and recursion categories, p. 20

- [**5.1 (Categories associated with internal theories)**](../../../manuscript/latex/sections/04-theory-extensions.tex#L12) identifies $\mathscr C$ with $\operatorname{Par}(\mathcal D,\operatorname{Mono})$ under the partial-inverse hypothesis and equips $\mathscr C[U]=\operatorname{Par}(\mathcal D/U,\operatorname{Mono})$ with a Turing structure.

- [**5.2 (Functoriality under theory extension)**](../../../manuscript/latex/sections/04-theory-extensions.tex#L131) sends a theory inclusion $i:T\hookrightarrow U$ to a fully faithful postcomposition functor with adjunctions $\Sigma_i\dashv i^*\dashv\Sigma_i$.

- [**5.3 (Essential incompleteness in the associated category)**](../../../manuscript/latex/sections/04-theory-extensions.tex#L228) assumes initial derivation algebras in every parameter slice and a logical theorem $\lambda:1\to S$ factoring through every consistent theory. For consistent $u:U\hookrightarrow S$, the constant family $1_U\times u$ over $U$ is essentially incomplete exactly when $u$ is. Evaluation at the chosen factorization $1\to U$ recovers $u$. A total Boolean extension of the partial theorem/refutation map exists exactly when its two domains are separable.

## 6. The syntactic recursion category, p. 24

For a consistent extension $T$ of PA in the arithmetic language, the objects of $S_T$ are formal expressions generated by $\omega$, binary product and binary coproduct. Morphisms are program indices modulo $T$-provable graph equality on their specified types.

- [**6.1 (The total restriction splitting)**](../../../manuscript/latex/sections/05a-internal-syntax.tex#L1) constructs the regular category of total maps in the restriction splitting.

- [**6.2 (Syntax and lists)**](../../../manuscript/latex/sections/05a-internal-syntax.tex#L277) constructs internal terms, formulas and finite lists.

- [**6.3 (Free variables and substitution)**](../../../manuscript/latex/sections/05a-internal-syntax.tex#L522) computes free variables and admissible substitution.

- [**6.4 (Derivations and theories)**](../../../manuscript/latex/sections/05a-internal-syntax.tex#L657) constructs finite derivations and obtains the least deductively closed subobject from the image of the conclusion map.

## 7. Interpretation and soundness, p. 37

Interpreting program graphs in a model $M\models T$ gives $F_M:S_T\to\mathrm{Pfn}$.

- [**7.1 (Lifting complementary conditionals)**](../../../manuscript/latex/sections/06-interpretation-in-models.tex#L64) constructs source conditionals and deduces inseparability of the diagonal pair.

- [**7.2 (The total interpretation functor)**](../../../manuscript/latex/sections/06-interpretation-in-models.tex#L125) extends the interpretation to the splitting and obtains a regular functor on total maps.

- [**7.3 (Soundness on standard codes)**](../../../manuscript/latex/sections/06-interpretation-in-models.tex#L175) proves soundness on standard codes using a model of the chosen axioms.

- [**7.4 (Ultrapowers of the interpretation functor)**](../../../manuscript/latex/sections/06-interpretation-in-models.tex#L348) compares ultrapowers of the standard interpretation with interpretation in the ultrapower of the standard model. The distinction between standard proof codes and elements of the interpreted proof object is needed in §8.

## 8. Essential incompleteness of arithmetic, p. 43

- [**8.1 (Comparison in the fixed syntactic category)**](../../../manuscript/latex/sections/08-essential-incompleteness-of-arithmetic.tex#L3) applies diagonal comparison in the fixed syntactic category of PA. Consistency of a c.e. arithmetic presentation deriving the PA sentence axioms suffices for recursive inseparability of its theorem and refutation sets (Corollary 8.4).

- [**8.2 (An indexed family of arithmetic theories)**](../../../manuscript/latex/sections/08a-uniform-theories.tex#L1) constructs an indexed family with fiber $\Gamma_e$ consisting of the PA axioms and the arithmetic sentences on whose codes program $e$ halts.

- [**8.3 (Uniform independent sentences)**](../../../manuscript/latex/sections/08b-uniform-independent-sentences.tex#L1) constructs one total morphism $q:E\to S$ whose standard interpretation at every index $e$ with consistent $\Gamma_e$ codes a sentence independent of $\Gamma_e$ (Theorem 8.6).

- [**8.4 (The numerical realization)**](../../../manuscript/latex/sections/08c-numerical-realization.tex#L1) realizes syntax and finite derivations numerically. With recursive supports for each symbol class, term and formula membership are decidable on *every* numerical word code (Proposition 8.8).

- [**8.5 (Numerical incompleteness)**](../../../manuscript/latex/sections/08d-numerical-incompleteness.tex#L1) applies §4 to the ordinary numerical diagonal pair and the theorem domain of a consistent c.e. presentation containing the PA axioms.

- [**8.6 (Numeral instances and theory extension)**](../../../manuscript/latex/sections/08-essential-incompleteness-of-arithmetic.tex#L288) sends each consistent c.e. extension $T$ of PA to the disjoint sets of numerals at which $T$ proves $\alpha$ and $\neg\alpha$, respectively. Theory inclusions induce the identity function on numeral indices.

- [**8.7 (The associated recursion categories)**](../../../manuscript/latex/sections/08-essential-incompleteness-of-arithmetic.tex#L329) assumes PA consistent and applies §5 to the internal theory $t_{\pm}$ generated by the diagonal pair in the splitting of $S_{\mathrm{PA}}$ (Corollary 8.10).

## 9. Miller sequences and essential incompleteness, p. 60

Miller's existence theorem supplies a sequence $a$ such that, if program $d$ computes the same real $r$ to every requested precision from every representation of $a$, then $a(d)=r$. Bauer–Hanson use a Miller sequence to construct a parameterized realizability topos with countable Dedekind reals (their Theorem 6.4). Section 9 uses the sequence to construct a theory of ordered fields.

- [**9.1 (Computation independent of the binary representation)**](../../../manuscript/latex/sections/04-miller-sequences.tex#L48) defines computations that give the same output from every binary representation of $a$.

- [**9.2 (The index sets below and above $1/2$)**](../../../manuscript/latex/sections/04-miller-sequences.tex#L209) reduces the diagonal pair to the index sets $L_a=\{n:a_n<1/2\}$ and $R_a=\{n:a_n>1/2\}$. Their domains are inseparable in the category $\mathcal E_a$, although each individual representation computes a separator of the underlying sets.

- [**9.3 (A theory of real closed fields)**](../../../manuscript/latex/sections/04-miller-sequences.tex#L328) adds constants $c_n$ and their strict rational bounds to real closed ordered fields. Every consistent extension in this language admitting a fixed axiom set semidecided by one oracle program from every representation has inseparable theorem and refutation domains (Theorem 9.7).

- [**9.4 (The associated recursion categories)**](../../../manuscript/latex/sections/04-miller-sequences.tex#L654) proves essential incompleteness of the constant family for each consistent internal extension in its associated category (Corollary 9.8).

## 10. A recursion category from a three-point space, p. 69

The objects of the total diagram category have shape $1\leftarrow0\to2$ in the category of c.e. tuple carriers. Appendix B supplies the recursion category and its splitting.

- [**10.1 (Complementary restriction idempotents and inseparability)**](../../../manuscript/latex/sections/09-three-point-space.tex#L148) characterizes complementary domains of diagrams and obtains inseparability.

- [**10.2 (Evaluation functors)**](../../../manuscript/latex/sections/09-three-point-space.tex#L180) interprets partial maps by evaluation at a vertex.

- [**10.3 (Propositional theories and component theorem sets)**](../../../manuscript/latex/sections/09-three-point-space.tex#L279) constructs the least c.e. propositional theory generated by the signed atomic axioms and logical schemes. At each endpoint separately, every consistent same-language extension admitting a c.e. axiom set is incomplete (Corollary 10.6).

- [**10.4 (First-order theories in the functor category)**](../../../manuscript/latex/sections/09-three-point-space.tex#L624) gives a first-order extension whose restriction to propositional sentences recovers exactly the propositional theory.

- [**10.5 (Categories associated with theory extensions)**](../../../manuscript/latex/sections/09-three-point-space.tex#L813) applies §5 to consistent internal extensions of this first-order theory (Corollary 10.9).

## Appendix A. Syntax and deductively closed theories, p. 78

- [**A.1 (Categorical hypotheses and notation)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L10) lists the categorical hypotheses.

- [**A.2 (Terms, formulas, and free variables)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L119) constructs terms, formulas, lists of free variables and the sentence subobject by pulling back the empty list.

- [**A.3 (Admissible substitution)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L236) defines admissible substitution, including failure when a free variable would be captured.

- [**A.4 (Inference rules and deductively closed subobjects)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L370) presents inference by an endofunctor and proves that finite derivations generate the least closed subobject.

- [**A.5 (First-order theories)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L452) specializes to first-order axioms, modus ponens and generalization, and takes the image of the sentence conclusion map.

- [**A.6 (Propositional theories)**](../../../manuscript/latex/appendices/a-syntax-and-theories.tex#L596) specializes to the propositional calculus.

## Appendix B. The three-point cosheaf construction, p. 86

- [**B.1 (Cosheaves and functor categories)**](../../../manuscript/latex/appendices/b-three-point-cosheaves.tex#L3) identifies cosheaves on the space with fork diagrams and computes the value on the whole space by a pushout.

- [**B.2 (Partial maps, ranges, and connected restriction idempotents)**](../../../manuscript/latex/appendices/b-three-point-cosheaves.tex#L135) constructs partial maps, their ranges and connected restriction idempotents.

- [**B.3 (A universal object and a frame)**](../../../manuscript/latex/appendices/b-three-point-cosheaves.tex#L252) gives a universal diagram and its frame.

- [**B.4 (A Turing morphism)**](../../../manuscript/latex/appendices/b-three-point-cosheaves.tex#L341) constructs the Turing morphism with a total parameter map for each partial family.

- [**B.5 (The recursion category and its splitting)**](../../../manuscript/latex/appendices/b-three-point-cosheaves.tex#L491) passes to the recursion category and its splitting and shows why it is inequivalent as a restriction category to ordinary partial recursive functions.

## Appendix C. Necessity of section lifting for inseparability, p. 92

Morphisms have ordinary partial-recursive extensions and domains c.e. relative to the halting set $K$. A faithful range functor into partial functions satisfies the preservation conditions of Lengyel's 2006 Theorem 4.1, yet a complementary pair separates the two diagonal domains. Disjoint parallel morphisms in this category can lack a common upper bound. The construction distinguishes the source-lifting hypothesis of Theorem 3.1 from preservation of products and reflection of zero.

## Appendix D. Faithful model interpretations and theory extension, p. 95

Taking every model of $T$ on the carrier $\mathbb N$ gives a faithful product interpretation of $S_T$ for consistent $T\supseteq\mathrm{PA}$.

- [**D.1 (Inseparable pairs under theory extension)**](../../../manuscript/latex/appendices/d-faithful-family.tex#L91) follows inseparable diagonal domains under theory extension.

- [**D.2 (Provability of numeral instances)**](../../../manuscript/latex/appendices/d-faithful-family.tex#L148) assumes that $T$ is c.e. and identifies $T\vdash C(\bar n)$ with $[C]_T\kappa_n=\kappa_n$ for the constant morphism $\kappa_n$, and with the corresponding equality under faithful interpretation.

- [**D.3 (The theory of the standard model)**](../../../manuscript/latex/appendices/d-faithful-family.tex#L181) identifies $S_{\operatorname{Th}(\mathbb N)}$ with the numerical recursion category. The former has inseparable domains even though true arithmetic is complete.

## Appendix E. Reading the Lean proofs, p. 97

- [**E.1 (Restriction and extension of an interpretation)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L6) traces the restriction and extension maps in the free-theory adjunction.

- [**E.2 (Separators and complete extensions)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L42) traces both implications relating separators to complete extensions.

- [**E.3 (One valuation for two derivations)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L70) evaluates two finite derivations under one valuation.

- [**E.4 (The lift of a conditional)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L107) identifies the conditional lift in diagonal comparison.

- [**E.5 (Evaluation of a theory in the slice)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L136) evaluates a family of theories at a logical theorem.

- [**E.6 (A uniform choice of independent sentences)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L168) identifies the morphism used for all indices of consistent presentations.

- [**E.7 (Finite proofs and the theorem domain for a Miller sequence)**](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L190) identifies the finite proof relation whose image is the Miller theorem domain.

## References, p. 100

The [bibliography](../../../manuscript/latex/bibliography.tex) follows Appendix E. The external inputs used for construction include the Turing-category results discussed in §§1–2, model-theoretic results in §§7–8 and Appendix D, and the Miller-sequence existence result in §9. The remaining historical comparisons in §1.1 describe other theorems with their own assumptions.
