# Two explicit witnesses for the historical comparisons in §1

The six outstanding historical conclusions have their hypotheses and uses in the [v81 source comparison](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/bacddde5000f53fcf6be55c63933d643cc9207cb/docs/reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md). The following equations specify witnesses for two of the constructions requested there. Both are manuscript-side derivations.

## Bauer–Hanson, Theorem 6.4

Fix a Miller sequence $\mu$. In the parameterized realizability topos $\mathcal T_\mu$ for all binary names of $\mu$, write $N$ for the natural numbers object, $R_D$ for its Dedekind reals, and $I_D\hookrightarrow R_D$ for the closed unit interval. Lemma 6.3 identifies $I_D$ with the assembly whose existence predicate at $x$ is $\{m:\mu(m)=x\}$ on its prescribed carrier. The identity realizer sends a witness $m$ of that predicate to the preimage $m$. Thus $e:N\to I_D$, with $e(m)=\mu(m)$ in this assembly, is an epimorphism.

For a recursive pairing of natural numbers, Lemma 6.1 gives an internal morphism $q:N\to R_D$ by
$$q(\langle m,n\rangle)=m(2e(n)-1).$$
Internally, for $x:R_D$ there exists $m:N$ with $-m<x<m$, whence $m>0$ and $y=(x+m)/(2m)$ belongs to $I_D$. Since $e$ is epic, internally there exists $n:N$ with $e(n)=y$, and then $q(\langle m,n\rangle)=x$. The conclusion for §1 is therefore $\operatorname{im}(q)=1_{R_D}$ as a subobject. The construction of the cut theory in §9 uses only the external Miller sequence at this step. [Bauer–Hanson, §§6–6.1](https://arxiv.org/html/2404.01256v3#S6.SS1)

## Lengyel, corrected Theorem 26

Let $L:\mathcal C\to\mathcal D$ be a faithful iteration functor between iteration categories with $\mathcal D$ separated. Let $\mathcal B=\mathcal B\langle X\rangle$ be a uniformly generated isotypical $B^\#$-subcategory of the total morphisms of $\mathcal C$. In $\operatorname{Tur}(\mathcal B)$ the weak universal morphism $\alpha:X\times X\rightharpoonup X$ must have the following property. For each $a:X\rightharpoonup X$ there is a total $g:X\to X$ in $\mathcal B$ with $\alpha\circ(g\times1_X)=a\circ\pi_2$, where $\pi_2:X\times X\to X$ is the second projection. The construction and composition of the developments in $\operatorname{Tur}(\mathcal B)$ and this equation for the constructed $\alpha$ are required.

Let $b:X\xrightarrow{\sim}X\times X$ be the frame isomorphism and let $s:(X\times X)\times X\xrightarrow{\sim}X\times(X\times X)$ be the associator. Define
$$\zeta=\alpha\circ(1_X\times b^{-1})\circ s\circ(b\times1_X):X\times X\rightharpoonup X.$$
Given $\psi:V\times X\rightharpoonup X$, choose a frame isomorphism $c:V\xrightarrow{\sim}X$ and apply the weak universal property to $a=\psi\circ(c^{-1}\times1_X)\circ b$. Take $j=b^{-1}\circ\langle g\circ c,c\rangle:V\to X$. This morphism is total. With $k=b^{-1}\circ(c\times1_X):V\times X\to X$ and $\pi_V:V\times X\to V$, the product equations give
$$
\zeta\circ(j\times1_X)
=\alpha\circ(g\times1_X)\circ\langle c\circ\pi_V,k\rangle
=a\circ k=\psi.
$$
The last equality uses the defining equations for $a$ and $k$. This equality is in the partial hom-set, including equality of domains. Specializing $L$ to the identity yields the separated case of Theorem 21. Appendix D uses the faithfulness of its family of interpretations, and its proof never needs this completion. [Author’s corrected theorem and construction](https://github.com/flengyel/errata/blob/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004/lengyel2004_repairs_v10.tex#L619-L634)

## Van Dijk–Gietelink Oldenziel, Theorems 5.19 and 5.20

The stated quantifier in Theorem 5.19 ranges over arithmetic-universe objects $U$ in $U_{\mathrm{rec}}$. Syntactic completeness of $U$ implies triviality of $U$. The authors exhibit their diagonal argument for a special case, using their predicate enumeration and projectivity of $1$ in the initial arithmetic universe. A formal proof at the general type needs an argument for every $U$ in that quantifier. Theorem 5.20 instead assumes consistency of the initial arithmetic universe $U_0$. It asserts that the equalizer of the two indicated internal truth values represents a subobject of $1$ distinct from the bottom subobject in $U_0$. The categorical slice theorem and the consistency proof for the signed PA theory have separate proofs in the manuscript. [Theorems 5.19–5.20, pp. 25–26](https://arxiv.org/pdf/2004.10482#page=25)
