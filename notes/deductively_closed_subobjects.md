# Deductively closed subobjects and derivations

Fix a formula object and a system of inference rules. Deductive closure can be expressed by an algebra structure on a subobject of the formula object. Under suitable hypotheses on images, the image of an initial algebra is the least such subobject. This separates the categorical construction of derivations from the construction of their conclusions.

Aczel treats sets closed under inference rules and identifies the least closed set with the conclusions of finite proofs for finitary rules [1, Definition 1.1.1 and Proposition 1.1.4]. The construction below expresses these conditions in a category with finite limits and finite coproducts. Initial algebras of dependent polynomial functors provide a related categorical treatment of inductive definitions [2, Section 5].

## 1. Inference rules and deductive closure

Let \(\mathcal D\) be a category with finite limits and finite coproducts. Fix an object \(F\), an integer \(N\geq0\), and morphisms
\[
p_n:R_n\longrightarrow F^n,\qquad q_n:R_n\longrightarrow F
\quad(0\leq n\leq N).
\]
The object \(R_n\) specifies instances of rules with \(n\) ordered premises. The morphisms \(p_n\) and \(q_n\) give the premises and conclusion. We use \(F^0=1\); thus \(R_0\) specifies axiom instances. In a logical application, the formula object and rule morphisms are supplied by a fixed language and calculus.

For an object \(q:Q\to F\) of \(\mathcal D/F\), form
\[
B_n(Q,q)=R_n\times_{F^n}Q^n
\]
with projections \(a_{n,q}:B_n(Q,q)\to R_n\) and \(b_{n,q}:B_n(Q,q)\to Q^n\), satisfying
\[
p_na_{n,q}=q^nb_{n,q}.
\]
Define
\[
H(Q,q)=\left(\coprod_{n=0}^N B_n(Q,q),\kappa_q\right),
\qquad
\kappa_q=[q_na_{n,q}]_{n=0}^N:
\coprod_{n=0}^N B_n(Q,q)\longrightarrow F.
\]
For a slice morphism \(h:(Q,q)\to(Q',q')\), the equations
\[
a_{n,q'}B_n(h)=a_{n,q},\qquad
b_{n,q'}B_n(h)=h^nb_{n,q}
\]
determine \(B_n(h)\) uniquely. They define an endofunctor \(H:\mathcal D/F\to\mathcal D/F\) by taking their coproduct. The identity and composition laws follow from pullback uniqueness.

**Definition.** A subobject \(m:T\hookrightarrow F\) is *closed under the specified rules* if there is a morphism
\[
\alpha:\coprod_{n=0}^N B_n(T,m)\longrightarrow T
\quad\text{such that}\quad m\alpha=\kappa_m.
\]
Equivalently, \((T,m)\) admits an \(H\)-algebra structure in \(\mathcal D/F\). Since \(m\) is monic, this structure is unique when it exists. The equation for the nullary summand states that all specified axioms belong to the subobject. The other summands express closure under the respective rules.

If the specified rules include the logical axioms and inference rules of a fixed calculus, such subobjects are its deductively closed theories. Inclusion of additional axioms in \(R_0\) restricts this class to extensions of those axioms. The subobject and the specified calculus are both necessary for this interpretation.

A slice morphism between two closed subobjects is automatically an algebra morphism: compose the required algebra equation with the target monomorphism and use the slice equations. Closed subobjects therefore form a poset, after identifying isomorphic representatives of the same subobject, ordered by inclusion.

## 2. Derivations and their image

Assume that \(H\) has an initial algebra with structure morphism
\[
\delta:\coprod_{n=0}^N B_n(P,c)\longrightarrow P,
\qquad c:P\longrightarrow F,\qquad c\delta=\kappa_c.
\]
In the applications formed from finite derivation trees, \(P\) is the derivation object and \(c\) gives the conclusion. The initiality assertion is the categorical recursion principle for these derivations.

**Proposition.** If \(\mathcal D\) is regular, the image of \(c\) is the least subobject of \(F\) closed under the specified rules.

**Proof.** Factor \(c=me\), where \(e:P\twoheadrightarrow T\) is a regular epimorphism and \(m:T\hookrightarrow F\) is monic. Regard \(e\) as a morphism \((P,c)\to(T,m)\) in the slice.

The functor \(H\) preserves regular epimorphisms. Finite products preserve them in a regular category; \(B_n(e)\) is a pullback of \(e^n\); and finite coproducts preserve regular epimorphisms. Hence
\[
\varepsilon=\coprod_{n=0}^N B_n(e):
\coprod_{n=0}^N B_n(P,c)\longrightarrow\coprod_{n=0}^N B_n(T,m)
\]
is a regular epimorphism. The equations
\[
m e\delta=\kappa_c,
\qquad
\kappa_m\varepsilon=\kappa_c
\]
give a commutative square with left morphism \(\varepsilon\) and right morphism \(m\). Orthogonality of regular epimorphisms and monomorphisms supplies a unique morphism \(\alpha:\coprod_n B_n(T,m)\to T\) with
\[
m\alpha=\kappa_m,
\qquad
\alpha\varepsilon=e\delta.
\]
Thus \(m\) is closed under the rules.

For any other closed subobject \(u:U\hookrightarrow F\), initiality gives an algebra morphism \(v:(P,c)\to(U,u)\), so \(uv=c\). The image factorization of \(c\) then gives a unique morphism \(w:T\to U\) with \(uw=m\). Hence \(m\) is the least closed subobject. \(\square\)

Regularity is a sufficient hypothesis for this proof. More generally, the argument applies to a proper factorization system whose right class consists of monomorphisms and whose left class is preserved by \(H\). Existence of an initial \(H\)-algebra is a separate hypothesis. Gambino and Hyland prove existence for dependent polynomial functors in locally cartesian closed categories with W-types [2, Theorem 12]; those hypotheses are stronger than the ones used here for the image argument.

## 3. Restriction categories and sentence theories

For a split restriction category \(\mathcal C\), Cockett and Lack prove that \(\mathcal C\) is equivalent, as a restriction category, to \(\operatorname{Par}(\mathcal D,\mathcal M)\), where \(\mathcal D=\operatorname{Tot}(\mathcal C)\) and \(\mathcal M\) is the stable class of restriction monomorphisms [3, Section 3.3]. A closed subobject used as a restriction domain must belong to \(\mathcal M\). The unrestricted image argument above applies directly when \(\mathcal C=\operatorname{Par}(\mathcal D,\operatorname{Mono})\) and \(\mathcal D\) is regular with finite coproducts.

In first-order logic, \(F\) is the object of all formulas. Let \(s:S\hookrightarrow F\) be the subobject of sentences. The pullback of \(c:P\to F\) along \(s\) gives
\[
c_S:P\times_F S\longrightarrow S.
\]
Its image \(m_S:T_S\hookrightarrow S\) is the theorem subobject of sentences. Restricting the inference construction to sentences before forming derivations would omit derivations through open formulas.

Assume \(m_S\) belongs to \(\mathcal M\). Its associated restriction idempotent is the partial identity
\[
t=[S\xleftarrow{m_S}T_S\xrightarrow{m_S}S]:S\rightharpoonup S.
\]
This morphism is obtained from the theorem subobject after deductive closure has been established. Fix a total negation morphism \(\nu:S\to S\). When the required restriction zero and join exist, the equations
\[
t\nu^*t=0_S,\qquad t\vee\nu^*t=1_S
\]
express disjointness and coverage of the theorem and refutation domains. In the concrete set and diagram interpretations below, these are respectively consistency and completeness of the sentence theories. The existing inseparability argument applies to these domains once its two reduction inequalities have been proved.

## 4. The three concrete applications

The total categories used for arithmetic, the cosheaf construction, and Miller's sequence are respectively
\[
\mathcal C_{\mathrm{rec}},\qquad
\mathcal C_{\mathrm{rec}}^J,\qquad
\operatorname{Tot}(K_r(\mathcal E_a)).
\]
Here \(\mathcal C_{\mathrm{rec}}\) has computably enumerable numerical carriers and total recursive morphisms, \(J=(1\leftarrow0\to2)\), and \(\mathcal E_a\) has partial numerical functions computed uniformly and independently of the binary representation of Miller's sequence \(a\).

These total categories have finite limits, finite coproducts, and image factorizations formed on their underlying sets. Their surjective morphisms are regular epimorphisms. For a surjection \(e:X\to Y\) and a morphism \(h:X\to Z\) constant on its fibers, the induced function \(k:Y\to Z\) can be computed by searching for \(x\in X\) with \(e(x)=y\) and returning \(h(x)\). This gives the coequalizer of the kernel pair of \(e\). Surjections are stable under pullback, proving regularity. The functor-category construction is componentwise; uniqueness of the induced functions gives naturality.

For the Miller category, the search uses the given binary representation. Its selected witness can depend on that representation, but its returned value cannot, because \(h\) is constant on the fibers of \(e\). This proves the factorization property without asserting that every surjection has a representation-independent section.

In the categories of numerical carriers, monomorphisms are precisely the injective morphisms. In the functor category they are the componentwise injective natural transformations. Their partial inverses on their images are computed by preimage search. For an injective morphism the witness is unique, so this also defines a representation-independent partial inverse in the Miller case. Thus all monomorphisms are admissible for the corresponding partial-map category.

Finite derivation trees give the initial algebras for the particular calculi used in these applications. For arithmetic and real closed fields, the rule objects have arities zero, one, and two: axioms, generalization, and modus ponens. The proof objects of sentences are then obtained by the pullback above. In the cosheaf application, evaluation at \(j\in\{0,1,2\}\) sends the categorical derivation and theorem objects to ordinary derivation sets and propositional theories; naturality makes the theorem sets a compatible family.

The syntactic recursion category \(S_T\) requires a separate analysis. Its morphism equalities express provability in the base theory \(T\). If an internal theorem domain is defined from the usual provability predicate for a computably enumerable \(T\supseteq\mathrm{PA}\), the equation excluding a sentence together with its negation expresses an internal consistency assertion. External consistency of \(T\) does not establish this equation. The numerical construction takes place in the partial-map category of recursive functions, where equality is extensional, rather than in \(S_T\).

## References

1. P. Aczel, *An Introduction to Inductive Definitions*, in J. Barwise (ed.), *Handbook of Mathematical Logic*, North-Holland, 1977, pp. 739–782. [Primary scan](https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf).
2. N. Gambino and M. Hyland, *Wellfounded Trees and Dependent Polynomial Functors*, TYPES 2003, Lecture Notes in Computer Science **3085**, Springer, 2004, pp. 210–225. [Author manuscript](https://eprints.whiterose.ac.uk/id/eprint/113158/1/gambino-hyland.pdf).
3. J. R. B. Cockett and S. Lack, *Restriction categories I: categories of partial maps*, Theoretical Computer Science **270** (2002), pp. 223–259. [Author copy](https://cspages.ucalgary.ca/~robin/FMCS/FMCS_06/RestrictionsI.pdf).
