# Dependency check of the incompleteness argument

Examined version: *Deduction and essential incompleteness in recursion categories*, 29 October 2026, commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. All 669 LaTeX lines and the PDF text were read. Page numbers below are printed page numbers. This report checks the logical dependencies of the note; historical claims about the Di Paola–Heller program belong to the separate source assessment.

## 1. The separation argument is independent of deductive closure

**Anchor:** p. 6, Theorem 4.2 and proof; source lines 421–454. The statement supplies a closure and calls $b$ a theory, but the proof uses neither $c_s$ nor $c_s(b)=b$.

The proof establishes the following more general assertion. Suppose that $p_+,p_-\le s$ are disjoint domains and that, for every complementary pair $(e_+,e_-)$ on $U$, a total $g:U\to U$ satisfies

$$
[\sigma(g\boxtimes1_U)]^*p_+=\pi_2^*e_+,
\qquad
[\sigma(g\boxtimes1_U)]^*p_-=\pi_2^*e_-.
$$

With the product and inverse-image properties used in the note and $0_U\ne1_U$, these domains have no complementary separator relative to $s$. No closure is required. It is not necessary even to assume that $p_-$ is the inverse image of $p_+$ along a distinguished $\nu$.

Indeed, given a separator $(d_+,d_-)$, put $\delta=\sigma\Delta_U$ and represent the complementary pair $(\delta^*d_-,\delta^*d_+)$. For the resulting $g$, put $\gamma=\langle1_U,g\rangle$ and $h=\delta g$. The equation $\sigma(g\boxtimes1_U)\gamma=h$ gives

$$h^*p_+=h^*d_-,\qquad h^*p_-=h^*d_+.$$

The separator inclusions force the two complementary domains $h^*d_+$ and $h^*d_-$ to be equal. Their meet and join then force $0_U=1_U$.

**Consequence:** closure and deductive rules specify a mathematically meaningful class of domains to which the separation result applies, but they are not premises used in its contradiction.

## 2. Closedness of extensions is also unnecessary for the contradiction

**Anchor:** pp. 6–7, Theorem 4.3 and proof; source lines 457–469.

For any domains $b\le t\le s$, monotonicity gives $\nu^*b\le\nu^*t$. If $(b,\nu^*b)$ is inseparable, the conditions

$$t\wedge\nu^*t=0_U,\qquad t\vee\nu^*t=s$$

make $(t,\nu^*t)$ a forbidden separator. This argument does not use $c_s(t)=t$ or $c_s(b)=b$.

This independence is realized by presentations allowed in §3: take $q=s$, $\ell=0_U$, and the unary rule $r=s:U\to U$. For every $a\le s$, its rule operation is $\operatorname{ran}(sa)=\operatorname{ran}(a)=a$, so all stages equal $a$. Their stable union is $a$, and $c_s$ is the identity. The theorem then applies to all domains meeting its remaining hypotheses. This is a valid specialization, not a counterexample to the theorem.

## 3. Exact roles of the categorical structure

| Ingredient | Role in the argument |
|---|---|
| Binary restriction products and total diagonals | Form $\delta$, $\gamma$, and the commuting square in Theorem 4.2. |
| Inverse image preserving meet, join, and relative top along total maps | Preserve complementarity in Theorem 4.2. |
| Ranges and finite stable unions | Establish the inverse-image and lattice facts used in Theorem 4.2. Once those facts are supplied directly, ranges do not occur in its proof. |
| Stable unions of generated increasing chains | Construct $c_q$ and $c_s$ in Theorem 3.1; do not occur in the separation contradiction. |
| Rule morphisms and fixed axioms | Determine the closure and identify its arithmetic fixed points; no compatibility with $\sigma$ or $\nu$ is used in Theorem 4.2. |
| Turing morphism $\tau$ | Described in §1 and supplied for the numerical category in §5; never used to derive Definition 4.1 or the separation result. |
| $\mathsf{Cons}$, $\mathsf{Th}$, and their natural inclusion | Organize presentations and closed inverse images; no morphism between presentations occurs in §4. |
| Distributivity | Used in inheritance of representation by consistent extensions, pp. 6–7; the preceding separation contradiction needs only the displayed lattice operations and preservation properties. |

## 4. These dependencies do not make the theorem set-theoretically vacuous

In the category of all partial maps of sets, every domain corresponds to an arbitrary subset. Any disjoint pair $p_+,p_-\le s$ has the relative complementary separator $(p_+,s\setminus p_+)$. Therefore a nontrivial object in that category cannot satisfy the representation hypothesis for such a pair. The hypothesis distinguishes the computability-restricted domain lattice from a full powerset lattice.

In the numerical instance, requiring domains to be c.e. and morphisms such as $\sigma$ to be recursive is consequential. Thus the absence of an explicit appeal to $\tau$ does not establish that all recursion-theoretic content has disappeared, that the proof is only an argument in unrestricted sets, or that the conditional theorem is false.

## 5. Inseparability is not effective inseparability

**Anchor:** p. 6, definitions preceding Definition 4.1 and the definition itself; source lines 398–418.

The note defines inseparability by nonexistence of a complementary separator. Definition 4.1 asserts existence of a representing total $g$ separately for each complementary pair. It supplies no uniform morphism taking indices of pairs or supersets to a witness. Theorem 4.2 proves the stated nonseparation property. No effective-inseparability conclusion is stated or established here.

## 6. Representation is an additional hypothesis, not the conclusion restated

**Anchor:** pp. 8–9, §5.2 and Corollary 5.2; source lines 602–655.

The arithmetic proof constructs a jointly recursive substitution map from syntax. Given strong numeralwise definability and consistency, a constant representing map gives the two exact inverse-image equations. This is a separate verification of the representation hypothesis; it does not use an incompleteness conclusion. Nothing in this argument justifies calling the hypothesis circular.

The remaining limitation is concrete: the note does not derive this hypothesis from a Turing morphism, relate it to an intrinsically constructed inseparable pair, or establish it for a general nonnumerical class of presentations. It does not prove the strong numeralwise representability theorem for $Q$ or PA. Their mention on p. 8 concerns their theorem sets being fixed points of the closure.

## 7. Result of the correctness check

No theorem-breaking defect was found in this pass through the range identities, union arguments, closure construction, presentation morphisms, separation proof, or conditional arithmetic corollary. This is an assessment of the displayed arguments, not a formal verification. The abstract's last sentence requires the same c.e. restriction on extensions as Corollary 5.2; the independent writing review treats that wording issue.

The strongest confirmed structural limitation is that the incompleteness contradiction does not use deductive closure or the Turing morphism. This establishes a missing connection relevant to a stronger claim that the whole recursion-theoretic and deductive apparatus drives the result. It does not refute the conditional theorem or, without a precise historical criterion, prove that every interpretation of the Di Paola–Heller program has failed.
