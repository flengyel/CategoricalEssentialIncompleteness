# Review: the existing S_T construction and effective observations

The valid unprimed construction S_T supplies a short route: the program
indices proved equal to identity and those proved equal to zero form a
recursively inseparable pair. Extension quotients enlarge both sets.
Completeness would decide membership in the first set by proof search.

Date: 29 October 2026. This review compares the constructions in the current
and preceding discussions with the valid unprimed syntactic categories.
It records this classical benchmark and the data to axiomatize. It makes no
claim of a new arithmetic incompleteness theorem or of a completed general
Di Paola–Heller construction.

## 1. Start from the valid categories

For a consistent c.e. extension T of PA, use the established category S_T.
Its objects are the formal numerical types generated from omega by binary
products and tagged coproducts. They have fixed effective codings. Arrows
are typed program indices modulo **one uniform T-proof** of Kleene equality:

\[
 e\equiv_T f\quad\Longleftrightarrow\quad
 T\vdash\forall x\,\forall y\,
       (G_e(x,y)\leftrightarrow G_f(x,y)).
\]

Here G_e(x,y) is the Sigma_1 output relation obtained by existentially
quantifying a terminating trace in a primitive recursive computation-trace
predicate for program e.
The graph compilers for identity, composition, restrictions, products,
coproducts, and the chosen Turing morphism have their specifications provable
in PA. This is the valid unprimed construction of Montagna and
Di Paola–Montagna; it does not use the failed pointwise quotient S'_T.
See the exact source locations and reconstructed laws in
[SYNTACTIC_SOURCE_CHECK.md](SYNTACTIC_SOURCE_CHECK.md).

A domain is represented by a partial identity with a Sigma_1 domain
predicate D(x). Its order is uniform provable implication:

\[
 [D]\le[E]\quad\Longleftrightarrow\quad
 T\vdash\forall x(D(x)\to E(x)).
\]

Meet, bottom, top, and binary join are conjunction, false, true, and
disjunction in this order. Restriction totality of a program means that
T proves its universal halting. These are pointed p-recursion categories
in Heller's 1990 class; they are not assumed dominical.

Theory inclusion supplies a covariant quotient functor

\[
 Q_{T,T'}:S_T\longrightarrow S_{T'},\qquad
 Q_{T,T'}(X)=X,\qquad Q_{T,T'}([e]_T)=[e]_{T'}.
\]

It is well-defined because every T-proof is a T'-proof. The fixed program
compilers show directly that Q preserves identities, composition,
restrictions, zero, products, coproducts, ranges, binary domain joins,
and the chosen Turing morphism. It is surjective on each hom-set.
For T⊆T'⊆T'', the equality Q_{T',T''}Q_{T,T'}=Q_{T,T''} holds on
objects and representatives; Q_{T,T} is the identity.

More explicitly, the chosen Turing morphism is
\(\tau_T:\omega\times\omega\rightharpoonup\omega\).
For every arrow \(f:X\times\omega\rightharpoonup\omega\), the
PA-formalized s-m-n theorem supplies a restriction-total parameter map
\(p:X\to\omega\) such that
\[
 f=\tau_T\circ(p\times1_\omega).
\]
The same program represents the parameter map after extension, and Q
preserves its totality and this equation. This is the Turing-morphism
property being used, not merely the existence of an interpretation of codes.

The canonical diagonal output pair is represented by the same programs
in every S_T. A complemented pair of domains has a dovetailing case
program whose totality T proves from its covering equation. Hence the
Turing diagonal argument proves the canonical pair inseparable in every
consistent S_T. The quotient functors preserve this particular pair.
This assertion does not require preservation of every inseparable pair.

## 2. Identity and zero in the effective presentation

Fix unary program codes i and z for identity and the nowhere-defined map.
For unary program indices e,f, let Eq(e,f) denote the closed arithmetic
sentence expressing their uniform graph equality as in Section 1; code
parameters in this sentence are substituted as numerals. Put

\[
 I_T=\{e:T\vdash\operatorname{Eq}(e,i)\},\qquad
 Z_T=\{e:T\vdash\operatorname{Eq}(e,z)\}.
\]

Equivalently, these are the fibers of identity and zero under the set map
\(q_T:\mathbb N\to S_T(\omega,\omega)\), \(e\mapsto[e]_T\).
They are c.e. when T is c.e. PA proves that identity and zero have different
graphs, so consistency gives \(I_T\cap Z_T=\varnothing\).
The map q_T is a presentation map of sets; it is not an asserted functor
from the extensional category of partial recursive maps.

Let \((\varphi_n)_{n\in\mathbb N}\) be the PA-formalized acceptable
program numbering used by the chosen Turing morphism. Fix its diagonal pair
\[
 A=\{n:\varphi_n(n)\downarrow=0\},\qquad
 B=\{n:\varphi_n(n)\downarrow=1\}.
\]
It is recursively inseparable: a recursive separator C would give a total
recursive function returning 1 on C and 0 outside C. At an index k of that
function, either choice of membership in C contradicts separation.

Write \(\alpha(x)\) and \(\beta(x)\) for its Sigma_1 output predicates.
Choose a primitive recursive compiler r such that program r(n), on input x,
simulates \(\varphi_n(n)\), returns x if the output is 0, and otherwise
remains undefined. PA verifies the compiler specification uniformly:
\[
 G_{r(n)}(x,y)\leftrightarrow(\alpha(n)\land y=x).
\]
This notation abbreviates the formalized primitive recursive compiler;
for a fixed external n the corresponding code and parameter are numerals.
If n belongs to A, PA verifies its finite terminating trace and proves
\(\operatorname{Eq}(r(n),i)\). If n belongs to B, PA verifies its
output-1 trace; machine determinism gives \(\neg\alpha(\bar n)\),
and hence PA proves \(\operatorname{Eq}(r(n),z)\). Thus
\[
 r(A)\subseteq I_{\mathrm{PA}},\qquad
 r(B)\subseteq Z_{\mathrm{PA}}.
\]
The inverse image under r of a recursive separator for the right-hand pair
would separate A and B. Consequently \((I_{\mathrm{PA}},Z_{\mathrm{PA}})\)
is recursively inseparable. Only the displayed inclusions are needed;
inverse-image equalities are not claimed.

For T contained in T', the actual extension quotient satisfies
\(q_{T'}=Q_{T,T'}\circ q_T\). Since Q preserves identity and zero,
\[
 I_T\subseteq I_{T'},\qquad Z_T\subseteq Z_{T'}.
\]
Every consistent c.e. extension T of PA therefore gives a disjoint c.e.
enlargement of the fixed inseparable pair, and its pair is inseparable too.
If T were complete, parallel proof search for Eq(e,i) and its negation
would decide I_T. That recursive set contains I_T and avoids Z_T, giving
the forbidden separator. Completeness is not being used to assert
\(I_T\cup Z_T=\mathbb N\): many programs are neither identity nor zero.

The direction can be stated without an unspecified backwards arrow functor.
Let Rec be the category of partial recursive maps on the effectively coded
numerical types, and let Pair(Rec) have objects (X,a,b) consisting of two
disjoint c.e. domains on X. Its arrows
\(u:(X,a,b)\to(Y,c,d)\) are total recursive maps satisfying
\(a\subseteq u^{-1}(c)\), \(b\subseteq u^{-1}(d)\); composition and
identities are those of Rec. Let Ext_con(PA) be the poset category of
consistent c.e. extensions of PA, ordered by theory inclusion. Then
\[
 \mathcal I:\operatorname{Ext}_{\mathrm{con}}(\mathrm{PA})
 \longrightarrow\operatorname{Pair}(\mathrm{Rec}),\qquad
 T\longmapsto(\omega,I_T,Z_T),\qquad
 (T\subseteq T')\longmapsto1_\omega
\]
is a covariant functor. The two displayed inclusions verify its arrow
action; the identity maps verify its functor laws. The compiler r is a
fixed arrow \((\omega,A,B)\to\mathcal I(T)\) for every T. Separators
pull back along these total arrows in the required backwards direction.

## 3. A backwards map on domains supplied by the presentation

Domains on omega in Rec are c.e.
sets, identified with their partial identities. For a domain [D] of S_T,
define

\[
 E_T([D])=\{n\in\mathbb N:T\vdash D(\bar n)\}.
\]

Proof enumeration makes this a c.e. domain, uniformly from a representative
and an enumeration of the axioms of T. For c.e. axiom presentations, finite
proof objects may include witnesses for the enumerated axioms; ordinary
proof enumeration is sufficient here.

Uniform provable equivalence gives equal sets E_T([D]), so this operation
is well-defined on the valid quotient. It is a covariant monotone map

\[
 E_T:\mathsf D_{S_T}(\omega)\longrightarrow
              \mathsf D_{\mathrm{Rec}}(\omega).
\]

Both posets may be regarded as thin categories; inclusions are the arrow
action. E_T preserves top and finite meets by elementary proof operations,
and preserves bottom by consistency. For an extension T⊆T',

\[
 E_T(e)\le E_{T'}(Q_{T,T'}e).
\]

This is an inequality, not an asserted equality. An extension may prove
additional numeral instances. Binary-join preservation is not used: a
consistent classical theory may prove a disjunction without proving either
disjunct.

There is also an equation-only description. Let kappa_n:omega→omega
be the total constant program with value n. For a domain e,

\[
 n\in E_T(e)\quad\Longleftrightarrow\quad
 e\kappa_n=\kappa_n\quad\text{in }S_T.
\]

The equivalence follows from the PA-verified partial-identity and constant
program specifications. It requires no terminal object and introduces
no pointwise equivalence relation on arrows.

E_T is a map on domain posets. No functor on all arrows S_T→Rec is claimed.
The proof below does not need one.

## 4. The same obstruction through domain observations

Retain A,B and their output predicates alpha(x),beta(x) from Section 2.
They represent the canonical domains a_T,b_T of S_T. PA proves

\[
 \forall x\,\neg(\alpha(x)\land\beta(x)).
\]

Every actual finite computation can be verified in PA. Therefore

\[
 A\subseteq E_T(a_T),\qquad B\subseteq E_T(b_T).
\]

Consistency of T and the displayed disjointness theorem imply that the
two right-hand c.e. domains are disjoint. They are thus disjoint
enlargements of the original inseparable pair and are themselves
recursively inseparable. No equality E_T(a_T)=A is asserted.

To display the forbidden separator under hypothetical completeness, put

\[
 C_T=\{n:T\vdash\alpha(\bar n)\},\qquad
 N_T=\{n:T\vdash\neg\alpha(\bar n)\}.
\]

Both are c.e. Consistency gives C_T∩N_T=∅. Computation verification gives
A⊆C_T. For n∈B, PA proves \(\beta(\bar n)\), so the uniform disjointness
theorem gives \(\mathrm{PA}\vdash\neg\alpha(\bar n)\), and hence B⊆N_T.
If T were complete, then
C_T∪N_T=N. The complementary c.e. domains C_T,N_T would separate A,B,
contradicting inseparability. Equivalently, parallel positive/negative
proof search would decide a recursive separator.

Only completeness for the displayed family \(\alpha(\bar n)\) is needed. The
argument applies to every consistent c.e. T⊇PA using the same programs
and predicates. It uses consistency, not soundness or omega-consistency.
In particular it does not require a separate Rosser comparison formula:
the canonical machine-output pair already has PA-provable disjointness.

With the categories defined in Section 2, there is another covariant functor

\[
 \mathcal O:\operatorname{Ext}_{\mathrm{con}}(\mathrm{PA})
 \longrightarrow\operatorname{Pair}(\mathrm{Rec}),\qquad
 T\longmapsto(\omega,C_T,N_T),\qquad
 (T\subseteq T')\longmapsto1_\omega.
\]

Both proof domains increase along extensions, verifying the arrow
inequalities. Identity and composition are inherited from Rec. The
identity on omega gives a reduction (omega,A,B)→O(T) for every T.
This is an actual instantiation of the pair-transport mechanism, extracted
from the S_T presentations and their extension quotients.

## 5. What the construction suggests axiomatizing

The PA example distinguishes the following data rather than identifying
all of them with the abstract category S_T:

1. **A family of computational presentations.** The category associated
   with a theory has a genuine composition congruence, restriction
   structure, a chosen Turing morphism, and specified computational program
   constructions. Theory extensions induce quotient functors preserving
   these constructions and the distinguished diagonal pair.
2. **Effective proof observations of computational equations.** In the
   PA benchmark their ambient category is the fixed category Rec. For a
   uniform family of arithmetic sentences Phi(n) expressing computational
   equations, define
   \(O_T^+(\Phi)=\{n:T\vdash\Phi(\bar n)\}\) and
   \(O_T^-(\Phi)=\{n:T\vdash\neg\Phi(\bar n)\}\).
   These are c.e. domains of Rec and both increase under theory extension.
   Taking Phi(e)=Eq(e,i) gives the direct identity/zero argument;
   taking Phi(n) to express e kappa_n=kappa_n gives the domain argument.
   For the latter, both observations are invariant under equality of
   domains in S_T; the positive observation is monotone in the domain and
   the negative one is antitone. Logical negation is used in the
   arithmetical proof query: no negated Sigma_1 domain is assumed to exist
   internally in S_T.
3. **Compatibility with finite computation.** The positive observations
   contain the first canonical diagonal domain, and the negative
   observations contain the second, possibly after inverse image along a
   fixed total compiler. In Section 2, Z_T is contained in
   \(O_T^-(\operatorname{Eq}(-,i))\), by PA-provable inequality of
   identity and zero. These inclusions follow from finite trace verification
   and uniformly proved program specifications.
4. **The logical connection.** Consistency makes opposite observation
   domains disjoint; completeness covers the parameter object by their
   union. These conditions are verified from actual deduction in the
   example, not assigned arbitrarily to a presentation.

A nonnumerical axiom system should replace numeral-indexed proof
observations by explicitly typed, parameterized computational proof
objects and their selected conclusion domains. Their existence and
compatibility must be proved in the proposed class of categories. The
PA calculation establishes the benchmark and identifies the required
operations; it does not construct these objects in every recursion category.

## 6. Boundaries that matter to this review

- **The valid quotient is retained.** S'_T and all quotients by separate
  proofs at each standard input are excluded. The user's current
  *Pointwise provable equality and the failure of composition*, v37,
  explicitly leaves unprimed S_T unaffected.
- **External totality is not internal totality.** Completeness would make
  the separator search total in Rec. It need not make that program
  T-provably total, so no internal total separator in S_T is inferred.
- **External consistency is not a consistency proof in T.** The argument
  uses PA-provably disjoint output domains. It does not assert that T's
  own internal theorem/refutation domains are disjoint in S_T; that
  would require an internal consistency statement.
- **Effectivity is essential.** Completeness alone cannot make all domains
  of S_T complemented: for true arithmetic Th(N), uniform provable
  equality is ordinary extensional equality, so the corresponding category
  is Rec and still has inseparable pairs. Th(N) is not c.e., so the
  proof-enumeration step used above is unavailable.

## 7. Which earlier constructions are needed here?

| Construction | Role after starting from S_T |
| --- | --- |
| Turing diagonal and explicit binary case distinction | Supplies the distinguished computational pair; the case operation is verified directly in S_T. |
| The current pair-transport theorem | Supplies the formal implication from disjoint computational enlargements to essential incompleteness. |
| The signed-literal adjunction | Explains the separator obstruction, but does not supply the PA-specific deduction comparison. |
| Polynomial finite-proof algebras and finite-stage unions | Useful for constructing deductive syntax from an arbitrary recursion category. PA already supplies an effective syntax and calculus, so these are not needed for this benchmark. |
| Range completion, regularity, finite-worklist iteration | Not needed for the S_T-to-Rec proof observations. Their conditional construction results remain available for genuinely nonnumerical cases. |
| Three-point computational cosheaves | A later test of whether the abstract proof-observation data can be constructed without reducing the entire argument to numerical syntax. |
| Presheaf or Boolean completions | Do not supply the required effective observation map merely by adding subobjects or complements. Their existing obstructions remain. |
| Arithmetic-universe introspection comparison | Starts from different data and supplies no comparison for this S_T construction. |

The preceding discussion's free Boolean-category and represented-Boolean-
quotient proposals do not supply an additional map needed by the proof
above. Their reported obstructions are not re-proved in this review.

## Source scope

The relevant primary scans and current FailureOfComposition v37 source
were checked. The earlier chat was consulted for scope and exclusions;
source claims used in the new argument are grounded in the primary-source
record. The previously proved finite-stage and cosheaf constructions are
reused without a new full audit. No Lean development was run or changed.
