## (A) Kill-shots / hard blockers

No fatal mathematical defect was established in this scoped terminology and definition-order review. The quantified interpretation of the axiom schemes is substantially ambiguous as written; see M05-1.

## (B) Major weaknesses

### M05-1 — Formula parameters are assigned to a functor rather than to a stated set of formulas

**Anchor:** PDF p.16, §8.3, source lines 1251–1263: “Their parameters range over $S$.” The schemes immediately precede this sentence.

**Failure mode:** `ill_typed`, `ambiguous`. **Evidence:** `structural_argument`, `absence_in_text`.

The manuscript has introduced $S$ as an object of $\mathcal E=\mathcal C_{\mathrm{rec}}^J$ (lines 1237–1244). It is a functor, not one set whose elements may be substituted into these schemes. No convention for generalized elements or componentwise interpretation of the displayed variables is declared here. The required componentwise construction occurs in Appendix B, where the constructors receive explicit component indices. Reading that later construction repairs the intended meaning, but it does not make the present statement typed as written. “Indexed by the split objects of $a$ positively and $b$ negatively” likewise leaves the actual axiom morphisms unstated at this point.

**Downstream impact:** The axiom family and the rule-closed subfunctors that define extensions in Theorem 8.2 do not have a declared interpretation until the appendix. **Severity:** major exposition/self-containedness defect, locally repairable; no counterexample to the intended construction is claimed.

**Repair:** Introduce the component notation before the schemes:

> For $j=0,1,2$, write $S_j=S(j)$, and let $\nu_j$ and $\Rightarrow_j$ be the components of the negation and implication morphisms. At component $j$, the logical axiom schemes, with $\alpha,\beta,\gamma\in S_j$, are …

Use $\nu_j$ and $\Rightarrow_j$ in those displays, and state modus ponens at component $j$. Define $A,B\subseteq V$ as the c.e. subfunctors on which $a,b$ are partial identities; the additional axioms at component $j$ are $\theta_j(x)$ for $x\in A_j$ and $\nu_j\theta_j(y)$ for $y\in B_j$. This also agrees with the already defined $A_i,B_i$ for $i=1,2$. An alternative internal formulation would have to type the axiom morphisms explicitly; no unstated generalized-element convention should be relied upon.

## (C) Minor issues

### C05-1 — Unnecessary terminology for evaluation and total morphisms

**Anchor:** PDF pp.14–15, §8.2, source lines 1116, 1151, 1166–1185: “Endpoint functors,” “endpoint probe,” “the point $p_y$,” “observed carrier.”

**Failure mode:** `ambiguous`, `inconsistent_use`. **Evidence:** `absence_in_text`, `structural_argument`.

The heading includes $E_0$, although the surrounding prose calls only indices 1 and 2 “endpoints.” “Endpoint probe” is explicitly defined, so it is not missing a definition; it is an unnecessary paper-specific name for a total morphism $H_i\to Y$. Calling such a morphism “the point” also introduces an interpretation without declaring it. “Observed carrier” adds another local name for the displayed subset of $Y_i$.

**Repair:** Use the heading “Evaluation functors.” Replace “endpoint” by “component $i$, for $i=1,2$” where the distinction matters. Write “For each $y\in Y_i$, let $p_y:H_i\to Y$ be the total morphism with component $i$ equal to $*\mapsto y$.” Refer thereafter to these total morphisms, and introduce $|e|_i$ simply as the subset on which $E_i(e)$ is defined. The formulas for $\Phi_i$ and $|e|_i$ can remain.

**Downstream impact:** Prevents unsupported terminology from obscuring the evaluation construction. **Severity:** minor; wording repair.

### C05-2 — An unnamed forgetful functor is used in a comparison

**Anchor:** PDF p.15, §8.2, source lines 1181–1184: “identify $\Phi_i$ with the underlying partial-set functor of $E_i$.”

**Failure mode:** `missing_definition`, `ambiguous`. **Evidence:** `absence_in_text`.

$E_i$ has target $\mathcal K$, whereas $\Phi_i$ has target $\Pfn$. “Underlying partial-set functor of $E_i$” is not a typed functor name or a previously declared composition. The displayed hom-sets and the component sets are related by bijections, not literally equal sets.

**Repair:** Define $U:\mathcal K\to\Pfn$ as the functor sending a c.e. numerical set to its underlying set and a partial recursive function to the same partial function. Then write “The bijections $p_y\mapsto y$ give a natural isomorphism $\Phi_i\cong U E_i$.” The naturality follows from the definition of postcomposition already given.

**Downstream impact:** Makes the compared functors' targets and the comparison relation explicit. **Severity:** minor; local typing repair.

### C05-3 — Undefined or unnecessary descriptions of the propositional construction

**Anchor:** PDF pp.15–16, §8.3, source lines 1236–1244 and 1265–1277: “classical presentation,” “covariant polynomial,” “split subfunctor.”

**Failure mode:** `ambiguous`, `missing_definition`. **Evidence:** `absence_in_text`.

“Classical presentation” has no declared mathematical meaning. The displayed $P$ is a polynomial functor, but the noun “functor” has been omitted. The general restriction splitting is defined in §2, and a c.e. subfunctor is defined in §8; neither definition introduces “the split subfunctor” of a restriction idempotent. Here that phrase refers to the subfunctor on which the partial identity is defined, not to an extra kind of subfunctor.

**Repair:** “We construct a theory in classical propositional logic from the disjoint restriction idempotents $a,b$. Define the polynomial functor $P:\mathcal E\to\mathcal E$ by …”. Replace “split subfunctor of $t$” by “subfunctor on which $t$ is defined,” or introduce that subfunctor explicitly once and use its name consistently. These are local terminology repairs; the existing initial-algebra equation is a sufficient definition of initiality here.

**Downstream impact:** Removes ambiguity from the object on which rule closure is imposed. **Severity:** minor apart from the separate typing defect M05-1.

### C05-4 — “Global value” obscures the change from a functor on $J$ to a cosheaf on $X$

**Anchor:** PDF p.17, Appendix A.1, source lines 1368–1386: “the global value of the product of $Y$ and $Z$,” “whose global value has two elements,” “its value at $X$.”

**Failure mode:** `ambiguous`. **Evidence:** `structural_argument`.

$Y$, $Z$, and $H$ are functors on $J$; $X$ is not an object of $J$. The values at $X$ belong to their associated cosheaves under Proposition A.1. This association is available, but “global value” is not defined and suppresses exactly the distinction used by the counterexample.

**Repair:** Write “The cosheaf associated with $Y\times Z$ has value … at $X$.” Refer likewise to “the value at $X$ of the cosheaf associated with $H$.” Keep the example: the distinction is substantive mathematics, not a dispensable disclaimer.

**Downstream impact:** Prevents an ill-typed reading of evaluation at $X$ and preserves the reason products are formed in $\mathcal E$. **Severity:** minor; local exposition repair.

### C05-5 — Finite-set and slice notation is explained after use

**Anchor:** PDF p.17, Appendix A.1, source lines 1382–1387 and 1401–1405: $H=(1\leftarrow0\to1)$, $2\to1$, followed by “Here $0$ and $1$ denote empty and singleton carriers”; $\mathcal E/Y_k$, followed by its definition.

**Failure mode:** `missing_definition` (late, not absent). **Evidence:** `absence_in_text`.

The meanings of $0$ and $1$ as sets are declared after the example, and $2$ as a two-element set is not explicitly included in that declaration. The meaning of the slice notation is also given after its display. These are conventional notations; the issue is the requested reading order, not mathematical unfamiliarity.

**Repair:** Move the finite-set convention before the example, including $2$, or define $H(0)=\varnothing$ and $H(1)=H(2)=\{*\}$ directly. Move the existing explanation of $\mathcal E/Y$ before the definition of extensivity.

**Downstream impact:** Local reading-order clarity. **Severity:** minor; relocation suffices.

## (D) Cross-section consistency failures

### D05-1 — $\tau_0$ is used before its relation to $\tau$ is declared

**Anchor:** PDF p.15, §8.2, source lines 1192–1198: “$\tau_0(p,-)$ for a fixed central program $p$.” Later definition: Appendix A.4, source line 1734, “Define $\tau_0:T_0\to V_0$ …”.

**Failure mode:** `missing_definition`, `ambiguous`. **Evidence:** `absence_in_text`.

$\tau$ and the evaluation functors have already been introduced, but the notation $\tau_0$ has not. The present passage also leaves the type of the fixed parameter $p$ implicit. The later appendix gives the component representation, using $\tau_0$ both for its total value map on $T_0$ and for the associated partial function.

**Repair:** Before its first use, define $\tau_j:=E_j(\tau):V_j\times V_j\rightharpoonup V_j$ for $j=0,1,2$. In the example write “for a fixed $p\in V_0$” and use $r_1^V$ for the component projection of the displayed output. In the appendix, make clear when the same notation is restricted to the c.e. set $T_0$.

**Downstream impact:** Makes the non-preservation example intelligible without importing its notation from the appendix. **Severity:** minor; local definition repair.

### D05-2 — The coding and numbering for the chosen Turing morphism should be one choice

**Anchor:** PDF p.14, Proposition 8.1 proof, source lines 1148–1155, “Fix a recursive bijection … and an acceptable numbering”; Appendix A.4, source lines 1668–1674, independently begins “Fix recursive bijections … We use an acceptable numbering …”.

**Failure mode:** `ambiguous`, `inconsistent_use`. **Evidence:** `structural_argument`.

The formula in Proposition 8.1 is a formula for the particular $\tau$ constructed in the appendix. It is not invariant under an arbitrary fresh choice of coding and numbering while $\tau$ remains fixed. Identical symbol names suggest the intended common choice but do not state it.

**Repair:** State in §8.2 that these are the coding and numbering used to construct $\tau$ in Appendix A.4; in the appendix explicitly reuse them and extend the tuple codings to the other arities. The standard term “acceptable numbering” itself is not an invented term, and its needed specialization property is stated later.

**Downstream impact:** Removes ambiguity about which partial function the component formula denotes. **Severity:** minor; choice-consistency repair.

## (E) Acceptance conditions, non-negotiable

1. Type the axiom schemes and their parameters componentwise in §8.3, or give an explicit internal formulation with typed axiom morphisms. Endpoint: M05-1 is removed without changing the theory or weakening Theorem 8.2. Failure blocks acceptance on the requested self-containedness axis.
2. Define $\tau_j$ before the component-0 example and use one declared coding/numbering for its construction and its component formula. Endpoint: D05-1 and D05-2 have explicit local definitions. Failure leaves the requested notation audit unresolved.
3. Replace the unnecessary local terminology in C05-1/C05-3 and type the comparison functor in C05-2. Endpoint: the construction is expressed using the already defined categories, morphisms, and subfunctors. Failure leaves the requested terminology audit unresolved.
4. Identify evaluations at $X$ as evaluations of the associated cosheaf and move the existing finite-set/slice conventions before use. Endpoint: C05-4/C05-5 are repaired while retaining the substantive product/subobject counterexample.

## (F) Not checked / uncertainty log

**Coverage:** Every sentence, displayed formula, heading, and proof in baseline source lines 1116–1479 was read. This covers blocks B096–B122. The source has no comments in this interval. Lines 1–295 and 979–1115 were read as prerequisites. The whole baseline was searched for the first declarations of the queried terms and symbols; relevant later passages and the prior definition of $\operatorname{Pair}(\mathrm{Rec})$ were read. PDF page anchors were checked against the extracted baseline page text.

**Adequately introduced notation and terms:** $\mathcal K$ is defined before $E_j$; $E_j$ has object and morphism assignments before Proposition 8.1; $\Phi_i$ has its source, target, object assignment and partial morphism assignment before its functor laws are used; $|e|_i$ is defined by a set before Theorem 8.2; $\zeta$, $q_0,q_1,d,a,b,A_i,B_i$ are introduced before their uses; $P$, its initial algebra, $\theta$, $\nu$, $\mathrm{Prf}$, $c$, and $t_0$ are declared before the extension theorem. $\operatorname{Pair}(\mathrm{Rec})$ is defined at lines 927–931 before the present section. Regular epimorphism, regular category, regular image and kernel pair are defined before Proposition A.2. $H_1,H_2$ are introduced before their hom-sets; $H_0$ is introduced at its first use in Appendix A.1. $\operatorname{CoSh}(X,\mathbf{Set})$ is recognizable notation for the category whose objects and morphisms have just been described, rather than an unexplained new construction.

**Outline and mathematical function:** §8.2 defines evaluation functors, proves their preservation and Turing properties, and compares them with partial functions on total morphisms from $H_i$. §8.3 constructs the propositional theory and proves inseparability and incompleteness of its extensions. Appendix A.1 proves the cosheaf/functor equivalence, explains the effect on products/subobjects, defines regularity and extensivity, and proves the required structure of $\mathcal E$.

**Source principle:** Knuth–Larrabee–Roberts, *Mathematical Writing*, §1, point 11 requires variables to be defined at least informally at first introduction; points 14 and 17 support consistent notation and left-to-right readability. These were read in the supplied excerpt. The preference to remove unnecessary local terms is the stated editorial constraint, not a claim that every such phrase is universally forbidden mathematical vocabulary.

This is an author-side, scoped exposition audit. It does not certify the entire paper's mathematics or novelty, reread the cited literature, or rerun compilation. The proof of the underlying syntactic and nonnumerical constructions was not independently reconstructed here. No main-source changes were made.

Strongest confirmed blocker: the untyped formula parameters in M05-1. Strongest suspected unconfirmed blocker: none identified in this scope. Most important unchecked matter: a new complete correctness audit of the nonnumerical Turing and proof constructions. The requested exposition diagnosis does not depend on unavailable material. Final recommendation: reject on the requested self-containedness/exposition axis until M05-1 is repaired; this is not a claim that the intended theorem is false.
