# Completion and preservation of computational domains

Exploratory research record, 29 October 2026. Sections 1–2 are included in the
reviewed supplement. Section 3 records an elementary finite-set argument;
Section 4 is a proposed sheaf construction with unproved obligations and is
not a result of the supplement.

Heller, *An existence theorem for recursion categories* (1990), §10, Example 5,
p.1267, already constructs a recursion category from partial maps of simplicial
sets whose diagonal has no range. The selected-presheaf calculation below is
a check of one proposed completion, not a discovery of the general possibility
of range failure.

## 1. Selected-subobject preservation

Let R be a small restriction category, C=Tot(Split_r(R)), and M the class of restriction monics in C. A monomorphism μ:P→Q in the presheaf category PSh(C)=Set^(C^op) is selected when, for every γ:yX→Q, its pullback along γ is isomorphic over yX to ym:yA→yX for some m:A→X in M. Write Mhat for this stable class.

**Proposition.** Yoneda induces, naturally in X, an order isomorphism

Sub_M(X) ≅ Sub_Mhat(yX).

It preserves and reflects the least and greatest selected subobjects, finite meets, and every join that exists in the selected-subobject posets. Consequently an inseparable pair remains inseparable when separation is defined using Mhat-subobjects of yX.

**Proof.** Yoneda preserves pullbacks of M-maps and takes M into Mhat. Conversely, apply the defining condition for μ:P→yX to γ=1_yX. Its pullback is μ itself, so μ is isomorphic to ym for an M-subobject m of X. Full faithfulness of Yoneda identifies factorizations between these monos, hence their order. The inverse assignments commute with pullback by its universal property. An order isomorphism preserves and reflects all existing order operations, including the equations defining complementary separators. ∎

This does not identify Mhat with all presheaf monomorphisms and does not assert that the presheaf partial-map category has ranges.

**Verified primary source:** Richard Garner and Daniel Lin, *Cocompletion of restriction categories*, arXiv:1610.07164, §3.1, fetched PDF pp.5–6 (definition of the selected class), Lemma 9, fetched PDF pp.6–7 (selected-subobject isomorphism). URL https://arxiv.org/pdf/1610.07164 . Published bibliographic record: *Theory and Applications of Categories* 35 (2020), no.22, 809–844, https://tac.mta.ca/tac/volumes/35/22/35-22abs.html . The numbered anchors above were checked in the fetched arXiv PDF, not inferred from published pagination.

## 2. A concrete failure of ranges in that completion

Let C_rec=Tot(Split_r(R_rec)); objects are c.e. subsets of finite powers of N and maps are computable functions total on their sources. Let 1 be a singleton object. Let A⊆N be non-c.e. Form in PSh(C_rec) the copairing

F_A : coproduct_(n∈A) y1 → yN

of the Yoneda images of the constant maps n:1→N. Regard it as a total map in Par(PSh(C_rec),Mhat).

**Proposition.** The map F_A has no restriction range in Par(PSh(C_rec),Mhat).

**Proof.** If its range existed, its selected mono into yN would, by Proposition 1, be isomorphic to y(i_T):yT→yN for a c.e. subset T⊆N. Each summand n:1→N factors through this range, so Yoneda and the concrete numerical category give A⊆T.

For each k∉A, every summand factors through the c.e. co-singleton N\{k}. By the coproduct property, F_A itself factors through y(N\{k})→yN. Leastness of the restriction range forces T⊆N\{k}. Thus T⊆A. Consequently T=A, contradicting the choice of A. ∎

Only the least-domain property of a restriction range is used. Ordinary presheaf-image preservation, global-point preservation, and a claim about complements of arbitrary presheaf subobjects are unnecessary. Enlarging the class of admissible subobjects can remove this particular obstruction, but then the original selected-domain isomorphism must be re-established rather than assumed.

## 3. Finite propositional entailment criterion

This is a proved finite-set lemma; its sheaf interpretation remains a construction target.

Fix disjoint subsets A,B of a set U, a finite propositional formula φ with its atom occurrences numbered 1,...,n, and labels u_1,...,u_n∈U. The ambient axiom set contains P_u for u∈A and ¬P_u for u∈B. For a partition π of {1,...,n}, write φ_π for the formula whose i-th occurrence is the variable x_[i]. Choose subsets I,J⊆{1,...,n}. Retain the triple (π,I,J) when

( conjunction_(i∈I) x_[i] and conjunction_(j∈J) ¬x_[j] ) ⇒ φ_π

is a propositional tautology. A retained triple is satisfied by the labels when u_i=u_j within each block of π, u_i∈A for i∈I, and u_j∈B for j∈J.

**Lemma.** The labelled formula φ is provable from the ambient axiom set if and only if at least one retained triple is satisfied.

**Proof.** A satisfied triple gives the indicated literal premises as axioms; substituting the atom labels into the tautology gives the conclusion by finite propositional deduction. The labels may satisfy more equalities than π records, because substitution preserves tautologies.

Conversely, partition occurrences by their actual equalities. Among the resulting finitely many atoms, assign those in A true and those in B false. The remaining atoms are free. If φ is provable, soundness says it holds for every completion of this partial assignment: every such assignment extends to all U by setting any additional A-atom true and all remaining unassigned atoms false. Hence the conjunction of the assigned literals implies φ tautologically. Choose I,J representing these assigned classes. This is a satisfied retained triple. ∎

There are only finitely many triples. No disequalities are required.

For total maps u_i:X→U and disjoint computational domains a,b, this suggests the domain

e_φ = finite join_(retained π,I,J) [ (meet_(i~πj) Eq(u_i,u_j)) ∧ (meet_(i∈I)u_i^*a) ∧ (meet_(j∈J)u_j^*b) ].

When equalizer domains exist and finite domain joins are stable, this is a computational domain. In a range restriction category with binary restriction products and the universal range property, Eq(u_i,u_j) can be formed as <u_i,u_j>^*ran(Δ_U): universal range gives π_1 ran(Δ_U)=π_2 ran(Δ_U), and the diagonal/pairing identities verify the equalizer property.

## 4. Finite-cover sheaf candidate and exact remaining lemmas

Assume the split total category has finite stable unions of M-subobjects and matching finite families of total maps glue. The latter follows from finite joins of compatible partial arrows; it is stronger than existence of domain joins alone. Use the finite M-covers whose union is the whole object, including the empty cover of 0. Compatible-arrow gluing makes this topology subcanonical.

The proposed next step is to construct finite syntax and proof objects in the resulting sheaf category by finitary polynomial initial algebras, and verify the comparisons listed below. Retain the selected mono class defined by representable M-pullbacks, rather than all monos. The concrete target is to prove that the base propositional proof-conclusion image is selected using e_φ above.

Required lemmas, in dependency order:

1. The finite-cover topology is subcanonical; Yoneda sends 0 to the initial sheaf and finite M-unions to sheaf unions. Prove these from the finite gluing assumptions.
2. The selected-mono class is stable under pullback and finite union, and the selected subobjects of each representable are exactly the original M-subobjects.
3. Sheafification transports the finitary syntax and proof initial algebras from presheaves to sheaves. For inference functors, verify the finite pullback and coproduct comparisons explicitly.
4. Every section yX→S of the sheaf of formulas is locally represented by a fixed finite formula shape on a finite M-cover of X; justify finite refinements from the chosen finitary coverage.
5. For a section represented by a fixed formula shape, prove that pulling back the theorem-image mono gives exactly y(e_φ)→yX. The finite-set lemma identifies the presheaf proof predicate as a finite union of representable branches; the cover topology must turn that union into the representable domain join.
6. Extend this local description across the finite cover to show that the whole theorem-image mono is selected.
7. Establish consistency from disjoint atomic axioms without a global valuation U→2. Stagewise finite valuations work on nonzero objects; at the initial object, use the empty-cover sheaf condition. Equivalently, show that the false-proof presheaf maps to y0 and hence its sheafification is initial.
8. Apply the already proved inseparability-transfer theorem to selected admissible theory extensions. For the numerical comparison, construct the code interpretation S→y(S_rec) and prove that every c.e. classical extension pulls back to a selected theory; do not assume this syntax object equals y(S_rec), since finite-cover-local formulas can have bounded shape while recursive code families may have unbounded shape.

Daniel Lin's *Presheaves over a join restriction category*, arXiv:1801.07390, §2 Definition 4 and §3, is relevant precedent: it uses arbitrary compatible joins, not merely finite ones. Its full hypotheses fail in the numerical c.e. domain category, so its theorem cannot be applied directly without a finite-cover adaptation. Verified PDF URL https://arxiv.org/pdf/1801.07390.
