# From internal deduction to generated theories in version 37

The abstract does not explain the connection that makes the construction useful. The paper supplies a single chain: an internal calculus, a chosen axiom subobject, its derivations and conclusions, the subobject of derivable sentences, and the restriction domains on which the incompleteness theorems operate. The abstract names several stages without saying that they are stages of that chain. The missing explanation is substantive even when the individual sentences are technically accurate.

This report concerns the actual construction and its exposition, not a fresh certification of every proof. Anchors below refer to the version 37 source and its compiled numbering.

## 1. What the internal deductive system supplies

Let \(\mathscr R\) be the recursion category. The paper forms its restriction splitting \(\mathscr S=\operatorname{Split}(\mathscr R)\), whose objects are pairs \((X,e)\), where \(e:X\rightharpoonup X\) is a restriction idempotent of \(\mathscr R\). A morphism \(f:(X,e)\rightharpoonup(Y,d)\) satisfies \(f=dfe\); it is total when \(\bar f=e\). The logical construction takes place in the category \(\mathcal D=\operatorname{Tot}(\mathscr S)\) of these total morphisms. Splitting restriction idempotents makes the represented domains available as objects. Regularity supplies images and their stability under pullback.

Appendix A begins with a regular category \(\mathcal D\), independently of any recursion category, and assumes the further structure needed for syntax and the initial inference algebras. It does not prove that the completion of every recursion category has that structure. Sections 5, 8, and 9 prove the relevant realizations.

For first-order logic, the data in \(\mathcal D\) include term and formula objects, their constructor morphisms, free-variable and admissible-substitution morphisms, and a sentence subobject \(j:S\hookrightarrow\Phi\). Syntax initiality and parameter stability appear in Definition A.1. The sentence subobject is defined by the empty free-variable list in Definition A.2. Quantification and logical equality are present. The propositional specialization uses an atom object, negation and implication constructors, and no quantifiers (A.6).

The inference data are objects \(R_n\in\mathcal D\) and morphisms
\[
 p_n:R_n\to\Phi^n,\qquad q_n:R_n\to\Phi,
\]
where \(\Phi^n\) denotes a finite product. They specify rule instances, ordered premises, and conclusions. Nullary instances include logical axioms and the chosen nonlogical axiom subobject \(i_A:A\hookrightarrow S\). In the first-order instance, the other rules are generalization and modus ponens. Pullbacks and finite coproducts define an inference endofunctor
\[
 H_A:\mathcal D/\Phi\longrightarrow\mathcal D/\Phi.
\]
Its initial algebra has underlying conclusion morphism \(c_A:P_A\to\Phi\). The initiality expresses the inductive construction of derivations together with their conclusions. The universal property is in the slice because evaluating a derivation must retain its conclusion.

“Internal deductive system” is a descriptive name for this package; the body formally defines its syntax, rule data, and inference algebra. It does not define a separate single object bearing that name. The abstract must give enough of the package's meaning to make the name informative.

## 2. Where a generated theory is, and how it belongs to that system

The full conclusion morphism has a regular-image factorization in \(\mathcal D\):
\[
 P_A\twoheadrightarrow T_A\xhookrightarrow{m_A}\Phi.
\]
Theorem A.5 proves that this image is the least subobject containing the nullary conclusions and closed under the rules. Theorem A.6 identifies it, for the stated first-order calculus, as the least formula subobject containing the logical and nonlogical axioms and closed under generalization and modus ponens.

Restricting conclusions to sentences gives \(c_{A,S}:P_{A,S}\to S\). Its image is
\[
 T_{A,S}=S\times_\Phi T_A\hookrightarrow S.
\]
This is the generated sentence theory: the deductive closure of the chosen axioms within the internal deductive system. It is not a separate external theory subsequently attached to that system. It is an object of \(\mathcal D\) equipped with a monomorphism into its sentence object. In the propositional specialization, the formula object already serves as the sentence object, so no separate free-variable restriction is needed.

The next step is essential for the rest of the paper. Suppose the sentence-image monomorphism \(m_A:T_{A,S}\hookrightarrow S\) has a partial inverse \(r_A:S\rightharpoonup T_{A,S}\) in \(\mathscr S\). Lemma A.7 identifies the same theory with the restriction idempotent
\[
 t_A=m_A r_A=\operatorname{ran}(c_{A,S}):S\rightharpoonup S.
\]
For the sentence-negation morphism \(\nu:S\to S\), its refutation domain is \(\nu^*t_A\). Thus the generated theory yields the exact pair of restriction domains to which categorical recursion and inseparability apply. Consistency is \(t_A\nu^*t_A=0\); completeness is \(t_A\vee\nu^*t_A=1_S\).

The abstract omits this identification. It says that images give “generated theories” and then introduces “the theorem and refutation domains” without telling the reader that the latter are representations of the former and its inverse image under negation.

There is no general object classifying all theories in this construction. Each axiom subobject determines its own image. Section 7.2 additionally constructs a specific indexed family \(\mathcal T\hookrightarrow E\times S\) of arithmetic theories from one indexed axiom subobject, with numeral fibers identified in Proposition 7.5. This is a family of represented computably enumerable presentations, not a power object of all sentence theories.

## 3. How this produces essential incompleteness

There are two related arguments, and an abstract should not merge them into an assertion that an arbitrary range functor transports incompleteness.

**Semantic comparison (§§3.1, 4.1–4.2).** A range functor \(F:\mathscr R\to\mathcal A\) extends to \(\widehat F:\mathscr S\to\mathcal A\), so it interprets the theory range and negation. Proposition 4.1 derives disjointness of the interpreted theorem and refutation domains from a soundness factorization through a validity subobject disjoint from its inverse image under negation. Theorem 4.2 additionally requires a total morphism \(\theta:U\to S\), reduction inequalities for the two domains obtained from the Turing morphism, and a source lift of the specified reversed partial conditional in the target. Under its structural and nontriviality hypotheses, Theorem 3.1 supplies a total morphism whose interpreted sentence family avoids both theorem and refutation domains. Therefore the interpreted theory is incomplete, and range-functor preservation of joins excludes completeness of the source theory too.

**Inseparability and extension (§4.3).** Corollary 4.3 starts with a fixed inseparable pair \(a,b\) on \(U\), a total reduction \(\theta:U\to S\), and a base theory range \(t_0\) satisfying \(a\le\theta^*t_0\) and \(b\le\theta^*\nu^*t_0\). For every larger consistent represented theory range \(t\ge t_0\), those inclusions persist. A complementary separator for \(t,\nu^*t\) would pull back to a separator for \(a,b\). Hence the larger theorem/refutation pair is inseparable and cannot cover the sentence object. The effective extension class is supplied by the realization, not by the word “represented” alone.

This is the missing explanation of essential incompleteness: an internal system first supplies a theory and its theorem/refutation domains; the categorical argument excludes completeness, and the same obstruction survives the permitted consistent extensions of its axioms.

## 4. Actual realizations and extension classes

| Realization | Location and constructed theories | Incompleteness argument |
| --- | --- | --- |
| Syntactic recursion category \(S_T\) | Theorem 5.9 constructs first-order logic with equality and each generated theory in \(\mathcal B_T=\operatorname{Tot}(\operatorname{Split}(S_T))\). It also represents its sentence theory by a restriction idempotent on \(\omega\) in \(S_T\). | The arithmetic application fixes \(S_{\mathrm{PA}}\), varies represented c.e. axiom subobjects, and uses the semantic comparison. Corollary 7.4 gives recursive inseparability for every consistent c.e. PA extension. |
| Miller category \(\mathcal E_a\) | Proposition 8.5 realizes first-order logic with equality in \(\mathcal D_a=\operatorname{Tot}(\operatorname{Split}(\mathcal E_a))\). The generated real-closed-field theory includes constants and the strict rational bounds specified by \(a\). | Theorem 8.6 reduces the inseparable cut pair to theorem/refutation domains and applies Corollary 4.3. Its axiom-extension class requires one oracle program to semidecide the same axiom set from every binary representation of \(a\). |
| Three-point cosheaf category \(\mathscr R_X\) | The relevant total category is \(\mathcal E=\mathcal C_{\mathrm{rec}}^J\), with \(\operatorname{Split}(\mathscr R_X)\simeq\operatorname{Par}(\mathcal E,\operatorname{Mono})\). Propositions 9.2–9.3 construct propositional syntax and derivations. Theorem 9.4 identifies the image as a theory subfunctor. | Theorem 9.5 uses the source-inseparability extension criterion. Corollary 9.6 gives two endpoint propositional theories whose consistent same-language extensions with c.e. axiom sets are incomplete. |
| Auxiliary numerical realization (§§7.4–7.5) | The same syntax and image/range construction is realized in the total splitting of ordinary partial recursion, with explicit comparisons to the standard syntactic interpretation. | Applies the source-inseparable-pair criterion to PA extensions. It is an additional realization of the abstract construction, not an omitted fourth principal application on a par with the cosheaf and Miller constructions. |

For arithmetic soundness, \(\mathbb N\) interprets codes and the operations on codes; a separately chosen structure \(K\models\Gamma\) interprets the decoded sentences. The construction does not require \(\mathbb N\models\Gamma\). The standard-code soundness factorization and its arithmetic-ultrapower transport are §§6.3–6.4. They are substantial results, but their abstract description should come after the reader understands what theory is being interpreted.

## 5. What the abstract needs, and what it need not teach

| Current expression | Mathematical role | Expository treatment |
| --- | --- | --- |
| “internal deductive systems” | Categorical syntax, rules, axiom subobjects, derivation/conclusion morphisms | Give a short explanation connecting axioms, derivations, and conclusions. Merely naming both logics does not supply it. |
| “generated theories” | The least deductively closed sentence subobjects determined by those derivations | Say generated **from the chosen axioms by the system's inference rules**, and identify them with the theorem domains used next. |
| “regular categories of total morphisms in the restriction splittings” | The precise ambient categories where images and initial algebras are constructed | Keep in §§4–5 and the realization statements. The abstract's word “completions” can retain the setting; the full technical description currently interrupts the explanatory chain and does not establish that chain. If retained, the restriction splittings must explicitly be of the named recursion categories. |
| “soundness factorization through a validity subobject…” | Supplies interpreted consistency under the exact validity-disjointness premise | Preserve the mathematical condition in the theorem. An abstract can explain its role as a sound interpretation giving disjoint theorem/refutation domains in the constructed cases, rather than reproduce the factorization terminology. |
| “a total reduction and a lift of a partial conditional” | Supplies the computational/categorical obstruction to coverage | Explain what is being compared or reduced. Listing these nouns without the theory/domain connection does not inform the reader how deduction enters. |
| “consistent represented extensions” | Larger axiom-generated ranges satisfying the consistency equation | State that extending axioms enlarges theorem domains and preserves the inseparability obstruction. Give the concrete effectiveness conditions in the applications. |

Removing the isolated technical ambient-category sentence from the abstract would not remove a hypothesis from a theorem, conceal a proof gap, or change the location of any construction. It would remove a piece of implementation detail from the place where an account of the construction's purpose and use is missing.

## 6. Four-sentence conceptual account for abstract planning

An internal deductive system supplies a sentence object and, for each represented choice of axioms, a morphism assigning to a derivation its concluding sentence. The image of that morphism is the theory generated by the axioms, and inverse image under negation gives its refutable sentences. In the constructed realizations, these two subobjects are represented by restriction domains, allowing the categorical comparison theorem to address provability and refutability under its soundness, reduction, and lifting hypotheses. Reductions from inseparable pairs persist under consistent represented extensions and therefore yield essential incompleteness.

These sentences explain the connection to preserve; they are not offered as a full replacement abstract or as a request to insert four further technical sentences into the existing one.

## Scope

Read: §3's comparison and conditional criteria; §4 in full; Appendix A's syntax definitions, rule/inference construction, closure/image theorem, first-order application, range lemma, and propositional specialization; §5's total-category realization, full derivation-initiality argument and generated-theory theorem; §§6.3 and 7.1–7.3; the numerical incompleteness chain in §7.5; §8.3 in full; §9's ambient presentation and §9.3 in full. This was an explanation/dependency audit of those argument chains. No independent verification of every numerical foundational lemma, the topological construction, every cited source, or the historical notes' proofs was attempted. No manuscript source was changed.
