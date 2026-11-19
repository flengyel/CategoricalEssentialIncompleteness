# Proof checks on manuscript v64

These notes index the 77 proofs and three numbered definitions in the printed manuscript. The page number is the start of the statement. For its full hypotheses, types and Lean declaration, follow the corresponding entry in the [v64 correspondence](../../../FORMALIZATION_STATUS_V64.md). The [referee report](referee.md) gives the fresh checks of the splitting and slice arguments, the two Boolean valuations, the scope of the arithmetic and oracle conclusions, and the fork test for global elements.

The earlier [proof-by-proof review](../V60_2026-11-17/proof-checks.md) assessed v59 at commit 7fd727f411653c8ce0336ef2f9280c5b978fc5a7. I matched its TeX to v64 at 97ef88d128017ab824e17f0269c6e928020f7376 by label and compared the complete numbered statement and proof environments. All statements and definitions agree byte for byte. Of the proofs, only 4.8 and 5.1 changed, and both were checked afresh. For the other 75 the notes use the earlier proof analysis, supplemented by the v64 checks in the report. Historical proof-status remarks in that earlier review refer to its own commit. These notes do not represent 77 new independent derivations or a new full Lean replay.

## 3. Diagonal comparison

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Theorem 3.1, p. 6 | Apply the Turing property before interpreting the computation. Precomposing with the graph of its total parameter reverses the two pulled-back domains. Disjointness makes both zero. The nonzero identity and join assumption are needed for the noncoverage clause. |
| Corollary 3.2, p. 7 | A complementary target pair would have join the identity. A lift with the two required fibers would contradict 3.1. Faithfulness supplies uniqueness at most. |
| Corollary 3.3, p. 7 | A total conditional on two complementary source domains gives the required lift after applying the coproduct comparison. Test the orientation by sending the positive domain to the second summand. |
| Proposition 3.4, p. 7 | A common join of the two disjoint branches agrees with each on its own restriction. Its domain contains both members of a cover, hence is total. |

## 4. Internal theories

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Proposition 4.1, p. 9 | For a split object use the chosen embedding and retraction to transport a receiving idempotent back to the original object. Range leastness there descends to its splitting. In the partial-map target a factorization through validity then bounds the interpreted regular image. |
| Theorem 4.2, p. 9 | Pull the disjoint target bounds back along the total reduction and apply 3.1. If the indicated join were the identity, preservation of that join would contradict the diagonal conclusion. Reflection of zero is unnecessary. |
| Corollary 4.3, p. 10 | A complementary separator for any disjoint extension pulls back along the total reduction, including its cover equation. The fork test in the report checks why failure of coverage alone cannot yield an independent global sentence. |
| Theorem 4.4, p. 11 | Axiom introduction gives extensivity and leastness gives monotonicity. The closed formula subobject already contains its sentence part as axioms, giving idempotence. A morphism into a mono over the sentence object is unique exactly when the image factors. |
| Theorem 4.5, p. 11 | Pull closed formulas back along a logical translation using the rule-instance comparisons, including side conditions. Compose the image/inverse-image adjunction with generation. This yields the generation and composition identities on theories. |
| Proposition 4.6, p. 12 | Regularity transports the image of the conclusion morphism. Taking the image of the assumed derivation comparison gives the required inclusion. Extensivity and idempotence give equality after closure. The additional right adjoint is conditional on the stated adjunction. |
| Theorem 4.7, p. 14 | A map to sentences describes a substitution for each nullary predicate. Its extension to free syntax respects admissible substitution because all replacement formulas are closed. The two signed inequalities extend it to a theory morphism. The inverse image under the counit supplies consistency for the right adjoint. |
| Corollary 4.8, p. 14 | A disjoint covering copairing is both monic and regular epic. Its inverse supplies the separator morphism. The one-element interpretation of terms makes every equality true and evaluates a quantified formula at its body. The truth fiber gives a consistent complete closed extension. |

## 5. Associated categories

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Lemma 5.1, p. 15 | The terminal-object calculation uses a splitting of the restriction of an arbitrary partial morphism. The equation for the split-source parameter establishes both totality and the evaluation identity. In the slice the graph embedding has a partial inverse, and its associated restriction idempotent gives essential surjectivity of the splitting. |
| Theorem 5.2, p. 15 | Postcomposition by a mono retains the spans and reflects their compatibility with the base. Factoring either leg through the pullback gives the two hom-set bijections. At the identity of the larger base the second unit has exactly the smaller base for its domain. |
| Theorem 5.3, p. 17 | Transport each closed formula subobject with its rule algebra and use target initiality for the transported axiom subobject. Evaluation at the specified point applies to an arbitrary closed consistent complete extension. The retraction also detects totality and carries total Boolean extensions in either direction. Apply 4.3 for the final reduction. |

## 6. Syntactic recursion category

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Lemma 6.1, p. 18 | The trace coding must prove specialization, evaluation and composition inside PA with variable numerical inputs. Pointwise identities of standard programs would be insufficient for later interpretation in nonstandard models. |
| Lemma 6.2, p. 20 | Search the least code of a witness to the given existential predicate. The search realizes its domain in PA, even when several outputs could work. Identification with the whole relation uses the additional proof of functionality. |
| Lemma 6.3, p. 20 | Universal provable equality of represented graphs supplies full faithfulness of the predicate presentation. Taking a domain formula for a recoded idempotent gives essential surjectivity. Preimage search for a provably injective morphism supplies the partial inverse used by 5.1. |
| Lemma 6.4, p. 23 | Induction collects the witnesses of a coded finite sequence of existential conditions. This works at arbitrary internal sequence lengths, including those in nonstandard models. |
| Proposition 6.5, p. 24 | A target algebra in a parameter slice supplies the operations to evaluate each tagged node over its parameter. Internal induction on a coded tree proves existence and uniqueness of the evaluation graph on the given carrier. |
| Proposition 6.6, p. 25 | Start the list fold at the empty-list section of the target algebra. Each recursive call retains the parameter. Induction on length proves agreement for any two such folds. |
| Proposition 6.7, p. 26 | At a binder equal to the replaced variable, substitution returns the original quantified expression independently of the recursive result for the body. At a distinct binder the success pullback enforces the capture condition. |
| Lemma 6.8, p. 27 | A derivation node records an actual rule instance. Matching the ordered child conclusions with its premises gives valid input to any target algebra. Inductive evaluation over the formula object establishes the initiality required for general finite rule data. |
| Theorem 6.9, p. 29 | Apply 6.8 to the chosen axiom subobject and the typed first-order rules. The regular image gives formula closure, and its pullback to sentences gives the generated theory. These steps also apply with a parameter. |

## 7. Interpretation and soundness

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Proposition 7.1, p. 30 | Interpret a typed graph in an arithmetic model using its carrier coding. Uniform provable graph equality gives a well-defined functor. Restrictions and ranges interpret as domain and image partial identities. The proof does not give faithfulness of a single arbitrary model. |
| Lemma 7.2, p. 30 | Complementarity gives two provably disjoint exhaustive predicate cases. Tagging them in reverse order gives a provably functional total graph, hence a source conditional. |
| Corollary 7.3, p. 31 | The model functor sends the identity of the numerical object to a nonempty identity. The conditional of 7.2 lets 3.3 deduce source inseparability. |
| Proposition 7.4, p. 31 | Interpret the predicate product, equalizer, coproduct and existential image in the entire arithmetic model. These computations pass through the predicate equivalence to the total split category. |
| Lemma 7.5, p. 32 | At a binder, admissibility justifies commuting the two updates of a variable assignment. This supplies the formula substitution fact needed in the soundness proof. |
| Proposition 7.6, p. 33 | Check the seven schemes under all assignments. Generalization uses validity under every assignment. Induction on a standard finite proof yields the factorization through truth in a model of the given axioms. |
| Lemma 7.7, p. 33 | For an equalizing family, the set of good coordinates belongs to the proper ultrafilter. It contains a coordinate that supplies a filler on the complement. The same reasoning handles an empty coproduct summand. Choice in the metatheory yields preservation of surjections. |
| Lemma 7.8, p. 34 | The comparison on predicates follows by Łoś's theorem. A nonempty set of good coordinates yields a predicate-valued representative, and an empty predicate stays empty. Full faithfulness on predicate presentations extends naturality to arbitrary split objects. |
| Theorem 7.9, p. 34 | Naturality at the conclusion morphism transports the standard factorization, and naturality at negation transports disjointness. This defines an external subobject of the interpreted sentence carrier for the ultrapower. |

## 8. Arithmetic

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Lemma 8.1, p. 36 | A standard computation trace gives a finite verification, hence the required PA derivation for its numeral instance. The two domain inclusions are then transported to the specified interpretations. |
| Lemma 8.2, p. 36 | One partial search can choose the first proof or refutation. When the two truth sets are disjoint its tag has the required reversed fibers. The program supplies a source lift before interpreting it. |
| Theorem 8.3, p. 37 | Consistency of the presented theory supplies a model of its axioms. Use standard-code soundness or its ultrapower transport for the interpreting arithmetic model, then 4.2 for noncoverage. The last assertion about individual sentence codes is stated for the standard interpretation. |
| Corollary 8.4, p. 38 | A recursive separator of the standard sentence-code sets pulls back along numeral substitution. Its conditional has a source program, contradicting 3.2. Deciding a consistent complete c.e. theory on the recursive sentence carrier would produce such a separator. |
| Proposition 8.5, p. 39 | A single numeral is a complemented subobject of the parameter object. Extensivity therefore splits the parameter slice into two factors. The rules retain their parameters, so the initial derivation object restricts to an initial algebra on the selected factor. |
| Theorem 8.6, p. 41 | Index the joint proof search before picking a consistent standard fiber. Diagonal evaluation in each consistent fiber rules out both possible tags. The resulting sentence morphism is total on every index, with independence asserted only at consistent indices. |
| Proposition 8.7, p. 42 | Tuple coding identifies numerical split objects with c.e. carriers. Dovetailed preimage search gives a section on the image of a surjection and the unique inverse of an injection on its image. |
| Proposition 8.8, p. 45 | Recursive syntax tests and finitely many semidecisions for axiom leaves recognize the derivation carrier. Evaluation in any supplied slice algebra terminates on that carrier. The subsequent comparison of proof codings relabels rule instances and preserves the ordered premises and conclusions. |
| Lemma 8.9, p. 50 | The diagonal parameter contradicts a separating conditional. A second argument collects the positive leaves of two supposed opposite derivations, evaluates their formulas, and proves in PA that both conclusions would be true. This establishes internal consistency without assuming a computable global separator. |
| Corollary 8.10, p. 51 | The universally closed reflexivity sentence gives the required global theorem in the nullary language. Apply the reduction to every consistent extension and then use 5.1–5.3 for its associated category and Boolean obstruction. |

## 9. Miller sequences

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Lemma 9.1, p. 52 | Enumerate cylinders disjoint from the name fiber alongside cylinders on which the oracle program returns a fixed value. A finite cover of Cantor space exists exactly when all names agree. Nonemptiness makes the value unique. |
| Proposition 9.2, p. 52 | Dovetail over inputs to compute a range on every name. The witness discovered can vary while its value and the domain of the search agree. Specialization gives one total parameter morphism for the unanimity evaluator. |
| Lemma 9.3, p. 53 | Finite unions of dyadic boxes at bounded stages yield uniformly computable distances. The weighted sums are positive precisely on the two disjoint halting opens. The Miller property turns a uniform index for their signed difference into both inverse-image identities. |
| Corollary 9.4, p. 54 | A common separator of the strict cuts would pull back to one of the diagonal pair. The first digit from a fixed name separates the strict cuts, and its value can differ between names at equality. |
| Proposition 9.5, p. 54 | For a function constant on the fibers of a surjection, search for a preimage and return the function value. This descends the morphism even when the first witness varies by name. Unique preimages of injections give partial inverses. |
| Lemma 9.6, p. 56 | Test the finitely many semidecidable labels on the tree, including axiom membership over the actual parameter. Folding in any target algebra preserves the parameter and the common partial graph across names. |
| Theorem 9.7, p. 57 | The real field with the designated constants satisfies the strict rational bounds, giving consistency. The two cuts reduce to provability and refutability of a strict inequality. Apply the domain criterion to each consistent extension under the printed uniform semidecidability hypothesis. |
| Corollary 9.8, p. 57 | Reflexivity supplies a global theorem in every extension. The field realization supplies the slicing and deduction hypotheses, hence the associated-category conclusions for arbitrary closed consistent extensions. |

## 10. The three-point space

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Proposition 10.1, p. 60 | Endpoint evaluation computes span domains and images componentwise. Specialization yields endpoint Turing morphisms. A central computation exposing a hidden coordinate fails the naturality condition required of an evaluated parameter. |
| Proposition 10.2, p. 62 | Tree evaluation in a propositional algebra is computable at each component. Naturality of its operations ensures that evaluation commutes with both fork transitions, giving the required unique natural transformation. |
| Proposition 10.3, p. 63 | At a modus-ponens node, the ordered child conclusions match the two required premises. A fold in any algebra therefore exists in the slice. Its equations and naturality determine its action uniquely. |
| Theorem 10.4, p. 63 | The conclusion image gives least closure. Two contradictory finite derivations would admit a truth assignment to all their leaves in the component in question. The componentwise empty meets prove internal consistency. |
| Theorem 10.5, p. 64 | The atom morphism reduces the internal pair. Separately, a recursive separator at an endpoint would separate its numerical diagonal sets. Inclusions of extension families grow both pullbacks, giving the stated covariant action on pairs. |
| Corollary 10.6, p. 64 | Enlarge only the chosen endpoint by the deductive closure of an arbitrary consistent c.e. axiom extension. Every transition into it still respects the family, so 10.5 applies. |
| Proposition 10.7, p. 64 | Variable names are constant along transitions. Relabelling can identify atoms and still preserves successful substitution and previously matching premises. Folds for arbitrary parameter-indexed axiom subobjects give the required natural initial-algebra morphisms. |
| Proposition 10.8, p. 65 | Erasure sends equality to a fixed tautology, drops quantifiers and is invariant under admissible term substitution. Thus inverse-image closure bounds the first-order theory above, and embedded derivations give the opposite inclusion on propositional sentences. Pulling back a complete endpoint extension would contradict 10.6. |
| Corollary 10.9, p. 66 | The embedded propositional tautology gives a global theorem. The conservative first-order theory, its reduction and the parameterized deduction construction allow transfer to every consistent internal extension and its associated partial slice. |

## A. Syntax and deduction

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Definition A.1, p. 69 | Definition. Parameter stability is an initial-algebra property in each slice. Decidable equality of variables supports the later binding tests. The Boolean identities are equations on jointly epic coproduct injections. |
| Definition A.2, p. 70 | Definition. Pull back the free-variable list along the empty list. Negation restricts to this sentence subobject because it preserves the free-variable list. |
| Proposition A.3, p. 71 | Carry the original expression with its substitution result through the parameterized fold. Pulling back the success injection yields the complemented domain of admissible substitution. |
| Definition A.4, p. 72 | Definition. A rule-closed formula subobject is a monic slice object admitting the rule algebra. Monicity makes its algebra structure unique. |
| Theorem A.5, p. 72 | Finite powers, pullbacks and finite coproducts in the rule construction preserve regular epimorphisms as needed. Descend the algebra operation to the regular image of the conclusion. Initiality factors that image through every closed subobject. |
| Theorem A.6, p. 73 | Instantiate the rule data with nonlogical axiom subobjects, the logical schemes and the two inference rules. Restrict the least formula closure to sentences by a pullback. Its regular image is stable under that pullback. |
| Lemma A.7, p. 74 | A total morphism's regular-image mono with partial inverse defines a receiving restriction idempotent. Splitting any other receiving idempotent gives a factorization of the same image, proving leastness. |

## B. The fork construction

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Proposition B.1, p. 75 | The only cover that imposes extra data presents the whole space by the endpoint pushout over the center. Its universal property extends transformations. The two-point example distinguishes this operation from evaluation of a componentwise product. |
| Proposition B.2, p. 75 | Regular images of computable diagrams have compatible component carriers. Descent after a surjection is natural by cancellation at the center. Representable probes detect component injectivity, and disjoint summands give extensivity. |
| Proposition B.3, p. 76 | Pullbacks intersect the required span domains. Images supply ranges. Unique preimages for component injections respect transitions and supply the natural partial inverse in the weak-choice argument. |
| Proposition B.4, p. 77 | A central singleton together with its two images gives a connected subdiagram. Singletons supported only at endpoints complete a family detecting disagreement of domains or values. |
| Lemma B.5, p. 77 | Encode a central element and both of its images into the universal object's coordinates. The resulting component injections are natural, and inverse search on their image gives a restriction embedding. |
| Lemma B.6, p. 78 | Pairing, parity, and finite-sequence coding use a shared coordinate seen by both transitions. Their recursive inverses therefore define isomorphisms of the diagrams. |
| Theorem B.7, p. 79 | Central evaluation checks the three computations and the two endpoint equations. Specialization gives a natural total parameter for any supplied partial morphism. On a valid central input, naturality supplies both endpoint agreements. |
| Proposition B.8, p. 80 | The stated coding isomorphisms give isotypicality, and fullness retains parameter morphisms. Restriction embeddings into the universal object realize all objects after restriction splitting. |
| Corollary B.9, p. 81 | For an idempotent partial function its image lies in its domain and is fixed, by equality of partial graphs under self-composition. The component images form a subfunctor. Inclusion and corestriction split the ordinary idempotent. |
| Proposition B.10, p. 81 | The orders of subobjects of the terminal object in the two completed total categories have different finite sizes. An equivalence would preserve this invariant. The coinciding endpoint images of distinct central inputs also obstruct decidable equality of the universal object. |

## C. Section lifting

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Proposition C.1, p. 82 | The oracle controls allowable domains, while every total source morphism remains ordinary recursive. The separator would compute a nonrecursive set if its target conditional lifted. The same two complementary domains give disjoint source branches with no common upper bound. |

## D. Faithful interpretations

| Printed result | Hypothesis or inference tested |
| --- | --- |
| Theorem D.1, p. 84 | Add the negation of the universal graph equivalence for distinct source classes to the consistent theory. Completeness and downward Löwenheim–Skolem yield a countable distinguishing model. A supported component detects the difference in the product target. |
| Corollary D.2, p. 85 | A graph class in the extension has a representative using the same formal objects and program indices as the base. A source Turing parameter therefore descends. The quotient preserves the specified operations that define the diagonal domains. |
