# Account outline

Domains, Hoare profunctors, and essential incompleteness.

1. **Computation, assertions, and deduction.** States the problem and distinguishes computational domains, Hoare relations, and deductive presentations; identifies the relevant literature.
2. **Restriction domains and direct images.** Defines restriction and range structure, the contravariant domain functor, direct images, and the local adjunction. These definitions support all subsequent Hoare constructions.
3. **Hoare assertions as profunctors.** Defines profunctors and their composition, then proves the total- and partial-correctness pseudofunctor laws, comparison, program-order variance, and detection of domains.
4. **Weakest liberal preconditions and representability.** Defines representing domains and the associated right adjoint. **§4.1** proves the exact numerical characterization and distinguishes existence, uniform synthesis, formula construction, and membership decisions.
5. **Stable unions of domains.** States the additional universal range property, defines Heller unions, proves their preservation laws, and types the bounded-distributive-lattice-valued domain functor. These laws are used by the separation arguments.
6. **Categorical separation and proof codes.** Proves the transfer theorem from an inseparable pair and positive/negative proof maps. **§6.1** proves the distinct representation-based inseparability theorem.
7. **The numerical category and effective unions.** Defines the partial-recursive category and verifies its range and uniform-union properties. The example at the end distinguishes uniform effective unions from arbitrary increasing unions.
8. **A numerical deductive construction.** **§8.1** constructs an inseparable pair, computation evidence, syntax, axioms, and decidable annotated proof checking. **§8.2** constructs the Boolean deductive category and proves essential incompleteness. **§8.3** connects the assertions to the Hoare relations and constructs the proof-conclusion maps. **§8.4** proves the conditional arithmetic representation corollary, including jointly recursive numeral substitution. **§8.5** gives an interpretation criterion and the comparison with effective verification.
9. **The intrinsic construction problem.** Identifies the additional categorical construction and arithmetic comparison questions; explains why unrestricted complementation would remove the computational separation condition.
A. **Closure operators associated with deductive presentations.** Constructs least closure for specified rules and axioms when the deduction stages admit stable unions. **§A.1** defines `Cons`, the contravariant theory and domain functors, and their natural inclusion. **§A.2** verifies the effective numerical deduction stages and compares their closure with the already defined propositional calculus.
B. **Ordinary interpretations and finite hom-sets.** Proves the collapse obstruction for locally finite targets.
C. **Adjoining partial witnesses to a profunctor.** Defines the coend extension, proves its support law, and recovers the total-support fibre.
D. **Indexed predicates and enrichment.** States Kelly's required monoidal and hom-object data, distinguishes indexed predicates, and separates logical negation from inverse image along a negation-code map.

The implemented reorganization is appropriate: the main argument first defines the numerical calculus directly, and Appendix A then identifies its closure operator. Thus the closure construction does not appear to supply the missing intrinsic deductive data. No further reorganization is needed.

