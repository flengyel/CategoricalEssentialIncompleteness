# Corrections and dependencies

The numerical category now distinguishes an object C = (m,C_0), its carrier |C|, and a morphism's represented function. Tuple encodings have declared domains and recursive images; the zeroth power uses its singleton code. The total equivalence has named functors Q and F, object and arrow actions, and natural isomorphisms. The partial-map equivalence has its monic-span action, exact domain description, functor laws, and full-faithfulness and essential-surjectivity proofs.

The regularity proof specifies the image object, its factorization, and the descended morphism for a surjection. The proof also constructs partial inverses of monomorphisms. These results establish the categorical hypotheses used by Appendix A.

The syntax proof specifies the constructor algebra, an arbitrary parameterized target algebra, and the two folds with their projection and algebra equations. A bottom-up evaluation algorithm uses each operation on its declared carrier; induction proves termination, carrier membership, and uniqueness. The list proof gives its structure, the canonical slice-product comparison, the empty-list value, the fold equations, and length induction. No operation is assumed to extend to a total recursive function outside its specified carrier.

The numerical free-variable and substitution algorithms are identified through their constructor equations with the categorical folds. Term substitution, failure-valued formula substitution, admissibility, and the successful restriction remain separately typed. The general substitution construction is cited from Appendix A.

For derivations, the proof retains the given axiom object rather than silently replacing it by an image representative. Numerical tree labels are encoded elements of the rule carriers and are decoded before applying premise and conclusion maps. The carrier of valid trees, full conclusion map, constructor algebra, arbitrary target algebra, and unique fold are explicitly stated. Evaluation preserves each node's conclusion and halts on the valid carrier.

The arithmetic sentence conclusion is the displayed pullback of the full conclusion map. Appendix A then gives the least generated sentence theory through its regular image. The numerical proof carrier is compared with the syntactic construction by a computable relabeling, rather than an unsupported equality of stored codes. The rule-instance comparisons rho_n preserve premises and conclusions. A separate map eta_n converts actual interpreted rule instances to the scalar predicate presentations used by the syntactic tree construction. Their composition and its inverse determine a bijection of valid proof carriers preserving conclusions, and hence equality of the relevant conclusion images.

The separate numerical incompleteness subsection declares its diagonal restriction idempotents and functors. Its reduction inequalities are explicitly in the restriction splitting and use the proved code comparison. The argument then invokes the existing domain-incompleteness corollary.

The source is organized into 08c-numerical-realization.tex and 08d-numerical-incompleteness.tex, input in that order by the arithmetic assembly file. The four published manuscript/appendix artifacts and current download links use version 26. The reviews and build reports remain outside the mathematical documents.
