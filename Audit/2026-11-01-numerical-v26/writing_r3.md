# Mathematical Writing review of the third numerical candidate

**Disposition: the previous repairs are resolved; one numerical-label type needs an explicit presentation choice.** The general categorical comparisons, parameterized fold proofs, list-source comparison, image-object convention, and object/carrier distinctions now have the required data. The two subsections retain their separate purposes and do not duplicate Appendix A's general arguments.

Reviewed snapshot: `tmp/numerical26/round3/08c-numerical-realization.tex`, `08d-numerical-incompleteness.tex`, and the arithmetic assembly file. I reread both subsections in full. The KLR source and methodology are recorded in the first report; the current issue is the author's explicit-type requirement, supported by KLR's advice on declared variables and consistent notation.

## Remaining presentation issue

At §7.4, lines426–443, the maps

`rho_n:|R_n^num|→G_N R_n^syn`

are typed between the numerical and interpreted rule carriers. At lines458–460, however, `rho_n(kappa_mn^(-1)(r))` is directly used as the stored numerical label of a syntactic derivation node. This requires `G_N R_n^syn` to be a subset of `N`. A rule object built directly from products need not have that unary presentation: for example, `R_1=V×Fm` has an interpreted product carrier before its numerical presentation is chosen.

The needed repair is to state that `R_n^syn=J_PA(C_n)` are the **unary predicate presentations used in the proof of Lemma5.8**, with `p_n^syn,q_n^syn` transported through the corresponding presentation isomorphisms. Then

`G_N R_n^syn=C_n(N)⊆N`

and the stored-label replacement has exactly the stated numerical type. The finite-product comparison `chi_n` already correctly handles the target of the premise map. The existing recursive relabeling proof can then be retained: its inverse is obtained by reversing the rule comparisons, and tree induction proves validity, conclusion preservation, and inverse equations.

This is a local declaration of the chosen presentation, not a request to equate categories, assume preservation of initial algebras, or add a hypothesis. The earlier construction provides those predicate presentations and computable comparison maps.

One accompanying phrase should be made literal at line378: values in the pullback summand of `H_A(Q,q)` are paired with the **decoded rule instance**. A stored label is a number in `widehat R_n`; decoding it gives the actual point of the rule carrier. The earlier paragraph states the decoding convention, so this is a local clarification of its use.

## Resolved checks

- `Im(f)` is now an object with its own specified carrier, and all enumerations and membership statements checked here use carrier notation.
- The syntax target algebra, its component maps, its parameter conditions, its fold equations, and the induction establishing computability and uniqueness are explicit.
- The list algebra uses the typed canonical source comparison, an empty-list value, and the nil/cons recursion equations.
- Derivation objects and their labels have numerical codes; their constructor and evaluation algebras are typed in the formula slice.
- The direct proof uses arbitrary algebra operations on their declared carriers and never assumes globally total recursive extensions.
- The comparison with arithmetic uses a typed recursive proof relabeling and conclusion equation, rather than an unsupported literal equality of proof-code carriers.
- The numerical source maps, their split images, and the interpretation functors remain distinct.
- §7.4 constructs the realization and its represented theory objects. §7.5 applies the incompleteness results; §7.6 follows with numeral instances.

No other necessary organization, terminology, or proof-exposition correction was found in this reading. The final source and rendered output should be rechecked after the presentation declaration is added. This is a scoped editorial/type review, not Lean elaboration or whole-paper certification. No manuscript source was edited by this reviewer.
