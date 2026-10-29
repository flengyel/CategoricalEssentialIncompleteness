# Continuation: general recursion-category construction

Continue the mathematical construction in `flengyel/CategoricalEssentialIncompleteness` on `main`. Work from the current committed sources, not from the earlier represented-Boolean-quotient formalization.

## Current documents

- `manuscript/domains_hoare_profunctors_essential_incompleteness.tex` and `.pdf`: *Domains, finite proofs, and essential incompleteness*, 23 pages, committed as `10284d07bd46f327472ccddf1ee508d0de5c2156`.
- `manuscript/general_recursion_category_construction.tex` and `.pdf`: the general-construction supplement produced after that commit. Consult its latest committed statements and review record before using them.
- `Audit/2026-10-29-polynomial-proofs/`: outline, hostile review, mathematical-writing review, and verification of the 23-page note.
- `Audit/2026-10-29-general-construction/`: review and verification of the supplement.

No new theorem in these notes has been formalized in Lean. The older Lean axiom-audit count does not verify the present constructions.

## Established mathematical structure

1. In a restriction category with binary restriction products, stable finite domain joins, a nontrivial object U, a Turing morphism τ, and the stated binary case distinction, d=τΔ gives an inseparable pair a=d*q0, b=d*q1. Universality is used at F=hπ2 to obtain total g and dg=hg. Binary case distinction is an explicit additional hypothesis.
2. A typed rule presentation gives a polynomial inference functor. In a split range restriction category, universal-object dominance and universal ranges construct a total typed constructor embedding γ:PW→W with restriction inverse δ. With q:W=S×U→S, choose an embedding k:PW→U and use γ=⟨t,k⟩; restrict its partial retraction to ranγ to obtain the typed δ.
3. Finite stages are e0=0 and e(n+1)=γP(e_n)δ. The supplement proves initiality on the union e from the indicated union conditions and exact-support gluing of finite partial folds h0=0, h(n+1)=αP(h_n)δ. The proof handles arbitrary split target algebras. For finitary inference polynomials, the Turing construction discharges the separate arrow-gluing assumption: a parameterized recursion theorem produces h=αP(h)δ, induction gives h_n≤h, and he has exact restriction e. The typed evaluator is filtered by ran(ΔS); the polynomial strength is used only with total program-parameter maps. The two finite-stage domain-union hypotheses remain. The proof does not assume that P preserves arrow joins or that arbitrary countable joins exist.
4. Parameter-stable versions give finite lists, syntax, and proof algebras. The syntactic signature is U+X+X²: atoms, negation, and implication. Logical rules are the three displayed classical Hilbert schemes and modus ponens. Positive A-axioms and negative B-axioms are indexed by the split objects of disjoint domains a,b.
5. Under the supplement's regularity, extensivity, range/regular-image compatibility, and decidable equality hypotheses, the proof-conclusion range is the least rule-closed domain. Consistency is proved using valuations depending on finite lists of positive axiom leaves. No global Boolean separator of A and B, or soundness of an arbitrary extension, is assumed.
6. The maps from atomic axiom instances to one-node proofs give the positive and negative range inequalities. Inseparability then proves every consistent computational extension incomplete. Computational theories are the stated rule-closed computational subobjects, not arbitrary subobjects of an enlarged topos.
7. The numerical split category realizes the construction hypotheses by uniform dovetailing. C.e. rule-instance carriers are allowed; their proof carriers are c.e. Recursive instance carriers with ordinary finite-tree coding give decidable proof checking.

## The next mathematical target

Derive the existence of the finite-stage domain union e from a precise categorical iteration structure. Use Heller's actual definitions of iteration categories, isotypical objects, frames, and the generated recursion categories. Identify the exact data needed for a finite-tree or finite-worklist evaluator whose termination domain is e. Prove the equality with the union of constructor stages. Do not infer leastness from an arbitrary fixed-point equation.

The supplement's Turing-fold theorem already constructs partial-fold gluing for finitary inference polynomials. Preserve its two essential details: the evaluator respects expression types before P is applied to it, and the strength identity uses total program-parameter maps. Nullary constructors invalidate unrestricted partial-parameter naturality. Do not replace this proof by external functoriality of P on arrows. For the polynomial preservation of e, the note separately assumes preservation by restriction products, total inverse image, and the finite coproducts in the presentation; product stability alone is not asserted to imply all three.

Then examine whether the other structural hypotheses follow from an appropriate established class of recursion categories:

- Can regularity and agreement of ranges with regular images be derived from Heller's factoriality or weak-choice hypotheses, together with the required finite limits? Prove the factorization and pullback laws rather than adding them tacitly.
- Which nonnumerical recursion categories have the required atom equality and parameterized finite constructions? Test at least one genuine nonnumerical example, with each hypothesis checked.
- Can decidable atom equality be weakened while retaining an internal consistency proof? A finite-formula characterization using equality partitions is a concrete candidate; the sheaf construction below is not yet established.

## Heller attribution and completions

Heller 1990 contains printed typographical errors as well as errors introduced
by OCR. Inspect the scan, type-check every imported equation, and reconstruct
any proof used. Consult `Audit/2026-10-29-general-construction/HELLER_SOURCE_CHECK.md`.
In particular, the equality-product and division formulas on p.1262 have
incorrect object subscripts. Do not copy the printed proof of Proposition 6.2
without checking its final composite. The current supplement proves its
range-filter calculation directly and does not invoke that proposition or the
iteration lemma to discharge an existence hypothesis.

Heller, *An existence theorem for recursion categories* (1990), §10, Example 5, p.1267, already constructs a recursion category from partial maps of simplicial sets whose diagonal Y→Y×Y has no range. Cite this as prior work. Do not present the general possibility of range failure as a new discovery.

Garner–Lin, *Cocompletion of restriction categories*, §3.1 and Lemma 9, define selected presheaf monomorphisms by representable pullbacks. They preserve the original selected-domain order on representables. This does not make the partial-map completion a range category. The supplement's particular counterexample is F_B:∐_{n∈B}y1→yN for non-c.e. B: any selected range would be a least c.e. superset of B, and the co-singleton upper bounds force it to equal B. Also, y0 need not be the initial presheaf; distinguish the selected-domain bottom from the empty presheaf.

A finite-cover sheaf route remains a candidate. For a fixed finite formula, enumerate partitions of its atom occurrences and positive/negative literal subsets for which the corresponding implication is a tautology. The domain of a branch is a finite meet of equality domains and a/b inverse images; take the finite join of these branches. No disequalities are required. To turn this into a construction, prove finite local syntax, selected representability of theorem images, and consistency. Ordinary presheaf images cannot be assumed selected. Do not assume a sheaf syntax object equals the representable object of recursive syntax codes; recursive code families can have unbounded formula shape.

## Working requirements

- State categories, functor types, object actions, morphism actions, variance, and universal properties explicitly. Define notation before using it.
- Keep restriction idempotents and domains in the partial category; identify their split objects in the total category. Distinguish logical negation from monotone inverse image along its code constructor.
- Do not call ordinary indexed predicates or Set-valued profunctors Kelly enrichment. Any enrichment claim needs its monoidal category, hom-objects, composition, and units.
- Preserve the proven conditional statements. Do not claim the Di Paola–Heller program is completed merely because the numerical model works or because a completion has all ordinary subobjects.
- Do the mathematical work before preparing an update. Review new proofs with the hostile referee and mathematical-writing plugins; resolve confirmed defects. Keep their reports and process remarks outside the mathematical documents.
- Run the checks appropriate to actual changes. Reuse the existing verification of unchanged sources. Do not rerun the older Lean development as a substitute for proving the new mathematics.
- Finish with a precise account of what was proved, which hypotheses were discharged, which remain, and the next construction to attempt.
