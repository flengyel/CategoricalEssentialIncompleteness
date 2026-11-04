# Writing review of the v46 correspondence notes

Scope: the changed correspondence rows and implementation notes for the
4 November 2026 proof batch. The manuscript's mathematics and layout are
not revised. This is not a whole-paper editorial review.

The governing source consulted was Knuth, Larrabee and Roberts,
[*Mathematical Writing*, Stanford report CS-TR-89-1193](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1 and the definition-placement discussions in §§4–5. The applications
below concern self-contained statements and consistent notation, following
§1 points 5 and 14. The report format is the supplied skill's workflow,
not a format prescribed by that source.

The current manuscript order is introduction; categorical preliminaries;
diagonal comparison; interpreted theories; syntactic recursion categories
and internal syntax; model interpretation; arithmetic; Miller sequences;
the three-point application; Appendices A–D; bibliography. The changed
notes follow the proof dependencies: generic list/substitution foundations,
concrete finite records, partial model search, numerical carriers, and
application/coherence consequences. No reordering of the manuscript is
proposed.

| Anchor | Difficulty | Principle and repair |
| --- | --- | --- |
| Prior correspondence table, Definition A.1 | It still said generic admissible substitution was pending, although its A.3 row and the verified construction stated the opposite. | Independent consistency finding. Distinguish the proved construction under Definition A.1 from the pending concrete initiality realizations. |
| Prior table, unnumbered predicate-equivalence row | A pending status contradicted the completed numbered 5.3 row. | Independent consistency finding. Name the actual equivalence, regularity/extensivity and mono-inverse declarations. |
| Lemma 5.1 and new model search notes | A change of numerical coding could otherwise be confused with literal equality. | Consistent notation and explicit types. State the square/pair-tag production coding, prove the actual even/odd source and model comparisons, and retain the exponential-product/uniform-trace gap. |
| New parity partial-graph description | Exactness depends on disjointness in the selected model. | Self-contained statement. State that condition in the row itself; the encoding/decoding isomorphism does not require it. |
| Concrete list notes | Internal nonstandard codes and ordinary set lists have different universal properties. | Independent typing rationale. State initiality in the actual predicate slices; describe the auxiliary set functors by the finite geometry and faithfulness they prove. |

Notation is fixed before use in the implementation report: `V46` is a
namespace abbreviation, `E:D≌Tot(R)` is an equivalence of total categories,
and source morphisms compose left to right in Lean. The records retain
index versus function, total versus partial morphism, and code-model
versus represented-language distinctions. Existing v5 records remain
historical.

The changed correspondence rows and implementation notes were read
continuously after the proof sources were frozen. The final verification
and source-identity paragraphs are checked against their recorded outputs
before delivery. No new literature claim, manuscript
version, PDF compilation or rendered-page inspection is claimed here.
