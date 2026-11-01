# Focused writing and dependency review — v21

*Logical consequence and essential incompleteness in recursion categories*, version 21. Scope: the complete integrated files `sections/06-interpretation-in-models.tex`, `sections/08-essential-incompleteness-of-arithmetic.tex`, `appendices/d-faithful-family.tex`, and the assembly order in `main.tex`. Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1, was consulted in the supplied full text `tmp/review_sources/klr.txt`.

The new order supports the argument: syntactic realization precedes interpretation and soundness, which precede the arithmetic comparison. The faithful-family material has moved with the observation argument that needs faithfulness. No structural blocker or invented mathematical terminology was found in this scope. The three narrow clarifications identified below have been applied by the parent. No realization proof should be removed.

## Actual outline and function

The main assembly is introduction; preliminaries; diagonal comparison; internal theories; syntactic category and realization; interpretation and soundness; arithmetic; Miller sequences; cosheaves; Appendices A–D.

| Reviewed part | Function and principal dependencies |
|---|---|
| §6 opening graph interpretation | Defines `F_M` and proves structural preservation from the arithmetized graph identities. |
| §6.1 Lifting complementary conditionals | Proves one program supplies the modelwise complementary switch; applies the locally connected target theorem. |
| §6.2 Total interpretation | Defines the extension to the splitting and `G_M`; proves finite-limit, coproduct, and regular-image preservation using the predicate equivalence. |
| §6.3 Standard-code soundness | Keeps the numerical model and semantic structure distinct; proves semantic substitution and finite-derivation soundness. |
| §6.4 Ultrapowers | Defines the Set ultrapower functor, proves preservation, constructs the natural comparison on the actual total category, and transfers the full proof-conclusion factorization. |
| §7.1 Fixed syntactic category | Defines the represented axiom and theorem objects, proves diagonal reductions and partial proof-search lifting, then invokes the general comparison. |
| §7.2 Numerical realization | Constructs `Rec`, establishes its inseparable pair, retains the full regularity/syntax/substitution/derivation realization, and applies the source-domain corollary. |
| §7.3 Numeral instances | Defines the pair category and extension functor used by the later cosheaf application; gives the Bernardi comparison. |
| Appendix D opening | Constructs the faithful model family and ambient-theory extension square. |
| D.1 Inseparable pairs | Retains the extension result and the limitations of the all-model target. |
| D.2 Numeral observations | Uses faithfulness in the second observation equivalence; states the c.e. hypothesis needed for enumeration. |
| D.3 Complete ambient theory | Preserves the distinction between computational inseparability and incompleteness of the ambient theory. |

## Local clarifications — resolved

Line numbers below are from the integrated source as first read; the parent reports all three repairs applied. The ultrapower theorem also now states the nonempty-index-set and proper-ultrafilter hypotheses directly.

| Anchor | Difficulty | Governing source or rationale | Repair |
|---|---|---|---|
| `prop:standard-code-soundness`, §06 lines267–277; used at lines437–439 | The proposition starts with “There is a unique function,” leaving Γ, A and K in the preceding text; the later theorem refers to the proposition’s “hypotheses,” which are not stated inside it. | KLR §1 point5 recommends self-contained theorem statements; this later reference makes the missing statement-level scope consequential. | Begin the proposition: “Let Γ be a computably enumerable set of arithmetic sentences, let A=A_Γ↪S be its axiom subobject in B_PA, and let K⊨Γ. For the validity inclusion v_K:V_K↪G_N S defined above, there is a unique function …”. Keep the existing maps, factorization, and negation conclusion. |
| §08 lines40–42 | “Under the standard interpretation G_N, the carrier P_Γ consists …” uses the internal object’s name where the interpreted set is meant. | Explicit object/interpretation typing; KLR §1 points11 and14 support defined, consistent notation. | “The set G_N(P_Γ) consists of the codes of finite derivations from Γ whose conclusions are sentences.” |
| §08 lines282–289 | A definition of ζ intervenes between A,B and “Their recursive inseparability.” | KLR §1 point17: left-to-right unambiguous reading. | Replace “Their recursive inseparability is another instance of …” by “The recursive inseparability of A,B is another instance of …”. |

## Definition order and typing

Confirmed distinctions:

- The variable object is explicitly `(ω,1_ω)∈B_PA`; its standard interpretation is `N`.
- The external set of axioms Γ and the internal subobject A_Γ are different named objects.
- `P_A` and its sentence-conclusion pullback `P_{A,S}` remain separate.
- `V_K` and its ultrapower are subobjects in `Set`, not claimed to be objects of the arithmetic predicate category.
- The natural comparison is transported through `J_PA:P_PA→B_PA`; the equivalent categories are not identified silently.
- Partial theorem idempotents are interpreted by `\widehat F_M`, while total syntax and conclusion morphisms are interpreted by `G_M`.
- The new arithmetic application concludes source noncoverage from target disjointness; it does not reflect zero or claim PA-provable source consistency.
- The numerical realization explicitly states the equivalence with `C_rec` and transports restriction-monomorphism claims through it.
- `Pair(Rec)` remains defined before its cosheaf use. The numeral-observation equations remain together with the faithful functor they use.
- The separate complete-ambient-theory subsection prevents the c.e. assumption of the preceding observation subsection from being silently imposed on `Th(N)`.

No new editorial/process commentary was found in the reviewed mathematical text. “Standard codes,” “predicate presentation,” “partial proof-search lift,” and the explicitly displayed conditional describe their mathematical constructions; no additional terminology is needed.

One dispensable proof-ending sentence is §06 lines431–432: “This constructs the stated natural isomorphism without identifying the two equivalent categories.” The preceding construction and naturality/independence argument already establish its content. Deleting that sentence is a small economy improvement, not a mathematical correction.

The repeated axiom-presentation definitions in §§6–7 serve the two local arguments; no consequential duplication requires removal. The full numerical realization has a distinct purpose from the `B_PA` realization and should be retained. No alternative outline is warranted.

## Scope

The three indicated source files and assembly order were read completely. Targeted earlier definitions of the predicate category, restriction-idempotent notation, and Turing evaluator were checked. This is a prose, typing, and dependency review of the new integration, not an independent proof certification of the whole manuscript. The separate mathematical agents checked the new soundness and arithmetic proofs. This reviewer did not compile or inspect rendered PDF pages; the parent owns those checks. The introduction, abstract, and Appendix A were not edited.
