# Syntax and interpretation prose pass

Scope: Version 46 working source of *Logical consequence and essential incompleteness in recursion categories*: `sections/05-syntactic-recursion-category.tex`, `sections/05a-internal-syntax.tex`, and `sections/06-interpretation-in-models.tex` only. Read the c20 mathematical-writing skill and its two references, the supplied KLR text (Section 1, relevant comments in Sections 4–5, and Lamport's handout in Section 32). Read the three owned files completely before and after the edits. No whole-manuscript judgment or independent correctness certification is claimed.

## Existing outline and mathematical functions

| Portion | Function and dependencies |
| --- | --- |
| Syntactic recursion category | Define object codes, uniformly provable graph equality, restrictions and ranges; identify the set presentation and distinguish the defective pointwise quotient; construct the Turing morphism. |
| Total restriction splitting | Define the predicate presentation and witness search; prove its equivalence with the total splitting, regularity, coproduct properties and partial inverses; establish the partial-map and Turing-category structure. |
| Syntax and lists | Construct sequence and syntax codes, then prove separate parameterized initiality results for arbitrary internal algebras. |
| Free variables and substitution | Identify numerical operations with the categorical folds and prove the free-for domain and substitution identities. |
| Derivations and theories | Construct the inference initial algebra and conclusion map, then identify the generated sentence theory with a restriction-idempotent splitting. |
| Interpretation and soundness | Define the model interpretation before proving its functoriality; lift conditionals; interpret the total category; prove soundness on standard codes and transfer it to an arithmetic ultrapower. |

The paragraph pass retained definitions, hypotheses, constructions, proof steps, comparisons, and applications. No section reordering was warranted.

## Implemented edits

| Anchor | Difficulty | Repair and basis |
| --- | --- | --- |
| Section 5, numerical coding identities | A closing sentence only restated which identities had just been given. | Deleted the recap. Economy is the current editorial remit; KLR Section 1(10–11) supports connected explanation and complementary, rather than merely repeated, statements. |
| Total splitting, finite-membership proof, syntax-initiality introduction, and monomorphism proof ending | Repeated announcements and conclusions added no mathematical step. | Removed the announced "required properties," the repeated attribution of an already specified induction to PA, and the final monomorphism/subobject recaps; stated the syntax induction directly. |
| Derivation fold | A sentence repeated the preceding explanation by decomposition and concatenation of value lists. | Kept that explanation before the displayed equivalence and deleted its repetition afterward. Replaced the negative warning about totality on arbitrary numerical inputs by the positive assertion of T-provable totality on the carrier of H(Q,q). |
| Short unreferenced formulas | Several object/type declarations and short predicate definitions interrupted sentences. | Made selected formulas inline; retained numbered formulas, central constructions and longer equations. Updated the local universal-quantification convention to cover the constructor equivalence after moving it inline. This implements the user's inline default while preserving KLR Section 1(16)'s purpose for significant displays. |
| Complementary-conditional relation R(x,z) | The display had a period before the continuation "is T-provably functional and total." | Removed the premature period. Kept the root's use of functional search, the T-provable totality claim, and the entire model/unique-section verification. |
| Semantic substitution and ultrapower prose | A closing case-exhaustion recap and an adjective added no premise. | Removed the recap and "usual" from the set-theoretic metatheory; preserved choice and all model assumptions. Shortened the decoded-expression sentence without removing the distinction between the code model N and the semantic structure K. |

All author credits and citations remain, including Montagna/DPM, Robinson/Rosolini, and Keisler/Łoś. The separate syntax and list initiality proofs retain arbitrary parameter objects and internal algebras, induction in T, and uniqueness among T-provable morphisms. All source predicates, arrow types, numbered equations, and total/partial distinctions remain.

## Definition and notation checks

The object term algebra and numerical codings precede graph equivalence; functional search precedes its uses; the predicate category precedes its equivalence with the total category; syntax and list objects precede substitution; sentence and derivation objects precede the theory construction. The arithmetic model M is fixed before F_M. N as the model of codes and K as the structure interpreting decoded formulas remain explicitly distinguished. No new terminology, hypotheses, citations, or notation were introduced.

## Deferred duplication candidates

- The specialized search defining [C]_T in Section 5 and the general functional-search proof in the next subsection share a witness-search construction. Consolidating them would require moving the general lemma before the construction of S_T; no forward dependency was introduced in this pass.
- Replacement of coordinates outside an ultrafilter member occurs in the equalizer proof, arithmetic-predicate comparison, and final semantic-membership description. A general statement for arbitrary inclusions could consolidate this technique, but the current proofs have different conclusions; this pass retained their short local explanations.

Verification: compared the edited sources with the version-45 frozen sources, confirmed unchanged label and citation sequences, checked paired LaTeX environments/display delimiters and even inline-math delimiters, and continuously reread the edited portions. Compilation and rendered-page checks are left to the root agent's combined build.
