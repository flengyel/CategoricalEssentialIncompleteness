# Independent first reading, v85

Logical consequence and essential incompleteness in recursion categories, version 85, 24 November 2026. Commit 3c74686045c1a74079d5d13ba16f72f525be9b3a. The source set is the 25 TeX files under manuscript/latex. Reviewed the manuscript and its own Appendix E independently of Lean files, correspondence, and older project reviews. The Stanford report by Knuth, Larrabee and Roberts was consulted as the editorial standard.

## Actual outline


1. Introduction — Question, principal equivalences, hypotheses, three examples and antecedents.
  - Related work

2. Categorical preliminaries — Restriction structure, subobject operations, computational parameterization.
  - Partial maps and restriction idempotents
  - Products, coproducts, and local connectedness
  - Recursion categories

3. Diagonal comparison and complementary conditionals — Diagonalize a lifted conditional; infer source inseparability.
  - The comparison theorem
  - Complementary conditionals

4. Internal theories and essential incompleteness — Deduction and interpretation; two-way relation between inseparability and free-theory essential incompleteness.
  - Theories and their interpretation
  - Incompleteness from semantic consistency
  - Inseparability in the source
  - Generation and logical translations
  - Change of the ambient category
  - Free first-order theories and inseparability

5. Theory extensions and recursion categories — Partial slices, inclusions, double adjunction and evaluation at a logical theorem.
  - Categories associated with internal theories
  - Functoriality under theory extension
  - Essential incompleteness in the associated category

6. The syntactic recursion category — Arithmetize programs, syntax, substitution, and finite proof initiality.
  - The total restriction splitting
  - Syntax and lists
  - Free variables and substitution
  - Derivations and theories

7. Interpretation and soundness — Interpret graphs in arithmetic models; derive standard and ultrapower soundness.
  - Lifting complementary conditionals
  - The total interpretation functor
  - Soundness on standard codes
  - Ultrapowers of the interpretation functor

8. Essential incompleteness of arithmetic — Use the comparison on PA, uniformize independent sentences, compare proof codes, and apply the slice theorem to the separate signed language.
  - Comparison in the fixed syntactic category
  - An indexed family of arithmetic theories
  - Uniform independent sentences
  - The numerical realization
  - Numerical incompleteness
  - Numeral instances and theory extension
  - The associated recursion categories

9. Miller sequences and essential incompleteness — Transfer the diagonal pair to the half-interval cuts of a Miller sequence and then to its ordered-field theory.
  - Computation independent of the binary representation
  - The index sets below and above 1/2
  - A theory of real closed fields
  - The associated recursion categories

10. A recursion category from a three-point space — Build the diagram-category example, endpoint propositional incompleteness, its conservative first-order extension and slice consequence.
  - Complementary restriction idempotents and inseparability
  - Evaluation functors
  - Propositional theories and component theorem sets
  - First-order theories in the functor category
  - Categories associated with theory extensions

A. Syntax and deductively closed theories — Abstract syntax, admissible substitution and initial rule algebras giving least theories.
  - Categorical hypotheses and notation
  - Terms, formulas, and free variables
  - Admissible substitution
  - Inference rules and deductively closed subobjects
  - First-order theories
  - Propositional theories

B. The three-point cosheaf construction — Build the realization in its functor category and separate it from the numerical recursion category.
  - Cosheaves and functor categories
  - Partial maps, ranges, and connected restriction idempotents
  - A universal object and a frame
  - A Turing morphism
  - The recursion category and its splitting

C. Necessity of section lifting for inseparability — Construct a faithful inclusion for which a target conditional admits no source lift, disproving a prior statement.

D. Faithful model interpretations and theory extension — Separate program classes through all countable models and compare theory extension and numeral provability.
  - Inseparable pairs under theory extension
  - Provability of numeral instances
  - The theory of the standard model

E. Reading the Lean proofs — Explain the Lean correspondence for selected proof steps, retaining distinctions between categorical and numerical languages.
  - Restriction and extension of an interpretation
  - Separators and complete extensions
  - One valuation for two derivations
  - The lift of a conditional
  - Evaluation of a theory in the slice
  - A uniform choice of independent sentences
  - Finite proofs and the theorem domain for a Miller sequence

## Findings and exact references

1. §8.7, Lemma on the theory of the diagonal pair: the first half repeats Turing diagonalization and separator pullback. Corollary of §7.1 for PA and the standard model plus the fact that the restriction-idempotent orders on identity splittings are unchanged supplies precisely the required pair. Retain the second half proving internal consistency with a joint finite support.
2. §9.3, theorem on Miller incompleteness: after the two signed bounds, use the domain-incompleteness corollary, consistency, and the unchanged source endomorphisms. The existing proof reconstructs the entire corollary. Retain extraction of an actual independent sentence from the proper numerical union. The same repeated reductio in §10.4 can likewise be cited after the reductions; preserve the endpoint pullback proof.
3. §6.3, numerical substitution: the implication and quantifier codomain operations are exactly A.3’s operations. Reference those constructions, keeping the primitive-recursive traversal, the bound-variable and failed-child behavior, and the proof of its categorical identity. Its final paragraph independently proves the identical identity/absent-variable equations already implied by A.3 once the two folds agree.
4. §4.1/§4.4 vs A.2/A.3: j denotes the sentence inclusion in the main exposition and the admissibility inclusion in Appendix A. The appendix calls the sentence inclusion s. Use j for sentences and i_Adm for admissibility; change the corresponding pullback labels, instantiation/equality parameter pullbacks, and q0=[λ,j i_A], but respect unrelated local j or s. These are genuinely different types. Φ vs Fm are explicitly identified and are optional harmonization.
5. §10.3 defines q0,q1 as conjugated summand idempotents on V before writing q0=λ:Ax→S in the very same subsection, which later additionally uses q_j for slice projections. Rename just the two idempotents ε^V_i.
6. Appendix B.3 chooses tuple bijections γ_n:N^n→N, then B.4 chooses encode_n and decode_n for exactly the same purpose; use the former family and inverse throughout §§B.3–B.4 and §10.2, retaining code_m for words, whose domain differs. §8.5 likewise explicitly sets A=D₀ and B=D₁, then a=1_A,b=1_B, all duplicates of already named numerical sets and partial identities. D₀,D₁ suffice for §§8.5–8.6.
7. Remove the final narration in the statement of §9.4’s corollary (the assertions already specify the instance). §10.3 repeats the three displayed Hilbert schemes of A.5 in full; point to the three existing equation numbers at the definition of the component schemes. §4.6’s sentence about precomposing a generalized index repeats associativity alone. Neither a global deletion of all repeated hypotheses nor a reorganization is called for.
8. Important meaningful repetitions. Signs and consistency in theorem statements, the finite common support for two proofs, the actual computation tying numerical proofs to categorical fibers, and preservation under pullback vs preservation under arbitrary functors are mathematical content. An argument about internal proper subobjects need not supply a global sentence; §4.3 explicitly explains this and the numerical extraction in §9 is stronger.

## Central scope

The free signed-sentence construction is characterized on the subcategory of disjoint pairs generating consistent theories; the corresponding existence of a complementary separator is exactly the existence of a consistent complete extension under the stated hypotheses. The associated-category result requires a fixed theorem point and parameterized derivation algebras. No missing mathematical hypothesis in either implication was established by this manuscript-only reading. The two computations used in the Miller category are uniform over representations, while actual separators for the cuts may depend on the representation. No claim of proof-assistant replay is part of this first reading. Source-line checks, literature/Lean verification, and PDF comparison follow separately.
