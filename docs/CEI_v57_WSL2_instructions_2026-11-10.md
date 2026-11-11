# WSL2 Codex instructions for version 57

## Division of work

GPT-6.1 Sol Ultra handles the manuscript and its mathematical exposition. Codex handles Lean formalization in `/home/flengyel/src/CategoricalEssentialIncompleteness`, the WSL2 checkout of `flengyel/CategoricalEssentialIncompleteness`.

The current manuscript is version 57. The abstract and introduction review is complete, and formalization can proceed. Version 57 clarifies the ambient categories in introduction paragraph five and updates the version metadata. The mathematical statements, proofs and fifteen open obligations are those audited in version 56.

The independent audit reconstructed all 77 numbered arguments and found no unresolved substantive gap. It inspected the existing Lean source for the 62 retained results and identified fifteen results without complete formalizations. The recorded fresh build and axiom checks cover the existing formalization. Establish the current local status before reporting further results.

## Files supplied

[Version 57 source archive](../manuscript/logical_consequence_v57_source.zip)

[Version 57 PDF](../manuscript/logical_consequence_and_essential_incompleteness_v57.pdf)

[Independent proof audit](https://chatgpt.com/library?file_id=libfile_67e3f345c65081919c94a401eaee76e8&account_id=personal)

[Machine-readable proof audit](https://chatgpt.com/library?file_id=libfile_02cc1afa79c48191a8d7841c955eaff1&account_id=personal)

The source archive contains the manuscript's `latex/` directory. The repository manifest and Lean status table must be reconciled in the checkout.

SHA-256 digests

```text
e29741844891826680520b5a352e963d0f0e6b04035e3943806df159c27d2832  logical_consequence_v57_source.zip
cec565fba1269765999a0f9f431f25beb34fa4e48882643d187d4500a9aa4dcb  logical_consequence_and_essential_incompleteness_v57.pdf
```

## Establish the local target

Set the working directory to `/home/flengyel/src/CategoricalEssentialIncompleteness`. Inspect `AGENTS.md`, the branch, remotes, working tree and newer files. Read `MANUSCRIPT_CURRENT.json`, the active correspondence table, `FORMALIZATION_STATUS_V57.md`, and `manuscript/latex/main.tex` with all its inputs.

Reconcile the supplied version 57 sources and PDF with the checkout. Preserve unrelated changes and verify any already completed obligations. Unpack the source archive into a temporary directory, compare it with the checkout, and integrate the version 57 changes into the repository's existing manuscript layout without replacing newer local work. Update `MANUSCRIPT_CURRENT.json`, source and artifact hashes, and the correspondence target through the repository's existing conventions. If a version-specific status filename is required, derive `FORMALIZATION_STATUS_V57.md` from the current table while preserving every completed and open entry. A change of version or filename does not discharge a proof obligation.

The verifier repair is already integrated in remote main. Begin by checking its regression tests, then continue with the general results below. Reopen manuscript wording only when formalization identifies a concrete mathematical defect. Report the exact statement and failed inference for manuscript correction.

The exported audit was conducted against the available Lean source, pinned to `leanprover/lean4:v4.35.0-rc2`. Inspect the local toolchain pin and dependency manifest. Keep the repository's pinned dependencies and source comparisons. Do not downgrade a newer local state without resolving its relation to the audited source. Run the local verification entry points after reconciliation, using the installed WSL2 toolchain. The snapshot commit and the audited uncommitted manuscript files are distinct pieces of evidence.

## Verify the integrated axiom parser

The independent audit found that the regular expression parsing quoted Lean declaration names stops at an apostrophe. It omits names ending in a prime and can truncate names containing an interior prime. The fresh audit uses corrected parsing of the complete output, so its evidence includes those declarations. It accounts for 25,781 current and 1,274 retained declarations, with zero unchecked reports and only the permitted axioms. The older map loses or truncates 31 full names and introduces two spurious keys.

The WSL2 continuation has already replaced the four expressions below with the shared `parse_axiom_reports` function. Do not reapply this superseded patch. Run `python3 scripts/test_verify_axiom_parser.py` and retain regression cases for `X.foo'`, `X.a'b`, an ordinary name and an axiom-free declaration. Verify that every raw axiom report is accounted for under its full name and that unexpected axioms still cause failure.

```diff
--- a/scripts/verify.py
+++ b/scripts/verify.py
@@ -1454,9 +1454,9 @@
             "current-statement-audit.log")
         text = run(["lake", "env", "lean", "CategoricalEssentialIncompleteness/AxiomAudit.lean"], "axiom-audit.log")
         found = {}
-        for name, contents in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
+        for name, contents in re.findall(r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", text):
             found[name] = sorted(x.strip() for x in contents.split(",") if x.strip())
-        for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
+        for name in re.findall(r"'([^\n]+)' does not depend on any axioms", text):
             found[name] = []
         if set(found) != set(AUDITED):
             raise RuntimeError(f"Axiom audit declaration set differs from the expected {len(AUDITED)} declarations")
@@ -1479,9 +1479,9 @@
                                str(sorted(actual_modules ^ expected_modules)))
         current_axioms = {}
         for name, contents in re.findall(
-                r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", current_text):
+                r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", current_text):
             current_axioms[name] = sorted(x.strip() for x in contents.split(",") if x.strip())
-        for name in re.findall(r"'([^']+)' does not depend on any axioms", current_text):
+        for name in re.findall(r"'([^\n]+)' does not depend on any axioms", current_text):
             current_axioms[name] = []
         if not current_axioms:
             raise RuntimeError("Current axiom audit produced no declarations")
```

## Formalization order

Construct the general adjunctions and their functors first. Then construct the associated-category functors and prove incompleteness transfer. Finally instantiate those results in the arithmetic, Miller and fork examples.

The existing proofs of syntax initiality, substitution, the finite inference endofunctor and its least image provide prerequisites. The table below gives the remaining printed conclusions and recorded obligations.

| Result | Label | Printed conclusion | Remaining construction or proof |
|---|---|---|---|
| 4.4 | `thm:first-order-reflection` | Generation by finite deduction is left adjoint to the inclusion of closed sentence theories, both on subobject orders and on total axiom presentations. | Construct the generation functor and natural hom-set bijection, reusing the existing least-theory image theorem. |
| 4.5 | `thm:translation-galois` | Logical translations give direct-image/closure left adjoint to inverse image and commute with generation and composition. | Define translations and prove closure preservation, the Galois connection, and the two composition laws. |
| 4.6 | `prop:deduction-comparison` | A regular comparison with the stated derivation morphisms gives the commuting generation square and, when present, the restricted right adjoint. | Construct the sentence-derivation comparison, image law, and stated mate construction. |
| 4.7 | `thm:free-first-order-adjunction` | Free first-order signed theories are left adjoint to theorem/refutation-pair extraction. | Define the pair and theory categories, construct both functors, and prove their natural hom-set bijection. |
| 4.8 | `cor:signed-first-order-incompleteness` | A consistent free signed theory is essentially incomplete exactly when its generating pair is inseparable. | Reuse the domain-incompleteness implication; construct the Boolean valuation and complete extension for a separator. |
| 5.1 | `lem:partial-slice-turing` | Partial slices are Turing categories and are split completions of the stated recursion subcategories. | Construct the Turing completion, slice Turing morphism, full recursion subcategory, and splitting equivalence. |
| 5.2 | `thm:theory-extension` | Theory inclusion gives a fully faithful partial-slice functor, its two adjunctions, properness, composition law, and internal-theory comparison. | Define postcomposition/reindexing on partial spans, prove both hom-set bijections and the comparison square. The second unit may be partial. |
| 5.3 | `thm:associated-incompleteness` | Essential incompleteness is equivalent for the original and constant-family theories; inseparability is equivalent to no total extension of the displayed partial Boolean morphism. | Construct the faithful constant-family functor and fibre retraction; prove closure, consistency, completeness, and total-extension transfer. |
| 8.9 | `lem:arithmetic-signed-theory` | The diagonal pair yields an internally consistent and essentially incomplete free signed theory in the PA total splitting. | Formalize the finite-positive-label list, Boolean valuation on both derivations, and PA-provable exclusion of contradictory conclusions. |
| 8.10 | `cor:arithmetic-associated-categories` | Every consistent internal extension of the arithmetic signed theory specializes the associated-category theorem. | Instantiate the extension and incompleteness theorems in the PA splitting, including its full recursion subcategory and faithful functor. |
| 9.6 | `lem:miller-parameterized-deduction` | Miller syntax and initial derivation algebras exist for arbitrary semidecidable nullary coefficients and axiom families in every parameter slice. | Extend the existing recursive-signature construction and prove parameter-stable evaluation and uniqueness. |
| 9.8 | `cor:miller-associated-categories` | Every consistent internal extension of the expanded field theory specializes the associated-category theorem and has the no-total-extension witness. | Instantiate both associated-category theorems and prove the claimed slice inseparability. |
| 10.7 | `prop:fork-first-order-realization` | The fork total category has first-order syntax and initial derivation algebras for arbitrary nullary coefficients, stable under parameters. | Construct the natural componentwise finite-tree folds and prove initiality in every slice. |
| 10.8 | `prop:fork-first-order-conservative` | The first-order fork theory conservatively extends the propositional theory and is internally essentially incomplete; the endpoint conclusions follow. | Construct the erasure and embedding, prove conservativity and consistency, and specialize domain incompleteness. |
| 10.9 | `cor:fork-associated-theories` | Every consistent internal extension of the first-order fork theory specializes the associated-category theorem. | Instantiate partial-slice extension and transfer, retaining the internal sentence and theorem data. |

## Mathematical requirements

Every declaration must express the printed hypotheses, objects, morphisms, equality conventions and quantifiers. Give functors their object and morphism actions, identity and composition laws. Supply natural transformations and their naturality proofs where the manuscript uses them. Prove initiality among all algebra morphisms at the stated types.

The slice functors in Theorem 5.2 have ordinary adjunctions between the underlying partial-map categories. The unit for the right adjunction is partial. Keep the faithful constant-family functor, the fully faithful inclusion functor, and the evaluation/retraction functor distinct. Retain the partial-inverse and parameterized-deduction hypotheses of the general theorem.

The arithmetic consistency argument in Lemma 8.9 is for the free signed theory on the diagonal pair. Its finite Boolean valuation is constructed from the finite proof labels. Formalize that argument at its stated type, including the PA-provable exclusion of contradictory conclusions.

For Lemma 9.6, the inference endofunctor acts on the category over `P × Fm`. The numerical derivation carrier includes positive membership checks for the parameter, the formula and rule labels, and nonlogical axioms. Quantify over arbitrary uniformly semidecidable coefficient objects and arbitrary parameter objects as printed.

For the fork example, variable names form the constant diagram. Atom transitions may identify labels. Prove the conservativity morphism and its naturality under those transitions, then instantiate the associated-category theorem.

Production proofs and their transitive dependencies must contain no `sorry`, `admit`, or dependency on `sorryAx`. The designated Palomar challenge declarations may retain their required proof placeholders as specified below. Do not introduce axioms standing in for the required results or hypotheses that change the printed statement. Reuse the existing constructions and prove the needed compatibility laws. The permitted logical axioms remain `propext`, `Quot.sound`, and `Classical.choice`. Place completed results in the production imports, add the corresponding statement checks, and include their transitive dependencies in the axiom audit. Update each correspondence row only after its declaration and checks compile.

## Palomar challenge declarations and registration

Preserve the designated placeholders for the Lean/Palomar registration. In the Došen–Petrić example, `Challenge.lean` defines the independent statements and contains five intentional `sorry` proof placeholders. `Solution.lean` imports the production module proving those statements, and `comparator.json` names the two modules, the selected theorem declarations, and the permitted axioms. The CEI registration must use its own declarations and designated files.

Inspect the existing CEI registration files and configuration before changing placeholder checks. Record the exact challenge declarations and expected placeholder count. Restrict the exception to those designated declarations. Keep the challenge module outside the production and solution import dependencies. Verify that the solution statements match the challenge statements and that their proofs depend only on the permitted axioms. A successful challenge compilation does not establish those proofs.

Preserve the repository's conventions for registration identifiers and source-link placeholders. Resolve them to verified values for the completed release. Keep registration status and the scope of the selected declarations accurate.

Reference files in [flengyel/Dosen-Petric-Maximality](https://github.com/flengyel/Dosen-Petric-Maximality) are [Challenge.lean](https://github.com/flengyel/Dosen-Petric-Maximality/blob/main/Challenge.lean), [Solution.lean](https://github.com/flengyel/Dosen-Petric-Maximality/blob/main/Solution.lean), and [comparator.json](https://github.com/flengyel/Dosen-Petric-Maximality/blob/main/comparator.json).

## Material for the later Lean appendix

After the formalization is complete, the manuscript can include an appendix explaining the Lean proofs. The example is Appendix D of [the Došen–Petrić version 25 manuscript](https://github.com/flengyel/Dosen-Petric-Maximality/blob/main/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v25.tex), especially its account of reading a Lean declaration and its correspondence between supporting declarations and mathematical proof steps.

During formalization, retain the following information for that appendix.

- The fully qualified name and exact type of each principal theorem, including its parameters, universe parameters, hypotheses, and conclusion, together with the corresponding manuscript result.
- The mathematical meanings of the Lean definitions used in those statements, including any representation by syntax or equivalence classes and the argument order of composition and substitution.
- The supporting declarations for each principal proof and the mathematical step established by each, distinguishing proved facts from hypotheses supplied as arguments.
- A representative theorem statement and proof whose notation can be explained to a mathematician unfamiliar with Lean.
- The division between the independent challenge statements, the solution module, and the production proofs, together with the exact scope of registration.
- The verified source commit or fixed release tag, toolchain and dependency versions, verification commands, and transitive axiom reports needed for accurate source references.

Draft the appendix after these records describe completed proofs. Explain the mathematics and its formal representation, define notation before use, and use source links identifying the verified revision. The manuscript appendix is part of the mathematical-writing work assigned to GPT-6.1 Sol Ultra.

## Local verification

Use the existing repository commands from the checkout root.

```bash
bash scripts/verify-wsl.sh
```

The underlying verifier is `python3 scripts/verify.py`. Its manuscript-only mode checks source and artifact correspondence but does not execute Lean. Preserve that scope distinction in the completion report.

For each completed result, report its Lean declaration, source location, printed statement match, verification command, and permitted-axiom outcome. Retain an open row for every unfinished obligation. Record a concrete mathematical obstruction and the exact failed step if the printed statement cannot be formalized as written.

## Completion record

For each completed result, record the declaration names, source files, statement checks, dependency and axiom checks, and verification command outcome in the correspondence table. Keep all unfinished rows open. Report the number of completed and remaining obligations after each verified group.

Run the full repository verifier after integration. Distinguish the supplied audit's earlier evidence from the local commands executed in this session. Record the local commit and working-tree state alongside the verification result. Follow the repository's instructions for commits and preserve the user's existing work.


## Commit and push requirement

Commit all completed changes to `main`, push to `origin/main` without force,
and verify the remote commit and active manuscript version before reporting
completion. The v57 manuscript is now supplied in the repository; preserve
subsequent local and remote Lean work during reconciliation.
