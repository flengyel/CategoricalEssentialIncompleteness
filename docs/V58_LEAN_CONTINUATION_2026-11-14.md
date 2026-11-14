# Codex continuation: formalization of manuscript v58

Continue the Lean formalization of **Logical consequence and essential incompleteness in recursion categories** in `flengyel/CategoricalEssentialIncompleteness`. Complete the remaining part of Theorem 5.3 first. Preserve completed proofs and all later local or remote work. Keep completed work committed and pushed to `main`.

## 1. Establish the current state

This brief was prepared against remote `main` at `04f4013a5c6c2c568d0e2d4bb0b9ed9ec24433a5`. That commit contains the v58 impact audit. It is a reference point, not an instruction to reset a checkout. The active manuscript is v58. At this reference point, 69 of its 77 numbered results have proved counterparts; eight remain open.

The usual checkout is `/home/flengyel/src/CategoricalEssentialIncompleteness`. Inspect it before changing anything:

```bash
git status --short --branch
git fetch origin
git log --oneline --left-right HEAD...origin/main
```

Preserve local modifications, untracked work and concurrent remote commits. Do not reset, discard or overwrite them. Reconcile the current checkout with `origin/main` before integrating a new proof batch. Read the current status rather than reverting to the counts in an older report.

Read these files in order:

1. `AGENTS.md` and `MANUSCRIPT_CURRENT.json`.
2. The correspondence table selected by the manifest, presently `FORMALIZATION_STATUS_V58.md`.
3. `manuscript/latex/main.tex` and its inputs; for the first task, read Sections 4–5 and Appendix A closely, including all standing hypotheses.
4. `docs/reviews/V58_REVIEW_2026-11-14/lean-impact.md` and its three linked detailed reports.
5. `docs/V57_ASSOCIATED_RETRACTION_2026-11-14.md` and its verification JSON, together with the preceding theory-extension report.
6. `docs/CEI_v58_WSL2_instructions_2026-11-14.md`. Consult `docs/V57_LEAN_CONTINUATION_2026-11-10.md` for earlier construction details; its intermediate proof counts are superseded by the current table.

Use the existing module and namespace names. The `V46` prefix does not select the manuscript version.

## 2. Preserve the v58 mathematical conventions

- **Initial derivation algebras are required only for axiom subobjects.** The principal `FirstOrderPresentation`, `NullaryPresentations` and `FirstOrderReflection` interfaces already have this scope. For an arbitrary axiom morphism `a : A ⟶ S`, generate from `imageSubobject a`. Do not infer initiality for `a` from initiality for its image. Older interfaces with stronger hypotheses may be used only where those hypotheses are separately proved or expressly available.
- **Truth is the second coproduct injection.** Preserve `Two.point true = coprod.inr` and the existing true/false fibers.
- **Nullary Boolean quantification is the second projection.** Preserve `NullaryBooleanValuation.quantifier_value` and its independent check.
- **Lemma 6.1 is already formalized.** `UniformTrace.composition_PA` proves the same-evaluator identity uniformly for arbitrary internal indices. Its compiler differs from the proof paragraph's chosen compiler. Do not replace a proved construction merely to obtain identical numeric indices, and do not claim the literal equation between those two compiler choices without a new proof. The existing statement and its primitive-recursive and PA-totality certificates remain the target.
- The v58 revision changed none of the 77 numbered result statements or three numbered definition environments. It corrected Appendix B's local decidable-equality convention to the existing Appendix A and Lean convention. No further manuscript correction was identified by the impact audit. Do not rewrite the manuscript merely to simplify formalization. If an actual defect emerges, identify the exact statement, obstruction and necessary correction before synchronizing the corresponding manuscript and Lean changes.

## 3. First task: complete Theorem 5.3

Target `thm:associated-incompleteness` in `manuscript/latex/sections/04-theory-extensions.tex` under exactly its standing hypotheses. Here `C = Split(R)`, `D = Tot(C)`, `C[U] = Par(D/U, Mono)`, and `u : U ↪ S` is a consistent internal sentence theory. The fixed logical theorem `λ : 1 → S` factors through each theory considered. The constant-family functor is `B_U`, and `E_U` is pullback along `λ_U : 1 → U`, followed by the base equivalence.

Already proved: the actual evaluation functor and natural retraction `E_U B_U ≅ Id`; restriction preservation; faithfulness and totality reflection; preservation and reflection of total extensions; the Boolean partial morphism, its values and domain; both displayed Boolean equivalences; and the no-total-extension witness from total subobject reduction bounds.

Reuse the producers `V46AssociatedEvaluation`, `V46AssociatedBooleanDecision`, `V46AssociatedExtensionWitness`, `V46ConstantFamilyRetraction`, `V46RestrictionRetraction`, and `V46BooleanPartialDecision`, and inspect `V46AssociatedCategoryChecks`. Do not reimplement these results. Also inspect the proved deduction comparison, mate, reflection and translation interfaces before adding another abstraction.

The remaining construction is:

1. **Identify the deductive systems and their comparison morphisms.** The sentence family is `U × S → U`, the theory is `1_U × u`, and negation is `1_U × ν`. Keep the original system, its parameterized syntax and its slice realization connected by explicit morphisms and equations. An unrelated slice presentation does not establish the printed theorem.
2. **Prove preservation of closed theories in both directions.** For an arbitrary closed sentence theory `v`, use its closed formula subobject `C(v)`. Transport the finite rule diagrams to construct a rule algebra containing the transported axiom subobject. Apply the supplied initial derivation algebra for that subobject; prove the conclusion factors through the transported closed formula subobject. Take regular images and restrict to sentences. Establish each preservation fact used for products with `U` and for pullback along `λ_U`.
3. **Prove preservation of consistency and completeness.** Identify the transported negation and refutation subobjects and the required intersections, joins and top subobjects. Derive the preservation statements using the actual finite-limit, regular-image and finite-coproduct comparisons. Carry the relevant base-theory inclusion through the natural retraction.
4. **Transport arbitrary consistent complete extensions.** A base extension is sent forward by `B_U`. An arbitrary closed consistent complete extension `W ≥ B_U(u)` in `D/U` is sent back by `E_U`; `W` need not be a constant family. Use `E_U B_U ≅ Id` to identify the resulting base theory. Prove the full essential-incompleteness equivalence with its complete extension quantifiers and the definitions already used by the project.
5. **Complete the final reduction clause.** Starting from the printed total reduction of an inseparable pair to the theorem/refutation subobjects of `t`, use Corollary 4.3 and the established comparison results for every consistent extension `u ≥ t`. Prove essential incompleteness of the associated theory as well as the no-total-extension conclusion. Reuse the existing witness theorem for the latter.

Do not supply closure preservation, consistency preservation, the desired equivalence, or a complete extension transport as new hypothesis fields. Do not assume that either functor preserves initial algebras. The proof uses initiality to map into a transported rule algebra. Do not add initiality for arbitrary axiom morphisms, complementedness of `λ_U`, or global elements for arbitrary objects.

Before implementing, write a short proof outline matching these five steps to the existing declarations and the remaining lemmas. Have an independent review check the transported-theory types and the arbitrary-slice-extension quantifier. If a step fails under the printed hypotheses, isolate the failure instead of weakening the theorem or hiding it in an interface.

## 4. Remaining results after Theorem 5.3

Use the current table's exact statements and labels. The following describes dependencies, not replacement statements.

| Result | Remaining construction |
| --- | --- |
| 8.9 | Internal consistency and essential incompleteness of the free theory generated by the arithmetic diagonal pair. |
| 8.10 | Arithmetic instance of the associated-category theorem. |
| 9.6 | Parameterized syntax and initial derivation algebras for arbitrary coefficient objects in the Miller category. |
| 9.8 | Miller instance of the associated-category theorem. |
| 10.7 | First-order syntax and derivation initiality in every parameter slice of the fork category. |
| 10.8 | First-order embedding and erasure, conservativity, consistency, essential incompleteness and the printed endpoint conclusions. |
| 10.9 | First-order fork instance of the associated-category theorem. |

Complete the prerequisite before its application. Keep all eight current rows open until their complete statements are proved. Theorem 5.3 alone advances the count from 69 to 70 only after every clause has passed its checks. Partial lemmas are progress, not completion of a numbered result.

## 5. Proof and verification requirements

Preserve the pinned toolchain, dependency manifests, source provenance checks and permitted-axiom policy. Production proofs and their transitive dependencies must not use `sorry`, `admit` or `sorryAx`. Leave the separately configured Palomar challenge placeholders and their isolation intact. The only permitted logical axioms are `propext`, `Quot.sound` and `Classical.choice`.

For each completed result:

- Construct the result in a production module and connect it to the existing definitions.
- Add an independent statement check with the complete printed hypotheses and conclusion. Check the full essential-incompleteness quantifiers, not merely an implication or the Boolean consequences.
- Import the producer and check through the manifest-selected production and statement entry points; retain complete transitive axiom coverage.
- Run strict elaboration and the relevant checks, then the required integration verification. Preserve command lines, exit statuses, source hashes, dependency state and logs. A build success alone does not establish correspondence with the printed statement.
- Update the current correspondence row only when the complete result and its checks pass. Record partial progress separately and leave the row open.

Run from the repository root:

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

The parser repair is already integrated; do not reapply it. The manuscript-only command does not execute Lean. The WSL wrapper uses a build lock and `LEAN_NUM_THREADS=1`; do not start competing builds or full replays in the same checkout. Given the reported memory pressure, use serial compilation through the established workflow and record an interrupted or failed run accurately. If moving to another machine, restore the same pinned dependencies and verify the same source bytes there.

The v58 impact audit ran no fresh Lean build. Its source comparison found 2,377 Lean and verification-input blobs identical to proof commit `f147a49ecddc87509b02156a912b0b0dbbdbce68`. That commit has an incremental verification record; the preceding full baseline is `45a8a6d017850a3a68fcecd01ad82f5a1a83674a`. Keep these distinct from any new run. Report incremental verification as incremental and a full replay as full only when the full command completes successfully. A later documentation change must be distinguished from the exact tested proof revision.

## 6. Commit and delivery

Commit and push each completed, verified proof batch promptly to `main`; do not accumulate several finished revisions only in a remote session or worktree. Preserve concurrent work and use a non-force push. If interrupted before a result is complete, preserve a compiling checkpoint and clearly record its unfinished obligations rather than marking the result proved.

For proof-only changes, update the current correspondence and verification records without gratuitously rebuilding or changing the manuscript. If manuscript text changes, synchronize the source, PDF, source archive, manifest, correspondence and current instructions together and run the manuscript checks.

After integration, fetch and compare local `main`, `origin/main`, and the live branch hash:

```bash
git fetch origin
git rev-parse main origin/main
git ls-remote origin refs/heads/main
git show origin/main:MANUSCRIPT_CURRENT.json
git status --short --branch
```

Report the remote commit, the exact completed mathematical result, verification scope and outcome, remaining open results and any preserved unfinished work. Do not describe the entire manuscript as formalized while any of its numbered results remains open.
