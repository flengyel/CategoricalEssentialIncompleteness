# Lean continuation requested for manuscript v57

The active target is manuscript **v57**, supplied on main by
`c61105d` after the earlier v51 verification reported below. The manifest,
24 TeX source files, PDF and source archive now agree. The archive was
unpacked into `/tmp/cei-v57-source-50vjv_yr`; every TeX file matches the
checkout. Both artifact hashes match the supplied WSL2 instructions.
`python3 scripts/verify.py --manuscript-only` passes for v57. This source
check is distinct from Lean verification.

The v57 implementation batch constructs Theorems 4.4 and 4.5 and
Proposition 4.6 with their printed hypotheses. The full v57 verification passed at
`c93832d761347607906b11615bd56cb937cdfdff`; its measured inputs and
command results are recorded at the end of this report.
The other twelve added results remain open. No manuscript source, artifact,
mathematical statement or proof has been edited in this batch.

The following sections preserve the preceding v51 development and
verification record. At the start of that phase, the v57 archive and PDF
were unavailable; `origin/main` selected v51 at
`de1466ac2fd820ed06931c467083a79f0481f84c`.

The checkout was fast-forwarded from `c5d7d0e` to that available main commit.
Before integration, the available v51 source archive was extracted to a
temporary directory and compared with the checkout. SHA-256 checks confirmed
that all 2,195 modified or untracked inputs present before integration were
preserved byte-for-byte. The comparison and preservation records are under
`.codex-work/v57-continuation-20261110/`. This comparison concerns the
available v51 archive, not the missing v57 archive.

The initial parser repair was committed and pushed as
`27695edc63647b4f624798aeeb4f72c284e4b4b1`. The proof sources, module-port
repairs, Lake-prefix regression case and expanded source measurements
described below are subsequent changes. Their integrated verification is
recorded below.

## Verifier repair

The four declaration-name capture sites in `scripts/verify.py` have been
replaced by the shared `parse_axiom_reports` function. Both retained and
current audits now capture through the closing quote preceding the report
suffix, preserving terminal and interior apostrophes. An independent check
of the raw report lines rejects skipped, truncated or repeated names.
Unexpected axioms are still rejected against the unchanged permitted set:
`propext`, `Quot.sound`, `Classical.choice`.

`python3 scripts/test_verify_axiom_parser.py` passes six regression tests.
They exercise ordinary names, terminal primes, interior primes, axiom-free
declarations, distinct declarations that would previously collide, rejected
axioms, malformed reports, duplicate reports and Lake message prefixes.
The established full
verifier runs these tests and measures their source with its other inputs.
Its source snapshot now also measures the contained Lean modules changed
by the module-system port, excluding dependency build trees and continuation
working directories. Their imported-source provenance checks are retained.

The preserved raw evidence from
`.codex-work/verify-20261109T102738Z-KM4dao/build-logs/` was reparsed without
running Lean or modifying the evidence:

| Raw log | Complete declaration names | Names containing apostrophes | Axiom union |
| --- | ---: | ---: | --- |
| `axiom-audit.log` | 1,274 | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| `current-axiom-audit.log` | 25,781 | 31 | `Classical.choice`, `Quot.sound`, `propext` |

The previous parser recorded 25,752 current names. It lost 31 complete names
and introduced the two truncated names `.eq_1` and `_1`. Reports for names
common to both parses agree. Complete name-to-axiom maps and raw-log hashes
are retained in `axiom-parser-raw-evidence-reparse.json` in the continuation
working directory. These corrected counts describe a reparse of the v48
raw evidence for proof commit `d437827275d64f6500e6a3bca2ee318420d11edd`;
they do not constitute a new Lean verification or a verification of v57.

## Build state and remaining results

The Lean toolchain and dependency manifest are unchanged. All sixteen
dependency worktrees are clean and match their pins. The unfinished
module-system port is preserved. Its development build runs through the
existing lock with `LEAN_NUM_THREADS=1`; module visibility repairs retain
the mathematical definitions, statements and proofs.

The available v51 manuscript-only gate passes. At that stage, full verification against
v57 awaited its sources and the proof batch. The fifteen requested results
were open: 4.4–4.8,
5.1–5.3, 8.9–8.10, 9.6, 9.8 and 10.7–10.9. No correspondence row has been
marked complete on the basis of the parser repair or a manuscript-only gate.

## Generation adjunction implementation

`V46FirstOrderGeneration.lean` and `V46FirstOrderGenerationChecks.lean`
compile. Both also pass independent raw Lean checks with
`-DwarningAsError=true`. They are integrated into the production imports,
both combined statement imports, and the current transitive axiom audit.
This earlier implementation had not yet been compared with the printed
v57 assumptions. Its stronger initiality premise is corrected by the
`FirstOrderReflection` construction recorded below.

The construction quantifies over a regular category `D` with finite
coproducts, variable object `V`, formula object `F`, logical-axiom coefficient
object `L`, sentence object `S`, and the logical, sentence, quantifier and
implication morphisms. It takes the initial finite-derivation algebra for
every axiom presentation `A ⟶ S`. This is the deduction prerequisite;
closure and the adjunctions are derived from the existing least-image
theorem.

The namespace in the following table is
`CategoricalEssentialIncompleteness.V46.FirstOrderGeneration`.

| Declarations | Mathematical step |
| --- | --- |
| `axiomProof`, `axiomProof_conclusion`, `axiomImage`, `axiomImage_over` | A nullary axiom rule gives a sentence proof and a factorization through the conclusion image. |
| `theory_closed`, `theory_least`, `generated_le_iff` | The image is closed, is least among closed sentence subobjects containing the axioms, and satisfies the order-adjunction equivalence. |
| `generation`, `inclusion`, `generation_galois`, `adjunction` | The object and morphism actions on subobject orders, their Galois connection, and the categorical adjunction. |
| `presentationGeneration`, `presentationInclusion`, `presentationHomEquiv`, `presentationAdjunction` | Generation on arbitrary objects of `Over S`, its natural hom-set bijection with closed sentence subobjects, and the adjunction. |

`Subobject S` represents monomorphisms into `S` up to isomorphism. Closed
theories form a subtype of this order. The presentation category is `Over S`:
its objects are arbitrary axiom morphisms and its morphisms commute with
their maps to `S`. Morphisms to a closed subobject are unique because its
inclusion is monic. Lean writes `f ≫ g` for applying `f` and then `g`.

`generation-types.log` in the continuation working directory records the
principal types with universe parameters, full names and explicit implicit
arguments. `generation-strict.log` and `generation-checks-strict.log` record
the two zero exit statuses. The latter includes transitive axiom reports for
`generation_galois`, `adjunction`, `presentationAdjunction` and
`theory_closed`; each has exactly the permitted three-axiom union. These
are targeted checks of uncommitted proof sources, not a full v57 replay.

`V46FirstOrderPresentationAdjunction.lean` additionally constructs the
reflection into the full category of all closed monic presentations, retaining
their supplied carriers. Its namespace is
`CategoricalEssentialIncompleteness.V46.FirstOrderPresentations`.
`Closed` defines the target by monicity and factorization of every sentence
conclusion. `generatedObject`, `imageMap` and `generation` give the object
and morphism actions. `inclusion_full` and `inclusion_faithful` prove both
properties of this inclusion; `homEquiv` and `adjunction` prove the natural
hom-set bijection and adjunction for every axiom presentation and every
closed monic target presentation.

The producer and `V46FirstOrderPresentationAdjunctionChecks.lean` pass both
Lake builds and strict raw Lean checks. The three printed transitive axiom
reports, for `generation`, `homEquiv` and `adjunction`, each contain only the
permitted three axioms. `presentation-types.log` records the definition of
`Closed` and principal types with full names, universes and explicit arguments.
The production entry point and both statement audits import this pair, and
the current axiom audit includes its private declarations.

## Generation in the total restriction splitting

`V46SyntacticGenerationAdjunction.lean` and its statement checks compile
and pass both strict checks. The namespace is
`CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction`.
The parameters are an arbitrary arithmetic theory `T` extending PA,
an arbitrary variable object `V`, coefficient families `σ`, `π` in
`TotalSplit T`, and a finite arity bound `d`. No consistency, soundness,
computable-enumeration or standardness hypothesis is added.

`adjunction` and `subobjectAdjunction` specialize the proved reflection
constructions using `SyntacticGeneratedTheoryTotal.proofAlgebra` and its
proved `proofInitial`. The caller supplies no initiality premise.
`closed_iff` identifies the target's closure condition with the existing
`IsSentenceTheory`; `generation_image` and `generated_sentence_subobject`
identify the object actions with the existing sentence-conclusion image.
The inclusion is full and faithful. Its natural hom-set bijection ranges
over arbitrary axiom presentations and all closed monic presentations.

The producer and checks are integrated into the production and audit
imports. The three transitive axiom reports contain only `propext`,
`Quot.sound`, `Classical.choice`. `syntactic-adjunction-types.log` records
the principal types with all universe and implicit arguments explicit.
This proves the displayed Lean adjunctions; this earlier implementation has the stronger all-presentations initiality
premise described below. The new reflector uses only axiom subobjects.

## Derivation translation implementation

`V46InferenceTranslation.lean` and its statement checks compile and pass
`-DwarningAsError=true`; both strict exit statuses are zero. They are in the
production import, both statement-audit imports and the current axiom audit.
This is a construction for comparing deduction systems. It does not claim
the complete v57 translation Galois connection or regular-functor comparison.

The namespace is
`CategoricalEssentialIncompleteness.V46.RulePresentation.Translation`.
The underlying `Translation` structure supplies a formula morphism and
morphisms on each finite rule-label object, with equations preserving the
ordered premises and conclusion. It has no proof-translation, closure or
adjunction field. The arity index includes zero. All coefficient objects
and rule families are arbitrary.

| Declarations | Mathematical step |
| --- | --- |
| `mapRule`, `mapRule_fst`, `mapRule_snd`, `mapRule_conclusion` | Map the rule-input pullback, preserving its coefficient and ordered-child coordinates. |
| `reindexAlgebra`, `step_conclusion`, `closed_pullback` | Pull any target algebra back along the formula morphism, using the specified rule equations, and derive preservation of inference closure under inverse image. |
| `fold`, `fold_conclusion`, `fold_constructor`, `fold_unique` | Translate initial finite derivations, preserve conclusions and constructors, and prove uniqueness among morphisms satisfying those two equations. |
| `id`, `comp`, `fold_id`, `fold_comp` | Identity and composition of translations and their induced derivation morphisms. |
| `sentenceMap`, `sentenceMap_conclusion`, `sentenceImage_le` | Restrict the derivation comparison to commuting sentence objects and obtain the generated sentence-image inclusion. |

The construction keeps each child's conclusion in the ordered premise
tuple; it does not replace these conclusions by the parent's conclusion.
`inference-translation-types.log` records the structure and principal types,
with universe parameters and implicit arguments explicit. The eight axiom
reports from `inference-closure-checks-strict.log` contain only
`propext`, `Quot.sound` and `Classical.choice`. The closure pullback extension and its checks also pass strict Lean, recorded
in `inference-closure-strict.log` and `inference-closure-checks-strict.log`.
These supporting modules alone do not establish a complete v57 numbered
result; the later statement comparisons are recorded below.

## Functor of finite derivations

`V46InferenceFunctor.lean` and `V46InferenceFunctorChecks.lean` compile and
pass both strict checks. They are integrated into the production imports,
statement audits and current axiom audit. `RuleSystem D N` retains each
formula object and its finite rule presentation. Its morphisms are the
translations defined above, with identity and composition on the formula
and rule-label morphisms; the category laws are proved.

In namespace `CategoricalEssentialIncompleteness.V46.RuleSystem`,
`derivationFunctor` maps a rule system to the conclusion morphism of its
chosen initial derivation algebra, and maps translations to the constructed
fold and formula morphism. Its identity and composition laws follow from
`Translation.fold_id` and `Translation.fold_comp`. `carrierFunctor` retains
the proof carrier, `formulaFunctor` retains the formula object, and
`conclusion` is a natural transformation between them. Its naturality is
the proved fold conclusion equation. No field assumes functoriality or
naturality. The chosen initial algebras remain the deduction prerequisite.
`inference-functor-types.log` records the structure and principal types with
all implicit and universe arguments explicit, including `closed_pullback`.

The three axiom reports for `derivationFunctor`, `carrierFunctor` and
`conclusion` contain only the permitted three axioms. This construction is
support for the translation and deduction comparisons; it does not assert
the complete printed v57 Galois connection or regular-comparison theorem.

## Resource and module-port repairs

The focused module-port repair build exits zero for
`PCats.DomPullbacks`, `Arith.Feferman.Specialization`,
`FailureOfComposition.NativeSyntaxShift`,
`V46MillerOracleProgramTable`, `V46ArithmeticIndexedFibersTransport` and
`V46ForkDerivationInference`. Helper visibility is adjusted where exported
definitions need it. The compiler indices `universalCode` and `ofTableCode`
retain private implementation helpers and expose their proved graph laws.

One earlier development build was interrupted during
`FailureOfComposition.ConcreteNormalForm`: the Lean process had reached
about 6 GB while WSL had less than 0.5 GB available and no swap. Its log
records compiler exit 130 and build exit 1. Bounded diagnostics then located
kernel conversion in the output-graph evaluation lemma. Factoring variable
exchange through a lemma for arbitrary formulas preserves the graph
definition and theorem statement. The repaired module compiles and emits
its object and C files with a 4 GB Lean limit; the diagnostic exits zero.
The profile records 87 ms of kernel type checking for that run. These
diagnostics and failed attempts are preserved under the continuation
working directory.

The first local full-verifier attempt is preserved at
`.codex-work/verify-20261111T010720Z-8ZXMED`, with exit status 1. It passed
the source and dependency checks and parser regressions, then failed in the
main build on remaining module visibility errors in
`V46MillerUniformComputations` and
`FailureOfComposition.NumericalSpecialization`. The two repaired modules
subsequently passed a focused build, with their algorithms retained and
implementation helpers private. This attempt did not reach the combined
statement or axiom audits, and is not a passing full verification.

The second full attempt,
`.codex-work/verify-20261111T013434Z-8VQmoZ`, also exits 1 during the main
build. Its remaining failures were visibility of the join implementation
in `V46MillerCategoryJoins` and the token reader in
`FailureOfComposition.NumericalProofBridge.Core.Presentation`. Both repaired
modules then passed the focused build recorded in `port-repairs-3-build.log`.
The main build also compiled the repaired `ConcreteNormalForm` module in
3.7 seconds. This second attempt did not reach the combined statement and
axiom audits either.

The third full attempt,
`.codex-work/verify-20261111T014655Z-Y5YCdm`, exits 1 in the main build.
Nine modules reported inaccessible private helpers: `SyntacticModel`,
`V46MillerSyntaxRawSums`, `V46MillerSyntaxRawLeaves`, `V46MillerCutDigits`,
`V46MillerCutInseparabilitySplit`, `NativeEqualityTransport`,
`NumericalProductProofs.Core`, `PrfEqTransportRepair.Core`, and
`NumericalRangeProofs.Core`. Helpers occurring in exported mathematical
constructions or syntax tests are made public. The finite-table compiler
index `decisionIndex` retains private implementation helpers with
`@[no_expose]`; its evaluation theorem remains public. None of these edits
changes a theorem statement or algorithm. The focused build of all nine
repaired modules exits zero in `port-repairs-4-build.log`. This third attempt
did not reach the statement or axiom audits.

The fourth full attempt,
`.codex-work/verify-20261111T020824Z-zAwgiA`, exits 1 during the main build.
It reached the arithmetic diagonal bounds and retained numerical proof
modules. Ten modules failed before the statement and axiom audits. Repairs
were applied after those failures, so this run does not verify the repaired
source. Its original logs and input record are preserved.

Two private Miller list-transport helpers shared the name `slice_map_left`
in one namespace. Their public names are `membershipOverMap_left` and
`deletionOverMap_left`, identifying the respective constructions. Their
local references are updated; no external public name is removed. The
fork conclusion-computability proof adds reflexivity after its final
simplification; its statement is unchanged. Remaining repairs expose
helpers needed by exported data or retain private compiler implementations
behind their proved graph equations. The 21-module focused repair build now exits zero in
`port-repairs-8-build.log`. At that stage, production integration and the full verifier remained
pending. The later passing run is recorded below.

A subsequent development build of the production entry point exposed
further private compatibility helpers in the Miller, numerical and fork
comparisons. Their types and uses in exported constructions were inspected
before export. The complete names of the reviewed export changes are
retained in the continuation working records. No theorem statement is
weakened, and no audit fixture is changed to bypass a dependency check.

`NativeInternalCorrectness` also failed at its definability tactic because
the checker module's definability instances remained private after the
module-system port. Exporting the existing proved instances restores the
proof: `native-definability-repair-build.log` exits zero and records the
correctness module compiling in 5.4 seconds. The induction predicate,
theorem hypotheses and automation limits are unchanged. This failure was
not an operating-system memory failure.

The next production development build reached
`FailureOfComposition.NativeFamilyInstances`, where kernel conversion in
`third_specialization` grew to 7,612,544 KiB resident memory over 32 minutes.
WSL had 442,648 KiB available. The compiler was interrupted, preserving the
log; the build exits 1. No operating-system OOM kill is claimed.

The bounded diagnostic `native-family-profile-1.log` identifies excessive
kernel memory use at that declaration. Factoring the already proved
`toNumVec_instance` equality through a lemma for an arbitrary formula keeps
the large instantiated quotation out of conversion. The public theorem
statement and syntax definitions are unchanged. The second diagnostic,
`native-family-profile-2.log`, exits zero with a 4 GB Lean budget and
records 220 ms of kernel type checking for the module.

`resource-repair-build.log` then records a successful Lake build of that
module, `V46MillerTheoryDomainApplication`, and
`V46NumericalDerivationInterpretationWordsFinal`. The latter repairs export
the sentence-carrier alias and make the existing scalar-identity type
explicit. All three compiler commands carry `--memory=4096`.

The package now supplies that budget through Lake's `weakLeanArgs`, which
preserves the compiled cache. The existing verifier supplies it to each
direct Lean invocation and records the actual arguments. Toolchain,
dependency revisions and permitted axioms are unchanged. Serialization and
`LEAN_NUM_THREADS=1` remain in force. No full verification pass is claimed
from these focused checks.

The analogous pointwise and closure checks in
`NativeMembershipInstances` then reached the 4 GB kernel budget. Applying
the same existing substitution equality before formula instantiation keeps
both statements unchanged. `native-membership-profile-1.log` exits zero
and records 256 ms of kernel type checking. The bounded production build
`production-development-8.log` exits zero (4,015 jobs), including the
production entry point. This is a build result; combined statement checks
and complete transitive axiom verification remain pending the full verifier.

## Source anchors for the continuation proofs

The following locations identify the principal declarations in the measured
source. Each production module has a matching `Checks` module imported by
`CurrentStatementAudit`, and each is imported with private declarations by
`CurrentAxiomAudit`. The explicit type records named above retain universe
parameters and implicit arguments for the later Lean appendix. They describe
the implemented constructions; the v57 statement comparison remains open.

| Namespace below `CategoricalEssentialIncompleteness.V46` | Principal declaration | Source location | Statement check |
| --- | --- | --- | --- |
| `FirstOrderGeneration` | `adjunction`, `presentationAdjunction` | [subobject adjunction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46FirstOrderGeneration.lean#L181), [presentation adjunction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46FirstOrderGeneration.lean#L227) | `V46FirstOrderGenerationChecks.lean` |
| `FirstOrderPresentations` | `adjunction` | [adjunction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46FirstOrderPresentationAdjunction.lean#L121) | `V46FirstOrderPresentationAdjunctionChecks.lean` |
| `SyntacticGenerationAdjunction` | `adjunction`, `subobjectAdjunction` | [presentation adjunction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46SyntacticGenerationAdjunction.lean#L52), [subobject adjunction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46SyntacticGenerationAdjunction.lean#L72) | `V46SyntacticGenerationAdjunctionChecks.lean` |
| `RulePresentation.Translation` | `closed_pullback`, `fold_constructor`, `fold_unique` | [closure](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46InferenceTranslation.lean#L149), [constructors](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46InferenceTranslation.lean#L178), [uniqueness](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46InferenceTranslation.lean#L221) | `V46InferenceTranslationChecks.lean` |
| `RuleSystem` | `derivationFunctor`, `conclusion` | [functor](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46InferenceFunctor.lean#L79), [naturality](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46InferenceFunctor.lean#L97) | `V46InferenceFunctorChecks.lean` |

## Integrated local verification of v51, 11 November 2026

`bash scripts/verify-wsl.sh` passed with exit **0** in
`.codex-work/verify-20261111T044232Z-gtWRUV`. All **1,602 commands** passed,
including the six parser regressions, the production build, combined
statement build, individual strict producer and statement checks, strict
combined statement check, and both transitive axiom audits. The five new
producer/Checks pairs in the source-anchor table each passed both strict
commands with exit 0. Their declarations are included in the automatic
current audit.

| Verification datum | Result |
| --- | --- |
| Manifest selected by the run | v51 |
| Current production modules | 815 |
| Current declarations audited under complete names | 26,141 |
| Retained declarations audited | 1,274 |
| Transitive axiom union | `Classical.choice`, `Quot.sound`, `propext` |
| Measured inputs | 2,238 |
| Dependency worktrees | All 16 clean and pinned at start and end |
| Imported source pins | 356 checked, no mismatches |
| Changed measured inputs during the run | None |
| Sum of recorded command durations | 11,135.55 seconds |

Measured-input snapshot SHA-256:
`869d1d45f02c0b521762231c54a0c4ffe342d4383ee00ada7d38800a6143d0be`.
Preserved raw `build-logs/verification.json` SHA-256:
`92b432ae3bd73313f7c7651dd063761e6bae5d63f6c4c8cb52ca0b7403f490bc`.
The wrapper began at `27695edc63647b4f624798aeeb4f72c284e4b4b1` with the
proof and module-port changes in its working tree. Its start status, diff,
command logs, complete axiom maps and exit status are preserved in the run
directory. A commit containing the measured bytes is identified in the
delivery record below; it is not presented as the wrapper's starting HEAD.

This is a new full verification of the available v51 integration. It does
not verify the subsequently supplied v57 manuscript or close its fifteen numbered
correspondence rows. The generation adjunctions are proved; matching 4.4
to its printed statement remains pending. The complete 4.5 and 4.6
statements remain open despite the proved translation and functor
constructions. The other twelve requested results remain open. Thus no
new v57 numbered row is marked complete in this batch. The 62 retained
rows keep their existing scope.

No manuscript source or artifact was edited. Existing Lean statements were
not weakened. The resource repairs factor proofs of the same equations,
and the module-port repairs change visibility and references. Lean's 4 GB
budget was used throughout this full run; no command timed out or exhausted
that budget.

## Commit and delivery

The proof batch is committed and pushed to main as
`962f9474dcd543529692cbdf37a6db703f4abda2`. The ordinary SSH push exited 0,
and `git ls-remote origin refs/heads/main` confirmed that commit. All 2,238
measured inputs were compared with its committed blobs and matched. The
comparison is recorded in
`.codex-work/v57-continuation-20261110/committed-source-identity.json`.
The report follow-up changes no measured input. Source links in the table
above identify this proof commit.

For the later appendix, `FirstOrderGeneration.generated_le_iff` at
[line 149](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/962f9474dcd543529692cbdf37a6db703f4abda2/Lean/CategoricalEssentialIncompleteness/V46FirstOrderGeneration.lean#L149)
is a short representative proof. Its two directions use the axiom
inclusion and leastness of the generated theory. The preceding tables
identify the supporting declarations and their hypotheses. No manuscript
appendix was edited.

Delivery follows the existing procedure: read report bytes from the pushed
report commit, compare all measured proof inputs with that commit, select a
new Downloads directory to preserve differing files, and verify each copy
by SHA-256. The delivery receipt records the report commit, proof commit,
remote confirmation, destination paths and hashes. The requested manuscript
version was 57; that delivery records the completed v51 run. The v57
integration below is a separate source state.

## Artifact and registration scope

The subsequently supplied v57 artifacts match both instruction digests:

| Artifact | Verified SHA-256 |
| --- | --- |
| `logical_consequence_v57_source.zip` | `e29741844891826680520b5a352e963d0f0e6b04035e3943806df159c27d2832` |
| `logical_consequence_and_essential_incompleteness_v57.pdf` | `cec565fba1269765999a0f9f431f25beb34fa4e48882643d187d4500a9aa4dcb` |

The checkout has no CEI `Lean/Palomar` Challenge, Solution or Comparator
configuration. The contained `FailureOfComposition/Palomar/Challenge.lean`
is a separate project's draft, with nine designated placeholders:
`obstruction_four_properties`, `no_quotient_composition_productive`,
`no_quotient_composition_godel`, `pi_one_characterization`,
`generated_congruence_classification`, `weak_totality_counterexample`,
`range_counterexample_godel`, `range_counterexample_productive`, and
`generated_quotient_partial_recursive`, all in
`FailureOfComposition.Palomar`. Its Solution supplies proofs independently
of the Challenge. Those placeholders are preserved; they are not CEI
registration declarations. No general exception to production axiom or
placeholder rejection has been introduced.


## v57 integration: generation and deduction comparisons

The v57 synchronization commit is `c61105d`. Its archive comparison is
recorded in `v57-archive-comparison.json` under the continuation working
directory. The two unrelated untracked Palomar drafts were preserved.
The toolchain, dependency manifest, imported-source pins and manuscript
bytes are unchanged by this proof batch.

The complete principal declaration types, with universe parameters and
implicit arguments displayed, are retained in `v57-principal-types.log`.
All namespace names below are under
`CategoricalEssentialIncompleteness.V46`. Composition `f ≫ g` applies `f`
first. A `Subobject S` is an isomorphism class of monomorphisms into `S`;
`Over S` also permits nonmonic presentations.

### Theorem 4.4: the initiality premise

The earlier `FirstOrderGeneration` construction requires initial finite
derivation algebras for every axiom morphism `A ⟶ S`. That theorem remains
valid under its stated stronger hypothesis. It does not establish 4.4 at
the printed hypotheses. The repair is in Lean; no manuscript repair is
needed.

`V46FirstOrderReflection.lean` requires such algebras only for axiom
**subobjects**. Its `extensive`, `monotone` and `idempotent` give the closure
operator on sentence subobjects. `generated_eq_pullback` identifies it
with the sentence pullback of the formula-conclusion image. `Theory` is
defined by `generated T = T`. The functors `generation` and `inclusion`,
the natural `homEquiv` and `adjunction` give the order reflection.

For an arbitrary presentation `a : A ⟶ S`,
`presentationGeneration` is defined as `generated (imageSubobject a)`.
Its action on morphisms uses the image factorization; `presentationHomEquiv`
and `presentationAdjunction` give the second reflection. No initiality
statement is asserted for the derivations retaining the labels of `A`.
The auxiliary `presentation_generated_comparison`, under the earlier
stronger hypotheses, equates sentence images only. It does not identify
or transfer initiality between derivation carriers.

`SyntacticGenerationAdjunction.sentenceAdjunction` and `axiomAdjunction`
instantiate these constructions with the previously constructed algebras
in `TotalSplit T`. The arbitrary extending theory, coefficients and variable
object are retained. `axiomGeneration_image` is the printed image formula;
`axiomGeneration_original` compares the generated sentence subobjects with
the earlier implementation. There is no extra initiality premise on the
caller.

The producer and Checks for the new reflector and its specialization pass
four strict Lean commands. The record is `v57-reflection-targeted.json`;
each command exits 0 and the printed transitive axiom reports contain only
the permitted three axioms.

### Theorem 4.5: translations and both reflections

`V46LogicalTranslations.lean` defines first-order presentations and
logical translations over the same variable object. Translation data are
the term, formula and sentence morphisms. The laws preserve the named
variables, logical constructors, successful admissible substitution and
sentence inclusion. Rule witnesses are existence conditions, rather than
additional choices determining equality of translations. Identity,
composition and the category laws are proved.

`Translation.rulesMap` constructs the finite-rule morphism including axiom
leaves. `V46TranslationGalois.lean` uses its initial fold to prove
`map_generated_le`, derives `inverse_closed`, and constructs `pushforward`
and `inverseImage`. `adjunction` is their natural hom-set bijection.
`generation_functor_identity`, `pushforward_comp`, `inverseImage_comp` and
the identity laws are proved at the functor types.

`V46FirstOrderTranslationReflection.lean` constructs the category `Axioms`
of presentations with axiom subobjects and its full subcategory of theories.
The generation and inclusion functors satisfy `Axioms.adjunction`.
`homEquiv_translation` proves that the bijection leaves the translation
unchanged. These three producer/Checks pairs pass six strict commands,
recorded in `v57-translation-targeted.json`, with exit 0 and only the
permitted axioms.

### Proposition 4.6: change of category and the algebra mate

`V46DeductionComparison.lean` defines the image functor `imageFunctor`
and the presentation functor `presentationFunctor`, with their object and
morphism actions. `image_presentation` derives image preservation from
preservation of regular epimorphisms. This uses a consequence of the
printed regularity hypothesis, rather than an additional assumption.

From the stated conclusion-preserving sentence-derivation morphisms,
`generation_square` and `presentation_square` prove the two functor
identities. `inclusionComparison` supplies the natural transformation
between the inclusion functors. For a subobject right adjoint,
`right_closed` proves closure preservation and `restrictedAdjunction`
constructs the restricted adjunction.

`V46DeductionSliceAdjunction.lean` constructs the right adjoint for an
ambient adjunction `G ⊣ H`. Its object over `S₁` is the pullback of `H b`
along `η ≫ Hσ`; it acts on morphisms by the pullback universal property.
`rightIso` is a natural isomorphism with the composed slice right adjoints,
including both coordinate equations. `adjunction` proves the presentation
adjunction, and `orderAdjunction` proves the corresponding image/pullback
adjunction on subobjects.

`V46DeductionMates.lean` transposes the inference algebra using the rule
natural transformation and counit. `fold_constructor` proves the resulting
constructor equation. `comparisonMap` specializes the initial fold and
restricts to sentence conclusions; `comparisonMap_conclusion` proves its
triangle. `generation_square_from_rules`, `presentation_square_from_rules`
and `theoryAdjunction` apply the comparison with these constructed maps.
The right adjoint and proof comparison are not left as unexplained fields.
Initiality is used only for source axiom subobjects.

All three producer/Checks pairs pass six strict Lean commands, recorded in
`v57-deduction-targeted.json`. Their seventeen named transitive axiom
reports contain only `propext`, `Quot.sound` and `Classical.choice`.
The production import, both statement imports and the automatic current
axiom audit include all seven new producers and Checks.

### Integrated v57 verification state

`bash scripts/verify-wsl.sh` passed with exit **0** at proof commit
`c93832d761347607906b11615bd56cb937cdfdff`. The run is
`.codex-work/verify-20261111T180312Z-YL3Qyj`. All **1,616 commands** passed,
including all sixteen strict commands for the seven new producer/Checks
pairs and the updated concrete generation-adjunction pair, the combined
statement checks and both transitive axiom audits.

| Verification datum | Result |
| --- | --- |
| Active manuscript | v57, unchanged from synchronization commit `c61105d` |
| Numbered results proved / open | 65 / 12 |
| Production modules audited | 822 |
| Current / retained declarations audited | 26,546 / 1,274 |
| Transitive axiom union | `Classical.choice`, `Quot.sound`, `propext` |
| Measured inputs | 2,254, all matching committed proof bytes |
| Dependencies | All sixteen worktrees clean and pinned at start and end |
| Imported-source pins | 356 checked, no mismatches |
| Measured inputs changed during run | None |
| Sum of command durations | 11,772.23 seconds |

Snapshot SHA-256:
`03bf086a498e9f6d7b077cf2c76e8d80d0bbb15c86f133a8b692a76a1c2a8128`.
Preserved raw verification JSON SHA-256:
`04851791204d6f8b7774af1c700828c31cae997b6691f265b10a03835fd53e7f`.
`v57-committed-source-identity.json` records the comparison of all measured
inputs with the proof commit. The wrapper started at that commit with no
tracked edits; the two unrelated Palomar drafts remain untracked and
unchanged. Lean used its 4 GB budget throughout this run. No command timed
out or exhausted that budget.

The following principal anchors identify the tested revision. The namespace
prefix is `CategoricalEssentialIncompleteness.V46.`.

| Manuscript result | Principal declarations | Tested source |
| --- | --- | --- |
| 4.4 | `FirstOrderReflection.adjunction`, `presentationAdjunction`, `presentationGeneration_obj` | [reflector](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46FirstOrderReflection.lean#L126), [presentations](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46FirstOrderReflection.lean#L155) |
| 4.5 | `FirstOrderPresentation.Translation.adjunction`, `generation_functor_identity`, `pushforward_comp`, `inverseImage_comp` | [Galois connection](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46TranslationGalois.lean#L95) |
| 4.5, following reflection | `FirstOrderPresentation.Axioms.adjunction`, `homEquiv_translation` | [reflection](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46FirstOrderTranslationReflection.lean#L117) |
| 4.6 | `DeductionComparison.generation_square`, `presentation_square`, `inclusionComparison`, `restrictedAdjunction` | [comparison](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46DeductionComparison.lean#L130) |
| 4.6, right adjoint | `DeductionSliceAdjunction.adjunction`, `orderAdjunction` | [pullback construction](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46DeductionSliceAdjunction.lean#L129) |
| 4.6, mate | `DeductionMates.comparisonMap`, `comparisonMap_conclusion`, `generation_square_from_rules`, `theoryAdjunction` | [constructed maps](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c93832d761347607906b11615bd56cb937cdfdff/Lean/CategoricalEssentialIncompleteness/V46DeductionMates.lean#L137) |

The post-verification update changes the correspondence's verification
wording and counts, this report and the README status paragraph. It changes
no Lean input, manuscript source, artifact, manifest, toolchain or dependency.
The correspondence is the only measured input with a documentation-only
change after the proof run; `v57-status-documentation-delta.json` preserves
its before/after bytes and SHA-256 digests. The subsequent manuscript-only
gate checks those documentation and target changes; it is not presented as
a second Lean run. All other measured inputs must match the tested commit
before delivery.

The first remaining mathematical construction is Theorem 4.7, followed by
4.8, 5.1–5.3 and the seven application results. Three of the fifteen added
results are proved and verified; twelve remain open. Uncompiled drafts for
the next syntax interpretation are kept separately in the ignored
continuation directory and establish no additional correspondence row.
No manuscript mathematical statement or proof was changed.


## Ongoing Theorem 4.7: syntax comparisons

The next development batch adds `V46VariableTests`,
`V46StableListComparison`, `V46NullarySyntaxAlgebra`,
`V46NullarySyntaxInterpretation` and `V46NullarySyntaxOccurrences`, with
Checks, production imports and automatic axiom coverage. These additions
follow the completed proof commit and are not part of its full-run snapshot.
All ten targeted strict commands pass; their fourteen selected transitive
axiom reports contain only the permitted three axioms. The record is
`v57-free-prerequisites-targeted.json` in the continuation working directory.

The equality test is determined by the diagonal. List initiality constructs
the comparison isomorphism and proves preservation of singleton, append,
deletion and membership. The six logical constructor equations give an
algebra morphism for the manuscript polynomial with empty function
coefficients and nullary predicate coefficient X. The fold interprets any
morphism X→S_Q, commutes with constructors and is unique with those laws.
Initiality also proves the occurrence-list comparison across the chosen
list carriers. Pullback gives `sentenceInterpretation`; its value on the
atomic sentence map is the supplied morphism.

This is supporting work for 4.7. The later substitution batch below proves
admissible-substitution compatibility. Logical-rule preservation, the two
categories and functors, and their natural hom-set bijection remain open.
The count remains 65 proved numbered results and twelve open. No manuscript
source or mathematical statement changes.


### Substitution comparison for Theorem 4.7

`V46.NullaryInterpretation.variableIso` in `V46NullarySyntaxTerms` identifies the term object with V through
its variable constructor. This follows from the initial-algebra structure
and the initial empty-function input. `V46CategoricalVariableSubstitution`
proves the variable constructor equation for the existing substitution fold.
`V46.NullaryInterpretation.term_substitution` in `V46NullaryTermSubstitution` then proves the term equation
required of the interpretation into any target first-order syntax.

`V46OptionSyntaxNaturality` proves naturality of the option-valued binary and
coefficient constructors by their coproduct-fiber decompositions. Occurrence
and membership comparisons prove preservation of both variable equality and
the capture test. `V46.NullaryInterpretation.quantifier_pair_comparison` in
`V46NullarySubstitutionQuantifier`
includes the equal-name branch, which returns the original body even when
the recursive result fails.

`V46.NullaryInterpretation.substitutionComparisonHom` in
`V46NullarySubstitutionHom` interprets the output
of the source substitution algebra. `V46NullaryInterpretedSubstitutionHom`
constructs `interpretedSubstitutionHom`, which substitutes after interpretation.
Both are algebra morphisms into the same algebra over the source substitution
parameter. Initiality in that slice gives
`V46.NullaryInterpretation.substitution_fold_comparison`.
Its result projection proves `formula_substitution_option` in
[V46NullaryFormulaSubstitution.lean](../Lean/CategoricalEssentialIncompleteness/V46NullaryFormulaSubstitution.lean).
The pullback lift `admissibleInterpretation` preserves both its input inclusion
and result, by `admissibleInterpretation_inclusion` and
`admissibleInterpretation_result`.

The target algebra operations and carriers are the supplied arbitrary
morphisms and objects. The source coefficient morphism X→S_Q may identify
predicate labels. No initiality is transferred to an axiom presentation or
to an image of its labels, and no soundness or arithmetic hypothesis is added.

The 21 supporting producer/Checks pairs are imported by the production entry
point, both statement audits and the automatic transitive axiom audit. All
42 targeted strict commands pass with `--memory=4096 -DwarningAsError=true`
and `LEAN_NUM_THREADS=1`, serialized through the existing lock. Their 64
selected axiom reports are parsed under complete declaration names and use
only `propext`, `Quot.sound` and `Classical.choice`. The command, exit status,
source hash and log for each check are retained in
`.codex-work/v57-continuation-20261110/v57-substitution-targeted-1.json`.
These are targeted checks of the new batch, not a replacement for the full
run of proof commit `c93832d761347607906b11615bd56cb937cdfdff` recorded above.
The next integrated full run remains pending.

The later logical-scheme batch below proves logical-rule preservation.
Theorem 4.7 remains open at its categorical adjunction. The proved/open count is unchanged: 65/12 among the 77 numbered
results of manuscript v57. The manuscript, its artifacts and all dependency
pins are unchanged.


### Logical translations for Theorem 4.7

`V46NullaryLogicalInstantiation`, `V46NullaryLogicalDistribution` and
`V46NullaryLogicalEquality` construct maps on the seven scheme-parameter
objects, including the pullbacks defining admissibility for instantiation
and the two substitutions of the equality scheme. The free-variable test
comparison gives the map on the quantifier-distribution fiber.
`V46NullaryLogicalInterpretation.logicalParameterMap` is the coproduct of
these maps; the namespace of its declarations is
`CategoricalEssentialIncompleteness.V46.NullaryInterpretation`.

Within that namespace, `logical_axioms_comparison` proves its axiom equation.
`translation` supplies every field of `FirstOrderPresentation.Translation`.
Its source `presentation` requires derivation initiality only for sentence
subobjects. `translation_unique` proves uniqueness for any logical translation
with the prescribed atomic sentence map; `translation_comp` identifies
composition with a target translation. The term/formula uniqueness comes
from syntax initiality, and equality of the sentence morphisms follows by
cancelling the target sentence inclusion.

The four producer/Checks pairs pass eight further strict commands and 22
selected transitive axiom reports. The retained record is
`.codex-work/v57-continuation-20261110/v57-logical-targeted-1.json`.
Together with the substitution batch, this gives 50 passing strict commands
and 86 selected axiom reports. All source hashes still match those records;
the permitted axiom union is unchanged. These 25 pairs are imported by the
production entry point, both statement audits and the automatic axiom audit.
Their next integrated full replay remains pending.

The first remaining step in 4.7 is to show that theorem/refutation-pair
extraction takes values in the stated consistent-pair category. Both
functors, their laws and the natural hom-set bijection remain to be assembled.
The numbered-result count remains 65 proved and twelve open. This batch is
local work following main `f4af420d06187a29d681cf54b055b711fb8cd8f8`; the
full verification recorded earlier covers its own proof commit, not this
later working tree.

The exact types, including universe parameters and explicit hypotheses, of
the principal interpretation, substitution and translation declarations are
retained in `v57-free-interpretation-types-3.log` in the continuation working
directory. The Checks modules give the associated statement types and
selected transitive axiom commands. No mathematical statement, manuscript
source, artifact or dependency pin changed.


### Theorem 4.7: the adjunction

The declarations in this final group complete the printed universal property.
The source is the category of disjoint signed subobject pairs whose generated
free theory is consistent. The target consists of presentations with a closed,
consistent sentence theory. `V46.FirstOrderPresentation.ConsistentTheoryCategory.morphism_bound_iff`
identifies its direct-image morphism condition with the printed
σ_!T≤U condition. Thus the use of the existing theory category preserves the
manuscript's morphisms.

`V46.SignedFirstOrder.axioms` is the union of the images of the positive
atomic and negative atomic inclusions. `theory` applies generation.
`interpretation_theory_bound` identifies the bound on its interpreted image
with the positive and negative pair inequalities.
`evaluation_consistent` proves the object condition for extraction: sentence
evaluation maps the generated signed theory into the supplied consistent
closed theory, whose inverse image is consistent. Downward preservation of
consistency gives the required source consistency.

`V46SignedFirstOrderCategories` constructs `generation` and `extraction` on
objects and morphisms, with their identity and composition laws.
`V46.SignedFirstOrder.homEquiv` restricts a theory morphism to its atomic
sentences and extends a pair morphism by the constructed interpretation.
The inverse laws follow from interpretation uniqueness and the atomic
constructor equation. Both naturality equations are proved.
`V46.SignedFirstOrder.adjunction` packages this bijection;
`unit_arrow` identifies the unit with θ_X and `counit_translation` identifies
the counit with sentence evaluation.

`NullaryPresentations` packages precisely the supplied syntax and derivation
hypotheses for every nullary coefficient object X. Its derivation hypothesis
quantifies over axiom subobjects, rather than all axiom-label morphisms. The
interpretation, substitution comparison, rule maps, evaluation consistency
and adjunction are constructed from those prerequisites. No field assumes
any of these conclusions. The construction does not transfer initiality from
an axiom image to a presentation with repeated labels.

The final five producer/Checks pairs pass ten strict commands with sixteen
selected axiom reports in
`.codex-work/v57-continuation-20261110/v57-signed-adjunction-targeted-1.json`.
The complete 30-pair batch therefore has 60 passing strict commands and 102
selected transitive axiom reports. Every retained report is accounted for
under its complete declaration name; all use only the permitted axioms.
The production entry point, both statement audits and automatic axiom audit
import all 30 pairs. The subsequent integrated full replay passed at proof commit
`c87ae0e3a7f1faed605c6bc1753f6309504527b7`, as recorded below. The earlier
1,616-command run remains evidence for its own commit.

There are now 66 proved counterparts among v57's 77 numbered results, with
eleven open: 4.8, 5.1–5.3, 8.9–8.10, 9.6, 9.8 and 10.7–10.9.
Corollary 4.8 is the next mathematical obligation. No manuscript statement,
source artifact, toolchain or dependency pin changed.


## Full verification of the free first-order adjunction

The tested proof commit is `c87ae0e3a7f1faed605c6bc1753f6309504527b7`.
The current manuscript remained v57. The combined entry point and current
statement audit passed before the strict replays. The established command
`bash scripts/verify-wsl.sh` completed with exit 0 in
`.codex-work/verify-20261111T234522Z-22sulL`.

| Verified item | Result |
| --- | --- |
| Commands | 1,676; all exit 0 |
| Measured inputs | 2,314; all match committed proof bytes |
| Current production modules | 852; automatic audit coverage matches the source inventory |
| Current / retained declarations | 27,204 / 1,274; all raw reports accounted for under complete names |
| Transitive axiom union | `propext`, `Quot.sound`, `Classical.choice` |
| Dependency worktrees | All sixteen clean and pinned, at the start and end |
| Imported-source comparisons | 356 passed |
| Numbered results proved / open | 66 / 11 |

The measured-input snapshot is
`70f2b4c994c8408f3a7ae53f3940fa2bcfb833660f2c96282e93e0560ed5a214`.
The SHA-256 of the preserved raw `verification.json` is
`c1877888d61bb1a39fbe29239216a086f687e306aa89e5c9a0645af0abbee4b4`.
The full run began at 2026-11-11T23:45:22Z; its completion record was written
at 2026-11-12T02:18:58Z. Its commands took 9,205.52 seconds in aggregate.
All 2,314 measured inputs were compared against both the working tree and
Git blobs at the proof commit. The retained identity record is
`v57-4.7-committed-source-identity.json` in the continuation working directory.

The earlier run `.codex-work/verify-20261111T233434Z-fC4ub3` was interrupted
by the tool-server restart after 84 successful commands. It has no recorded
exit status. Its verbatim log snapshot and `interruption-record.json` remain
separate from the completed run. The later persistence helper found that the
verifier had finished and exited before changing any process; no third
verification run was launched.

The principal result is
`CategoricalEssentialIncompleteness.V46.SignedFirstOrder.adjunction`.
Its explicit source and target are `generation F` and `extraction F`.
`F : NullaryPresentations V` supplies the printed syntax and derivation
prerequisites for all coefficient objects X; the family contains no
interpretation, rule-preservation, consistency-extraction or adjunction
assumption. Those constructions are proved. The exact universe parameters,
field types and principal theorem types are retained in
`v57-free-first-order-principal-types.log`.

The supporting results are `homEquiv` and its naturality proofs,
`unit_arrow`, `counit_translation`, `evaluation_consistent` and
`interpretation_theory_bound` in the same `V46.SignedFirstOrder` namespace.
`V46.FirstOrderPresentation.ConsistentTheoryCategory.morphism_bound_iff`
proves that the target category's morphisms have the printed closure bound.
The corresponding Checks modules retain explicit intended-statement types;
the full strict replay and automatic axiom audit include their production
proofs and dependencies.

The later report commit changes only the active status descriptions, README
and this continuation report. Only the correspondence file is a measured
input among those three files; its before/after bytes and SHA-256 are retained
in `v57-4.7-status-documentation-delta.json`. All other measured inputs remain
identical to the tested proof commit. No mathematical statement, manuscript
artifact, toolchain, dependency pin or imported-source pin changed.

Corollary 4.8 is now the first open result. Its remaining construction is the
internal Boolean valuation for a separator, its substitution and truth laws,
and the consistent complete extension. The other open rows remain 5.1–5.3,
8.9–8.10, 9.6, 9.8 and 10.7–10.9.


## Corollary 4.8: Boolean extension and inseparability

The principal declaration is
`V46.SignedFirstOrder.essential_incomplete_iff_inseparable` in
[V46SignedFirstOrderIncompleteness.lean](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderIncompleteness.lean).
It retains the disjointness and consistency hypotheses, arbitrary coefficient
object X, and the syntax/derivation family from Theorem 4.7. The ambient
category is an arbitrary split restriction category C whose total category
is regular and finitary extensive. `RestrictionSubobjects.MonoInverses C`
is precisely the printed partial-inverse hypothesis on all monomorphisms of
Tot(C); it assumes no incompleteness or comparison conclusion.
`FirstOrderPresentation.EssentiallyIncomplete` includes the base consistency
condition and quantifies over every closed consistent internal extension.

`NullaryBooleanValuation.algebra` interprets terms in the terminal object,
equality by true, nullary predicates by the given separator d:X→2, and
negation and implication by their Boolean truth functions. Quantification
is projection. `valuation` is the constructed syntax fold, with all five
formula-constructor equations proved. Arbitrary generalized morphisms are
used throughout; no pointwise semantics, standardness or choice of witnesses
for carrier membership is assumed.

`OptionSyntax.mask` retains an option's failure status and replaces its
payload. Its composition, branching, unary, coefficient and binary laws
support the substitution invariant. The `PairGood` equation compares the
computed Boolean option with the mask of the original Boolean value.
Constructor closure holds on arbitrary parameter families, including the
equal-binder branch that returns the original formula even when recursive
substitution fails. Initiality factors the substitution fold through the
constructed equalizer subalgebra. `substitution_option_value` is its option
equation, and `substitution_value` restricts that equation to the existing
admissibility pullback.

`logical_axioms_value` proves validity of all seven scheme morphisms.
`modus_ponens`, `rule_value` and `truthAlgebra` construct the inference algebra
on the true-formula fiber, with ordered premises and their own truth values.
`sentence_closed` applies the existing least-image theorem to this algebra.
`sentence_consistent` and `sentence_complete` identify the true and false
fibers as complementary. `SignedFirstOrder.booleanTheory_extends` proves
that the sentence theory contains both signed axiom images, hence their
generation. Thus a separator supplies the required complete consistent
extension.

`RestrictionSubobjects.orderIso` constructs the identification of subobjects
of Tot(C) with restriction idempotents of C. It proves the order equivalence
using partial inverses of the subobject inclusions, and surjectivity using
splittings. `complementary_iff` and `inseparable_iff` preserve the specified
notions of complementary pairs and inseparability. They connect the
subobject proof with the manuscript's restriction-category conclusion;
the comparison is not an assumption.

All sixteen producer/Checks pairs are imported by the production entry point,
both statement audits and the automatic transitive axiom audit. The targeted
run `v57-4.8-targeted-2.json` passed 32 strict commands, including 70 selected
axiom reports with only `propext`, `Quot.sound` and `Classical.choice`.
The earlier targeted run records development failures in imported namespaces
and unused simp arguments; those logs are preserved. Exact principal types,
universes, hypotheses and the final axiom report are retained in
`v57-signed-incompleteness-principal-types.log` in the continuation working
directory. Lean uses f ≫ g for the manuscript's gf.

This batch changes no manuscript statement, artifact, toolchain, dependency
or imported-source pin. There are now 67 proved numbered counterparts and
ten open mathematical obligations: 5.1–5.3, 8.9–8.10, 9.6, 9.8 and 10.7–10.9.
The integrated full replay for Corollary 4.8 passed at `45a8a6d017850a3a68fcecd01ad82f5a1a83674a`.
The completed replay below establishes 67 numbered counterparts; the preceding
66-result run remains preserved for its own source snapshot.


## Full integrated v57 verification of Corollary 4.8

Proof commit `45a8a6d017850a3a68fcecd01ad82f5a1a83674a` passed
`bash scripts/verify-wsl.sh` in
`.codex-work/verify-20261112T155244Z-TqJmof`, exit **0**.
All **1,708 commands** passed on **2,346 measured inputs**: the combined
production build, current intended-statement checks, every strict source and
Checks replay, and both final transitive axiom audits. The audits cover
**868 current production modules**, **27,399 current declarations** and
**1,274 retained declarations**. Both axiom unions are exactly
`propext`, `Quot.sound`, `Classical.choice`.

All sixteen dependency worktrees were clean and pinned at the start and end.
All 356 imported-source comparisons passed. Every measured input matches both
the tested worktree and the committed proof bytes.
Snapshot SHA-256:
`9ef1a2c9287cb228366e13f9756cf01d7717889fa7af256155f393c71ab2cedf`.
Raw verification JSON SHA-256:
`b50d91a19023f4c8d84631f0a562684d10466d2310896a70b686556c9d60ac49`.
The [verification record](V57_SIGNED_FIRST_ORDER_VERIFICATION_2026-11-12.json) retains these results and
the reporting change's measured correspondence-file delta.

The preceding attempt at the same proof commit stopped after 1,063 recorded
successful commands. Its report has `success: false`; the wrapper's saved
exit-status `0` does not establish a completed verification. Its original
logs, report and exit-status are preserved separately. The completed replay
above supplies the full result. The interruption's cause is not established.

The reporting change updates verification descriptions only. Lean sources,
manuscript source, PDF, archive, manifest, toolchain, dependency pins and
current instructions retain their tested bytes. There are **67 proved
numbered results and ten open mathematical obligations**. Lemma 5.1 is the
first remaining construction.


## Section 5 prerequisites, 13 November 2026

The [prerequisite report](V57_SECTION5_PREREQUISITES_2026-11-13.md) records
the drift check and proof commit `04b6acb8876a7faa0bf712e4633f27d8addc9dcf`.
The weak-choice bridge, binary restriction-product construction and induced
partial-map functor have explicit statement checks and current audit
coverage. All 17 incremental commands passed; the complete transitive
audits cover 871 current modules, 27,470 current declarations and 1,274
retained declarations, using exactly the three permitted axioms. This run
does not replace the preserved full replay. The active manuscript remains
v57, with 67 proved numbered counterparts and ten open obligations.


## Split Turing structure and slice equations, 13 November 2026

The [split Turing report](V57_SPLIT_TURING_2026-11-13.md) records proof
commit `7f361377d4f57b400c672fb30f495d85057dbdc0`. All fourteen product
laws and both prodominical laws are proved, as are Turing parameterization
for arbitrary split objects, total embeddings and partial retractions,
the restriction-terminal property, and the ambient slice parameter and
retraction equations.

All 21 incremental commands passed. Complete transitive axiom audits cover
875 current modules, 27,506 current declarations and 1,274 retained
declarations, with exactly the three permitted axioms. Earlier verification
runs remain preserved. The partial-map slice construction, constant-object
recursion subcategory and splitting equivalence remain open, so the count
remains 67 proved numbered counterparts and ten open obligations.


## Actual partial-slice comparison, 13 November 2026

The [partial-slice report](V57_PARTIAL_SLICE_COMPARISON_2026-11-13.md)
records proof commit `62aef20d5c22faa9f754bb3ee64218e3954f686a`. The monic-span comparison
now works under the printed partial-inverse hypothesis without range or
weak-choice premises. The actual partial-map slice is identified with
ambient partial morphisms over T, preserving restriction and totality.
Fixed-input restriction products and the universal computation with a
total parameter are proved in the actual monic-span quotient.

All 24 incremental commands passed. Complete transitive axiom audits cover
881 current modules, 27,698 current declarations and
1,274 retained declarations, with exactly the three permitted axioms.
Lemma 5.1 still requires arbitrary slice-object products, the constant-object
recursion subcategory and the splitting equivalence. The count remains
67 proved numbered counterparts and ten open obligations.


## Arbitrary partial-slice products, 13 November 2026

The [slice-product report](V57_SLICE_PRODUCTS_2026-11-13.md) records proof commit `647deeeb12d3309d2aede19592e6d7d61bd070c8`.
Arbitrary slice-object products now have all fourteen PCategory laws,
and their induced restriction is proved equal to the existing one.
The evaluator is a Turing morphism for that complete product structure.
Restriction terminal morphisms, total embeddings into the constant
universal family, partial retractions and splitting of every restriction
idempotent are proved in the actual monic-span quotient. The original
recursion-category data yield the universal slice object directly.

All 25 incremental commands passed, including
18 strict commands. Complete transitive axiom
audits cover 890 current modules,
27,874 current declarations and
1,274 retained declarations, using exactly
the permitted three axioms. All 2,377 measured
inputs match the proof commit, and the earlier verification evidence is
preserved. Lemma 5.1 remains open for the full constant-object recursion
subcategory and its splitting equivalence. The count remains **67 proved
numbered counterparts and ten open obligations**.
