# (A) Kill-shots / hard blockers

No false theorem or fatal mathematical defect is established by this **scope and dependency audit** of version 26 of *Logical consequence and essential incompleteness in recursion categories* (77 pages, commit `490418a5eecbefa532e4d9283a7d504e4c611198`). This is an author-side audit of proposed shortening, not a new correctness certificate for the whole manuscript.

The main risk is shortening by erasing comparison data or by calling an application redundant because it reaches another incompleteness conclusion. The manuscript contains several distinct result branches. Its syntactic, numerical, Miller, and cosheaf realizations have different ambient categories and different universal-property obligations. Their conclusions are related, but they are not interchangeable proofs.

The construction of theories in Appendix A is common machinery. It does not itself establish its realization in any of those computational categories. Those application proofs cannot be removed merely by retaining the appendix.

# (B) Major weaknesses

## S1. The current front matter names an older priority and organization

- **Anchor:** Introduction, pp.1–2, `sections/01-introduction.tex:17–42`, “The principal application uses a sequence … constructed by Miller”; lines79–88 give the roadmap. The abstract also devotes most application detail to Miller and cosheaves.
- **Claim as written:** Miller is the principal application; the roadmap places its discussion before the syntactic construction and describes “Sections … models–family” as a range of sections constructing the model functors.
- **Failure mode:** inconsistent_use of the document's organization and contribution priority.
- **Evidence:** the current order is syntax (§5), soundness (§6), arithmetic and uniformity (§7), Miller (§8), cosheaves (§9); the faithful-family section is now Appendix D. The newer core includes Theorems4.2,5.9,6.9,7.3 and7.6, whose role the deferred front matter does not yet describe.
- **Impact:** the shortened outline must choose what mathematical contribution the paper announces. Moving §8 while retaining “principal application” would misdescribe the article. Moving Appendix D while retaining the current range of section references would also leave a stale roadmap.
- **Severity:** major organizational issue for the eventual final manuscript, locally repairable. It is not a defect in a theorem. The author has expressly deferred the introduction and abstract; this audit does not recommend editing them before the scope decision.
- **Repair:** settle the main result and retained applications in the outline, then write the front matter around that final order. Preserve the named mathematical contribution of any moved branch in its companion treatment.

## S2. A reference-only pruning rule would delete necessary data

- **Anchor:** Proposition7.7, p.36, `08c-numerical-realization.tex:38ff`; its post-proof construction of sentence/proof objects and `08d-numerical-incompleteness.tex:55–81`. Theorem9.5, `09-three-point-space.tex:562ff`, has target `Pair(Rec)`.
- **Claim under examination:** material with no incoming theorem-label reference could be removed as unused.
- **Failure mode if adopted:** missing_definition / unproved dependency after the cut.
- **Evidence:** `prop:arithmetic-theory-realization` has no incoming literal `\ref` in the current mathematical source, but its constructed objects and comparison are used by the remainder of §7.4 and by §7.5's subsection reference. `Pair(Rec)` is defined only in §7.6 (`08-essential-incompleteness-of-arithmetic.tex:300ff`); Theorem9.5 uses it. Appendix C is cited by its section label rather than by `prop:missing-lift`. A terminal result need not have a later proof consumer to be a contribution.
- **Impact:** a mechanical reference table is useful evidence but is not the complete mathematical dependency graph.
- **Severity:** a major error in a proposed shortening method, not an allegation that the present manuscript already omits these definitions.
- **Repair:** record three separate facts for each item: explicit citation consumers, semantic consumers of its objects/constructions, and whether it is a stated endpoint. Do not classify a terminal theorem as dispensable solely because its citation count is zero.

## S3. Removing both non-arithmetic branches narrows the representation claim

- **Anchor:** §8, Proposition8.5 and Theorem8.6; §9 and AppendixB, especially Theorem9.4 and PropositionB.10. Introduction lines71–77 asserts that the cosheaf recursion category is not restriction-equivalent to the numerical recursion category.
- **Claim as written:** the construction applies beyond arithmetic, including a representation-independent oracle category and a recursion category built from a nontrivial cosheaf diagram.
- **Failure mode if both branches are silently removed:** unsupported_generalization of the remaining article's advertised examples or representation scope.
- **Evidence:** the syntactic category and ordinary numerical category in §§5–7 do not supply the cosheaf non-equivalence result, the failure of decidable equality on its universal object, the naturality obligations for its propositional folds, or Miller's representation-independence argument. The generic Appendix A theorem is conditional on the required structure and existence hypotheses; it does not prove that these additional models satisfy them.
- **Impact:** moving both application branches can yield a coherent shorter paper on the general construction and arithmetic realizations, but it changes what that paper demonstrates about examples beyond arithmetic.
- **Severity:** major scope qualification if claims are retained without the examples; no counterexample to the existing constructions is alleged.
- **Repair:** either retain one complete non-arithmetic application or state the narrower scope and give precise references to complete companion results. A short example summary cannot replace the required realization proof when the main article claims to establish that realization itself.

# (C) Minor issues

## C1. There is genuine numerical-background repetition available to consolidate

**Anchors:** AppendixB, `b-three-point-cosheaves.tex:87–115`, reproves finite limits, numerical images, preimage descent and regularity of `C_rec`; Proposition7.7 already proves these facts with explicit numerical coding. AppendixB lines602–650 constructs `Q_num:Split(Rec)→Par(C_rec,Mono)` and proves the restriction equivalence; Proposition7.7 now proves the same equivalence by the explicit functor `Q~`.

**Assessment:** necessary numerical background is duplicated within the current combined article. **Evidence label:** structural argument comparing the two stated categories and functor constructions. **Severity:** minor economy issue, repairable by relocation/citation. Keep the detailed proof once, and let AppendixB cite it before proving the new componentwise and naturality assertions for `E=C_rec^J`. The current inverse orientation is immaterial once the named equivalence and its restriction structure are available. If the cosheaf material becomes a separate self-contained document, it must contain this background or use a precise external reference; the internal cross-reference cannot simply disappear.

## C2. The local-connectedness argument for the fork is repeated

**Anchors:** §9.1, `09-three-point-space.tex:146–163`, and PropositionB.4, `b-three-point-cosheaves.tex:241–265`.

The main text describes the same finite-subfunctor probes and domain/value detection used in the appendix proof. A shorter main statement can name the probes and cite the complete appendix proof, rather than present the argument twice. This is an elementary consolidation of the same category and same proof, not a license to suppress the probe types or move the result out of every proof location. **Evidence label:** direct source comparison. **Severity:** minor, repairable.

## C3. Definitions of regularity and related background are repeated

**Anchors:** AppendixA.1 and the paragraph preceding PropositionB.2 (`b-three-point-cosheaves.tex:63–77`).

The regular-epimorphism, regular-category, and regular-image terminology is reintroduced in AppendixB. Choose one primary definition location in the combined article. AppendixA must retain the hypotheses and definitions needed to perform its one job, and AppendixB can refer to that location. The slice/extensivity conventions also need one clear definition rather than repeated introductory prose. **Severity:** minor economy issue; the present repetitions are not mathematical errors.

These confirmed savings are local. They do not justify a claim that twenty or thirty pages can be removed while preserving every present contribution. The larger reduction requires moving complete result branches.

# (D) Cross-section consistency failures

The following table challenges the principal candidate moves. “Optional” refers to the selected main proof route, not to mathematical worth.

| Candidate | Mathematical role and actual dependency | Safe treatment and necessary qualification |
| --- | --- | --- |
| **Appendix D, about3 pages** | TheoremD.1 constructs the faithful all-model family; D.2 uses it for source inseparability under ambient theory extension. The complete-ambient-theory example proves a real limitation: internal inseparability alone does not imply incompleteness of the ambient arithmetic theory. No main proof uses D.1 or D.2; `sec:family` is mentioned in the deferred roadmap. | The whole comparison branch can move. Preserve its result, model-family construction, and limitation example in the companion. It cannot replace the one-model soundness factorization: the functor `F_T:S_T→∏_M Pfn` and the external model K of represented axioms serve different purposes. |
| **§6.1, Lemma6.2 and Corollary6.3, about1 page** | The complementary-source switch proves the single-model source-inseparability result and supplies the family lift in AppendixD. Current arithmetic Theorem7.3 uses the partial proof-search lift of Lemma7.2 instead. | If the source-inseparability comparison branch moves, §6.1 can move with it. Keep Proposition6.1 and §6.2's interpretation structure needed for the soundness route. Do not silently replace Lemma7.2's partial source lift by a totality claim. |
| **§7.4–§7.6** | Proposition7.7 realizes AppendixA in `Tot(Split(Rec))`, while Theorem5.9 realizes it in `B_PA`. Theorem7.3 concerns the latter category and its standard/ultrapower interpretations; §7.5 is an additional numerical source application. §7.6 defines `Pair(Rec)`, used in §9. | Ordinary numerical realization is not a duplicate universal property merely because it uses the same syntax codes. Moving this branch is possible if the main article narrows its representation scope. If the cosheaf branch remains, retain or relocate the numerical-base results and `Pair(Rec)` definition it uses. Do not infer preservation of initial algebras from regularity of `G_N`. |
| **§6.4 ultrapowers** | Theorem6.9 transfers the standard soundness factorization to the whole interpreted proof object, including nonstandard elements. Theorem7.3 expressly asserts incompleteness under these ultrapower interpretations. The standard arithmetic and uniform-independence conclusions need only standard-code soundness. | Logically removable only with the corresponding narrowing of Theorem7.3. It is a distinct factorization/comparison result, not repeated standard soundness. It is part of the recent central development and should not be cut merely because the shortest standard arithmetic proof avoids it. |
| **§8 Miller, about6 pages** | Theorem8.6 is an independent endpoint using §3's source inseparability and Corollary4.3. Proposition8.5 independently proves first-order realization in the representation-independent oracle category. The witness may depend on the oracle representation while the value/domain must not. | A coherent companion branch. A companion needs the comparison/lifting and incompleteness statements, the categorical syntax/rule hypotheses, and the actual realization proof, not just its external real-field model. Moving it removes the current introduction's principal application and its inseparability/non-preservation example. |
| **§9 plus AppendixB, about14 pages** | Gives a genuinely nonnumerical recursion category, its splitting/frames/Turing morphism, propositional syntax and derivation algebras, a consistency proof and endpoint observations. PropositionB.10 proves non-equivalence with the numerical category and failure of decidable equality of V. These results do not precede the arithmetic core. | A coherent substantial companion package. It must retain the construction of `A=Par(C_rec^J,Mono)`, numerical-base facts, the `Split(R_X)≃A` comparison, the generic comparison/incompleteness theorem or precise reference, AppendixA's propositional closure theorem, and the `Pair(Rec)` definition if the observation-functor conclusion remains. Do not call it a pointwise Set construction: the whole-space cosheaf value is a pushout. |
| **Appendix C, about3 pages** | PropositionC.1 proves that the lifting hypothesis of Theorem3.5 cannot be omitted, even for a faithful product-preserving zero-reflecting functor; it also distinguishes joins of idempotents from joins of disjoint arrows. | Retain with Theorem3.5 if the shortened paper still advertises necessity of its lifting hypothesis. It is not needed to prove the positive theorem, but it supports a precise mathematical claim and guards against a false strengthening. It can move with the source-lifting study only if the main scope and claims move accordingly. |

Three type interfaces must survive consolidation:

1. `H_A:D/Fm→D/Fm` and its initial algebra live in the relevant total category D. A realization in one D does not establish one in another. The regular image gives the least theory only after that category's hypotheses and initiality are proved.
2. `G_M:B_PA→Set` preserves the finite limits and images used in the interpretation. The natural isomorphism `U G_N≅G_M` transfers the factorization. Neither assertion supplies a generic initial-algebra preservation theorem. Keeping the actual fold and relabeling proofs avoids this unproved shortcut.
3. The component functors of the fork carry additional naturality and Turing-universality obligations. The endpoint functors preserve the specified universality; the central component does not. A shortened statement must retain that distinction and the reason its endpoint observations are recursively inseparable.

**Concrete scope recommendation:** a shorter core article can retain §§2–7, AppendixA and the lifting counterexample, while moving Miller, the full cosheaf construction/application, and the all-model comparison to complete companion treatments. This yields a paper on the categorical construction and arithmetic realizations, not a paper that itself establishes all the current non-arithmetic examples. The strongest genuinely nonnumerical model is the fork/cosheaf branch. If the main paper's chosen contribution includes proving representation beyond numerical/syntactic arithmetic models, keep that branch or make its complete companion result a precise part of the publication package. That tradeoff should be stated in the outline, not disguised as a duplicate-proof deletion.

# (E) Acceptance conditions, non-negotiable

1. **A contribution statement for the shortened outline.** It must identify the retained general theorem(s), realization(s), and endpoints. Claims about moved examples must be relocated or precisely cited. Failure rejects the proposed outline as a faithful description of the work.
2. **A semantic dependency table.** It must record explicit references, unlabelled construction use, and terminal outcomes separately, including Proposition7.7 and `Pair(Rec)`. Failure means the deletion list is not reliable.
3. **One full proof per retained realization.** Preserve the typed initial algebras, arbitrary target folds, carrier/domain invariants, and relevant code/naturality comparisons. A cross-category shortcut requires a proved comparison theorem with matching hypotheses. Failure requires restoring the omitted proof or dropping the realization claim.
4. **A complete companion package for each moved branch.** List its numerical-base facts, syntax/rule theory, categorical comparison theorem, construction proof, and terminal application. Failure leaves the moved result undocumented and blocks claiming it has been preserved.
5. **One primary location for genuinely duplicated proofs.** The numerical regularity and partial-map equivalence may be cited from Proposition7.7 in AppendixB; new fork naturality arguments must remain. Failure is an economy defect rather than a false theorem, but leaves a concrete requested reduction unfinished.
6. **Preserve the mathematical qualifications.** The validity object is an external Set-subobject; standard code interpretation and the semantic model K are distinct; an internal inseparable pair alone does not imply ambient logical incompleteness. Failure risks changing the theorem rather than shortening its presentation.
7. **Reconcile the final front matter after the scope changes.** The present Miller-principal and `models–family` roadmap cannot survive arbitrary branch moves. This is required when implementing the outline; it does not reopen the author's decision to defer those edits until the end.

# (F) Not checked / uncertainty log

The audit inspected the current document assembly, front matter, definitions and statements throughout the main sections and appendices, the explicit-reference interfaces, the complete generic comparison/lifting and interpretation arguments, the arithmetic/ultrapower interfaces relevant to the proposed cuts, the Miller and fork application chains, both computational category constructions, the all-model comparison, and the lifting counterexample. It read source rather than using earlier PASS dispositions as proof of independence.

This is not a new line-by-line correctness audit of every proof. In particular, the long PA-internal syntax/list/substitution and general derivation proofs in §5, the algebra-equivalence details of the indexed family in §7.2, and every constructor/encoding verification in the expanded §7.4 were used through their explicit statements and inspected interfaces rather than re-proved in this scope task. Bibliographic claims and novelty were not freshly checked against primary literature. No Lean elaboration, new compilation, or global layout validation was performed by this reviewer. Page quantities are approximate from the current section starts and can shift after actual repagination; no exact shortened page count is certified.

**Strongest confirmed blocker:** no false theorem; the current deferred front matter and a proposed cut list must be reconciled with the actual chosen scope, and a reference-only deletion rule is inadequate.

**Strongest suspected unconfirmed blocker:** none promoted to a finding. No new preservation theorem or counterexample is invented to justify a cut.

**Most important thing not checked:** the full semantic dependency inventory for every unnumbered construction requires the parent synthesis alongside the mechanical reference graph; the interfaces identified above are confirmed examples, not proof that a reference scanner finds all of them.

**Dependence on unavailable material:** none for the source-based scope conclusions. The audit does not require a claim about the publication prospects or literature originality of the contributions.

**Final recommendation:** unknown for a whole-paper publication decision. The proposed focused-core/companion organization is mathematically viable subject to the seven explicit preservation conditions above. Do not shorten it by suppressing types, replacing full realization proofs by assurances, or silently retaining the broader claims of moved branches.

---

## Superseding addendum — the cosheaf construction remains in the paper

The author has fixed the scope: §9 and Appendix B remain. This supersedes the option in (D) of moving the cosheaf branch to a companion. Its role is mathematical: the paper is to construct logical consequence in a recursion category beyond the numerical prototype, and to prove that this example is not restriction-equivalent to that prototype. Proposition B.10 supplies that distinction, while §9 proves the propositional realization and its consequences. The author's stated motivation from Heller supports this choice of examples; no fresh claim about the wording or historical scope of Heller's paper is made by this audit.

The retained contribution therefore includes the general categorical construction of theories, the syntactic arithmetic realization with standard and ultrapower soundness comparisons, and the fork/cosheaf propositional realization. Appendix A.6 is a direct dependency of the latter. A shorter outline must preserve those three parts rather than treat the last as an optional illustration.

### Numerical foundation required by the retained cosheaf branch

I independently reread the relevant source interfaces for this addendum, including the first 240 lines of §7.4, all of §7.5, the definition of `Pair(Rec)` in §7.6, §9's evaluation and endpoint-inseparability argument, and Appendix B's numerical comparison and distinction proof. The following are semantic dependencies, not conclusions from reference counts.

| Numerical material | Retained consumer | Required treatment |
| --- | --- | --- |
| `Rec`, its objects in `O`, and the carrier bijections `gamma_X` | Appendix B, lines608–647, constructs `Q_num:Split(Rec)→Par(C_rec,Mono)`; §9, lines179–182, uses that equivalence. | Keep the numerical category definition and its restriction structure. The object types and carrier bijections already have a retained source in syntactic §5. |
| `C_rec`, finite limits, disjoint pullback-stable coproducts, regular images, surjective descent | §9 defines `E=C_rec^J`; Proposition B.2 proves its componentwise structure and the subsequent partial-map construction uses it. | Keep one full numerical-base proof, currently §7.4, lines18–35 and113–160. Appendix B may cite it while retaining the new diagram-category proof. |
| Computable partial inverses of monomorphisms; `Tot(Split(Rec))≃C_rec`; `Par(C_rec,Mono)≃Split(Rec)` | Appendix B's comparison and Proposition B.10; §9's evaluation functors. | Keep the equivalences and their restriction structure, currently §7.4, lines63–210. Specify the orientation and chosen comparison functor when replacing Appendix B's second construction by a citation. |
| `J_rec:Rec→Pfn` and the underlying-partial-function interpretation | Appendix B, lines608–616, explicitly uses `J_rec` in the formula for the coded map. | Move its definition and necessary preservation facts out of the numerical arithmetic application if that application moves. They belong with the numerical foundation. |
| Computability of switches for complementary c.e. domains | §9, lines313–326, applies Theorem3.5 to `K_2` and derives recursive inseparability of the endpoint pair. | Preserve the elementary computability argument. §9 already proves the fact in its own target category; the sentence citing the arithmetic section is a comparison, not a dependence on the numerical first-order proof object. |
| `Pair(Rec)` | Theorem9.5, §9, lines562ff, has this category as its target; lines579ff use the definition. | Retain its definition from §7.6, lines300–306, in the numerical foundation or immediately before the observation theorem. The arithmetic assignment `T↦(omega,P_T,N_T)` is a separate application. |

These dependencies do **not** require the full numerical first-order syntax realization. In §7.4 the structural proof ends at line210. The parameterized syntax folds begin at line212. The subsequent substitution, derivation-fold and numerical/syntactic proof-code comparisons establish an additional realization in `C_rec`; they are not used to construct §9's propositional formula and derivation algebras. Section9 constructs those algebras in `E` and checks naturality there, using Appendix A.6. Its endpoint diagonal is constructed from its own `tau` and `zeta` (§9, lines277–326), rather than imported from the ordinary numerical arithmetic diagonal.

Likewise, §7.5 has two distinguishable parts. Lines6–16 and28–48 supply numerical structure and the switching fact. Lines56–81 use the numerical proof-code comparison to obtain the further numerical arithmetic incompleteness result. Retaining the former does not require retaining the latter in the main article. The ordinary numerical diagonal pair in lines17–26 and49–54 is not the fork endpoint pair; §9 proves the endpoint result separately.

There is consequently a mathematically coherent split of Proposition7.7: one proposition for the numerical categorical foundation and restriction equivalences, and a second result for the full numerical first-order realization. If the latter moves, its statement, parameterized folds, substitution and derivation proofs, and typed code comparison must move together with §7.5's numerical arithmetic application. Keeping the combined statement while relocating half its proof would be an incomplete proposition. No initial-algebra preservation theorem may be substituted for those proofs. The retained main syntactic realization is Theorem5.9 in `B_PA`; the retained soundness comparison is §6, including the ultrapower theorem. Neither depends on the later numerical realization in §7.4.

### Consolidations and optional relocations

The following changes have mathematical grounds under the fixed scope.

1. **Consolidate numerical background once.** Proposition7.7's structural proof and Appendix B, lines87–115 and608–647, establish the same numerical regularity and restriction-equivalence facts. Keep the complete typed proof in the retained numerical foundation. Appendix B must still prove the componentwise and naturality assertions for `E=C_rec^J`, the partial-map structure, the Turing morphism, and the splitting comparisons for the fork. These are additional theorems, not consequences of the numerical equivalence alone.
2. **Consolidate the fork's local-connectedness proof.** Section9, lines146–163, and Proposition B.4 repeat the same finite-subfunctor probe argument. State its role and the probe types in the main text; retain its full proof once in Appendix B. The observations by the two endpoint probes, and the central component's failure to preserve the selected Turing morphism's universality, are distinct claims and remain.
3. **Use one primary location for general categorical definitions.** The repeated regularity definitions in Appendix B can cite Appendix A.1. Appendix A remains self-contained. This removes duplicated definitions without deleting any existence or preservation hypothesis.
4. **Miller §8 is a possible separate application.** Its representation-independent oracle realization and real-field application form a distinct theorem chain. No retained cosheaf proof was found to use that chain. Moving it changes the examples established in this article and requires the eventual front matter to cease calling it the principal application; it does not remove the retained nonnumerical representation supplied by §9 and Appendix B. Its complete realization proof must accompany its theorem if relocated.
5. **Appendix D may move with Lemma6.2 and Corollary6.3.** These are the complementary-conditional lifting and single-model source-inseparability results in subsection6.1, followed by the faithful all-model family in Appendix D. The arithmetic soundness route uses the separate partial proof-search lift of Lemma7.2. The retained cosheaf route checks its numerical endpoint switch directly. Neither needs the all-model family. The complete-ambient-theory example remains part of the relocated comparison branch and records a genuine limitation.
6. **The full numerical first-order application may be relocated after the split just described.** This preserves a numerical foundation for the cosheaf example while leaving the main paper's first-order arithmetic development in the syntactic category. It is a scope choice, not a claim that the two realizations have the same universal property in the same category. The `Pair(Rec)` definition and other foundational facts listed in the table must remain available.

The numbering in item5 is essential: **Lemma6.2 and Corollary6.3** are candidates for relocation. **Subsections6.2 and6.3**, which construct the total interpretation and standard-code soundness factorization, are retained. Subsection6.4's ultrapower comparison and its corresponding clause in Theorem7.3 are also retained. The ultrapower theorem addresses the whole interpreted proof object, including nonstandard codes, and is not a duplicate of standard-code soundness.

The seven acceptance conditions in (E) continue to govern the shorter outline with its scope fixed by this addendum. In particular, §9, Appendix B and Appendix A.6 are retained; the main syntactic arithmetic and ultrapower soundness arguments are retained; every relocated application remains a complete theorem package; and the numerical structural foundation and `Pair(Rec)` remain defined before their retained uses. No manuscript edit has been made in this audit. No exact page saving is claimed. The proposed boundary is between necessary categorical foundation and additional realization/application theorems, not between frequently and infrequently cited results.

---

## Final scope addendum — retain the applications and merge the numerical foundation

The author's subsequent direction retains **Miller, the syntactic categories `S_T`, and the cosheaf application**, and requires the numerical foundations to appear once, using the best parts of the two existing presentations. This is now the governing scope. The application-relocation options discussed above are not selected recommendations. The retained article includes all of its current application branches, the full numerical first-order realization and its arithmetic application, Appendix A.6, and the standard and ultrapower soundness comparisons. The recommendation is consolidation of genuine duplicates while preserving the mathematical results.

The appropriate numerical consolidation has one primary foundation result, followed by the full numerical logical realization. Its proof should combine the following material already present:

- **Definitions and coding:** `Rec`, `J_rec`, `C_rec`, the tuple codings including dimension zero, and the chosen formal-object carrier bijections. Keep these available before the fork's comparison and observation functors. Section9's repeated introduction of `C_rec` can refer to this primary definition.
- **Regular and coproduct structure:** the explicit finite-limit, image, kernel-pair descent, and tagged-coproduct proofs in §7.4, lines113–160. They provide a complete numerical foundation that Appendix B, lines87–115, need not re-prove.
- **Total and partial comparison:** §7.4's typed `Q`, `F`, their natural isomorphisms, computable partial inverses of arbitrary monomorphisms, and the restriction equivalence `Par(C_rec,Mono)≃Split(Rec)`. Retain the useful orientation and object/morphism formulas for Appendix B's `Q_num:Split(Rec)→K`; its value on `(X,e)` must be typed as the object `(1,D_e)` of `C_rec`, rather than left as an untyped subset. The one established equivalence supplies full faithfulness and essential surjectivity. A second complete proof of the same equivalence is unnecessary. If a chosen quasi-inverse replaces the current explicit `Q_num`, state the relevant isomorphism instead of treating two chosen functors as literally equal.
- **Numerical observations:** retain `J_rec` and the definition of `Pair(Rec)` once. Keep the arithmetic and cosheaf observation constructions as their separate applications. The endpoint switching fact remains proved for the actual endpoint target in §9; the cross-reference to the numerical switch can point to the foundation.

The full numerical first-order realization still needs its own parameterized folds, substitution structure, derivation initiality and proof-code comparison after that foundation. These are retained, rather than replaced by transport through an unspecified interpretation functor. Appendix B still needs all new facts about `E=C_rec^J`, its partial-map category, Turing morphism, restriction splitting, and the non-equivalence/no-decidable-equality result. Only the repeated numerical-base proof is consolidated. Likewise, §9's local-connectedness proof can be presented once in Appendix B while its typed probes and uses remain explicit in the main section.

**Appendix D together with Lemma6.2 and Corollary6.3 remains an optional future relocation, not a selected change.** The distinction from subsections6.2 and6.3 remains as stated above: those subsections and the ultrapower subsection are part of the retained soundness route. No deletion is justified merely by the absence of a later citation, and no reduction in the theorem inventory is recommended by this final addendum.

The independent numerical dependency checks recorded in the previous addendum continue to apply: they explain where the merged foundation is consumed. They no longer support relocating the numerical logical application, because that application is now expressly retained. The seven conditions in (E) apply to this consolidation-only scope, with its companion-package condition dormant unless the author later selects a relocation. No manuscript changes were made, and no exact page reduction or whole-paper correctness certificate is claimed.
