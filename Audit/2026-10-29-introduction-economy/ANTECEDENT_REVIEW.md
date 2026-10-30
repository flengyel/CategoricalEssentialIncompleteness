# Whole-manuscript antecedent and terminology review

This report records the complete-source prose audit requested after the
initial Introduction plan. The baseline is
`manuscript/essential_incompleteness_via_local_connectedness.tex`,
repository main `c5533a6`, SHA-256
`99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21`.
The author is revising that source concurrently; the anchors and proposed
repairs below refer to this baseline and are not a final-status assertion
about a later file. No main-source edits were made by this reviewer.

The manuscript's mathematical objects are substantially more precise than
some of its prose labels. The chief defects are the undefined effective
diagram label, several unnamed comparisons, some omitted local variable
introductions, and descriptions that blur a range idempotent with its
split image object or a carrier-total map with an ambient-total recursive
function. They can be repaired without changing the constructions.

The complete source, including all appendices and bibliography, was read;
the current pass checked each paragraph and display for antecedents and
scope, with a second independent reading of Appendices A–C. Existing
mathematical proof verification is not replaced by this prose audit.
The mathematical-writing plugin and the supplied Knuth–Larrabee–Roberts
Section 1 excerpt govern the review. Verified source principles applied
are self-contained statements (5), connected prose and variables explained
at introduction (10–11), reader expectations (12), consistent notation
(14), and unambiguous sentences (17). The author's stricter requirements
govern specialized abstract terminology and the requested full-source
scope.

## Coverage in reading order

| Source block | What was checked | Finding |
| --- | --- | --- |
| Title, metadata, abstract | Antecedents of “the theory,” “these functors,” and “this”; theorem preview; effective-diagram label. | “The theory” needs an explicit quantified theory, and the diagram label needs actual carriers/arrows. The abstract's class of extensions must stay explicit. |
| §1 | Motivation before machinery; historical comparison; range-functor and lifting descriptions; source/target direction; primed/unprimed systems; effective step. | Follow `OUTLINE.md`: shorten repeated setup, specify the particular selecting-map lift, and replace the unmotivated effective-diagram label. |
| §2 | Every restriction equation and variable scope; idempotents versus split objects; functor definition; coproduct comparison; totality; Turing parameters. | The coproduct comparison should be named and typed. The range-functor definition does not require product preservation. |
| §3 | Program index/class/predicate distinctions; formal types; graph equations; range description. | Define `[e]_T` explicitly. The range and graph conventions otherwise give the intended meanings. |
| §4 | Object and arrow actions of `F_M`; nonstandard traces; references to composition/domain/range formulas. | The arrows and coordinates have identifiable antecedents. Product preservation is a proved property of these particular functors. |
| §5 | Families, coordinates, faithfulness, projection/quotient directions, commuting square. | Replace the unspecified “chosen computational operations” by the actual preserved operations for `Q`. |
| §6 | Types of sections and lifts; source versus target totality; all theorem hypotheses; copairing and inverse-image references. | Type the target section, name the comparison, replace the ambiguous possessive before inverse images, and quantify `T′` in the corollary. |
| §7 | Observation operation versus functor; fixed numerical pair; proof/refutation sets; pair-category arrows and separator pullback. | Replace “identity-arrow reductions” with the actual identity morphism in the defined pair category. |
| §8 | Diagram category, domains/ranges, endpoint maps, probe construction, theorem scope. | Replace the loose diagram labels, distinguish image objects from range idempotents, and bind the endpoint index explicitly in the final theorem. |
| Appendix A.1–A.2 | Component probes, total-category descent, partial domains and images, range agreement. | Repair the singleton-source antecedent and carrier-total descriptions; express definedness at the chosen element directly. |
| Appendix A.3–A.5 | Word universal property; exact-domain Turing factorization; full subcategory; splitting functors. | Name the semigroup and extending morphism; keep component value maps carrier-total; name the classical splitting comparison functor and its direction. |
| Appendix B | Grammar, formula/proof transitions, initiality, theorem images, finite valuation and its component scope. | No additional consequential antecedent defect found. The final valuation is deliberately not asserted to be a natural Boolean map. |
| Appendix C | Oracle/index notation, actual domains versus program extensions, target inclusion, categorical separator and failed lift. | No additional substantive antecedent defect found. Replace the grammatical “Their total arrows” by “The total arrows” if that wording remains. |
| Bibliography | Referents and consistency with body labels. | No private LOC/three-point citation remains. Quoted bibliographic titles should not be rewritten to enforce prose terminology preferences. |

## Necessary clarifications and concrete replacements

### 1. Effective diagrams and cosheaves

**Anchors:** abstract “using computable diagrams”; Introduction “These
are computable diagrams”; §8 “The computational diagrams form”; Appendix
A “a computational diagram” and “a computational diagram map.”

The shorthand does not tell a reader which effective structure is meant.
The actual construction is already precise: diagrams of shape
`J=(1←0→2)` in `C_rec`, whose objects are c.e. subsets of finite powers
of `N` and whose arrows are partial recursive functions total on their
source carriers. Use this description once in the Introduction and the
formal category definition in §8; thereafter write “a diagram in
`C_rec`,” “an object of `E`,” or “a morphism in `E`.”

Do not equate this category with all set-valued cosheaves on the space.
The underlying set-valued fork determines such a cosheaf; the numerical
carrier and recursive-arrow restrictions define the actual category used.
Nor should the wording suggest numerical injective coding of every global
pushout: Appendix A correctly treats that value as a quotient. A generic
“computational cosheaf” label adds no information unless expressly defined
by this construction. Use the category and maps directly instead.

### 2. A named, typed coproduct comparison

**Anchor:** §2, range-functor definition; §6 theorem and join criterion.

The phrase “under the coproduct comparison” suppresses a standard map
whose direction matters in the displayed lifting equation. Add to the
definition:

> The canonical coproduct comparison is
> `χ_{X,Y}=[F i_0,F i_1]:FX+FY→F(X+Y)`; preservation requires this
> map to be an isomorphism.

Declare that later coproduct identifications use `χ`, or write the exact
lifting equation `Fℓ_c=χ_{U,U}s_c`. Type the section in the theorem as
`s_c:FU→FU+FU`. Without the identification, the currently displayed
`Fℓ_c=s_c` has different written targets. This is a suppressed comparison,
not evidence that the intended theorem is false.

This change must not introduce a product comparison or product-preservation
hypothesis. General range functors here preserve restrictions, ranges,
zeros and binary restriction coproducts. The model functors and endpoint
functors separately have product-preservation results.

### 3. Program equivalence classes

**Anchor:** immediately after `eq:uniform` in §3.

The notation `[e]_T` later denotes an arrow but is not introduced
explicitly. Add:

> Write `[e]_T` for the equivalence class of the typed program index `e`.

This keeps `[C]_T`, already defined as the partial identity represented by
the predicate `C`, from having to serve as an implicit definition of the
different notation for a program class. In the selecting-program proof,
ensure that `G_s` is understood as the graph formula of the chosen program
representing the arrow `s`; a short declaration of that representative
is sufficient if the rewrite otherwise makes the distinction unclear.

### 4. Unspecified operation bundle

**Anchor:** §5, after the definition of `Q_{T,T′}`, “It preserves the
chosen computational operations and Turing morphism.”

Replace by:

> The functor `Q_{T,T′}` preserves restrictions, zeros, ranges, binary
> restriction products and coproducts, and the chosen Turing morphism.

These are properties of this quotient functor, proved by the unchanged
program representatives. The sentence should not read as a definition
of an additional unnamed class of functors.

### 5. Local antecedents in the lifting argument

**Anchors:** proof of `thm:local-lifting`; `cor:pair`.

Replace “its inverse images of the summand domains” by “the inverse
images under `s_c` of the summand domains.” The preceding sentence contains
several arrows and domains, while `s_c` is the map whose inverse images
are required.

The corollary's final sentence should begin:

> For every consistent extension `T′⊇T`, the images under `Q_{T,T′}`
> are the identically defined inseparable pair in `S_{T′}`.

This binds `T′` within the statement rather than relying on the earlier
section's discussion of theory inclusions. Subsequent uses of “the lifting
hypothesis” should point to `thm:local-lifting` or its explicitly named
condition; no separate informal “comparison theorem” is needed.

### 6. State the pair morphism, not a new reduction label

**Anchor:** §7, “The inclusions of `A,B` give identity-arrow reductions…”

Use:

> The identity function defines a morphism
> `(ω,A,B)→(ω,P_T,N_T)` in `Pair(Rec)`.

The pair category has just been defined, so this is both shorter and
mathematically explicit. The following separator-pullback argument then
has a named kind of morphism to which it applies.

### 7. Range idempotents and image objects

**Anchors:** §8, partial-arrow description; Proposition
`prop:fork-structure` in Appendix A.

Change “its range is the subdiagram of component images” to:

> Its range is the partial identity on the subdiagram of component images.

Change “Its ranges are the regular images of the value maps” to:

> Its range idempotents are the partial identities on the regular images
> of the value maps.

This matches the range definition in §2 and retains the distinction
between an idempotent in the partial category and its split image object
in the total category. The notation `E_i(e)` versus `|e|_i` already makes
the corresponding distinction correctly in the observation argument.

### 8. Explicit endpoint range

**Anchor:** `thm:cosheaf-observation`, “Fix either endpoint `i`.”

Replace by “Fix `i∈{1,2}`.” The theorem is then independent of a reader's
remembering the endpoint convention from the previous subsection.

### 9. Total on a carrier is not ambient total recursion

**Anchors:** §8 object/morphism description; Appendix A.1 descent;
Appendix A.4 value maps for a partial diagram.

The numerical category allows partial recursive functions total on their
specified c.e. source carriers. It does not require total recursive
extensions on the ambient numerical space. In particular:

- “the unique total recursive map `v:Z→W`” should be “the unique partial
  recursive map `v:Z→W` that is total on `Z`”;
- “total recursive value maps `F_j:D_j→V_j`” should be “partial recursive
  value maps `F_j:D_j→V_j` total on `D_j`”;
- the maps `s_j:N^{m_j}→N` from numerical specialization really are
  total recursive on the whole stated numerical powers, so retain that
  stronger wording there.

Likewise, after defining `C_rec`, describe morphisms of `E` as commuting
triples of arrows of `C_rec`, rather than leave “total recursive component
maps” to carry an ambiguous convention.

### 10. The source of the singleton probes

**Anchor:** proof of `prop:fork-total`, after the diagrams `H_j`.

“These maps are computable, since their nonempty components are
singletons” grammatically attributes singleton components to maps.
Replace by:

> These maps are computable because every nonempty component of their
> source `H_j` is a singleton.

The mathematical point concerns maps out of finite singleton source
components, not arbitrary values or target components.

### 11. Definedness at the chosen image element

**Anchor:** proof of `prop:fork-structure`, range agreement.

After choosing `z∈(I_f)_j`, replace “`g_j(z)` and `h_j(z)` are defined
on the same inputs and have the same values” by:

> The map `g_j` is defined at `z` exactly when `h_j` is, and their values
> there agree.

The chosen element is the input. Its partial values do not themselves
have an input domain.

### 12. Name the word extension and the splitting functor

**Anchors:** Appendix A.3, free-semigroup paragraph; Appendix A.5,
comparison with the classical category.

For the word universal property, name an internal semigroup `M` in `E`
and a total diagram map `f:Y→M`, then state that there is a unique
semigroup map `f^#:Y^#→M` extending `f` along singleton insertion.
This avoids the ambiguous “to it” / “its unique extension” chain and
types the universal property.

For the classical splitting, replace “This proves both essential
surjectivity and full faithfulness of the comparison” by:

> The functor from the restriction splitting of `Rec` to `K`, defined
> on objects and arrows by the domain-subset construction, is therefore
> fully faithful and essentially surjective.

The source, target and direction of the comparison are then explicit.

## Statements checked and not treated as defects

The general range-functor theorem does **not** assume that `F` preserves
products. Its source is a prodominical recursion category with ranges and
binary restriction coproducts. Its target is split and locally connected,
has ranges, restriction zeros and binary restriction coproducts, satisfies
weak choice, and has inverse images preserving binary domain joins. The
remaining data are a source Turing morphism, an isomorphism `U≅U+U`,
`F(1_U)≠0`, and lifts of the sections belonging to every complementary
source pair. The proof takes the image of the already formed composite
`bτΔ_U`; it does not replace it by a composite using a product comparison.

The specific functors `F_M`, `F_T`, `Q`, the endpoint functors, and the
counterexample inclusion have separately stated product-preservation
properties. Those are not grounds for adding product preservation to the
general definition or theorem.

The actual theorem retains lifting. Appendix C precisely describes the
statement with that hypothesis dropped. The disjoint-arrow-join criterion
is present and uses range agreement rather than preservation of arrow
joins. Its private-source antecedent was Proposition 4.8; the criterion
was not missing from that source.

Several local names do have mathematical definitions and need not be
removed indiscriminately: `S_T`, the word frames, endpoint probes,
`|e|_i`, the polynomial syntax algebra, and the stated extension class.
The phrase “computational extension” is explicitly defined by a domain
on the syntax object with rule closure; if retained, its meaning is that
definition, not a claim about arbitrary external extensions. The shorter
phrase “computational cosheaf,” by contrast, is not needed to specify the
actual diagram category.

No further consequential antecedent issue was found in the finite proof
grammar or the consistency argument. The two proofs determine the finite
positive support; the valuation is chosen at a fixed component. The final
componentwise empty-domain conclusion explains its internal consequence
without claiming a natural Boolean valuation or global separator.

## Next pass

The Introduction economy plan and these repairs should be checked against
the rewritten file, not marked resolved merely because they were proposed.
That pass should record its new source hash, verify every changed anchor,
repeat the loose-term and unnamed-comparison search, and inspect the
rendered pages affected by the rewrite. All existing mathematical proofs
must remain. This report does not claim to have compiled a new version or
to have certified new mathematics.
