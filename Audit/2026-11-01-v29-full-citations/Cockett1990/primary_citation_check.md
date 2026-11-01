# CockettLists: primary citation check

The outstanding citation use is **verified from the original primary article**. No mathematical or bibliographic correction is required in version 30. The former `existence verified/fulltext unavailable` use status can be replaced by `verified`; the claim-bearing primary text has now been read. This closes only the CockettLists access limitation, not a fresh audit of any other reference.

## Scope and exact claim

The manuscript is *Logical consequence and essential incompleteness in recursion categories*, version 30, 1 November 2026. This check covers `output/manuscript/local_connectedness/appendices/a-syntax-and-theories.tex`, lines 148–157, and its CockettLists bibliography entry. No manuscript edits were made. The current local source, not only the frozen version-29 source, was checked.

Lines 148–154 define stability under parameters for an initial algebra: replace constant objects by their products with P over P, form the endofunctor in the slice, and require the pullback of the initial algebra along P→1 to be initial in that slice. Lines 155–157 say:

> For list objects, this is the parameterized recursion property studied by Cockett; its formulation by pullback into slices is recalled by Maietti.

The attribution is expressly limited to list objects. The preceding extension of terminology to other finite polynomial functors is the manuscript's definition; these sentences do not attribute existence or parameter stability of general polynomial or many-sorted syntax algebras to Cockett.

## Bibliographic metadata

| Field | Checked value | Evidence |
|---|---|---|
| Author | J. R. B. Cockett | Printed title page, p.1 |
| Exact title | *List-arithmetic distributive categories: Locoi* | Printed title page, p.1; the final letter is capital I in the all-caps title, not the digit 1 |
| Journal | *Journal of Pure and Applied Algebra* | Printed title page, p.1 |
| Volume and year | 66 (1990) | Printed title page, p.1 |
| Issue | 1 | Publisher-deposited cached Crossref record |
| Pages | 1–29 | Printed title-page journal header; 29-page PDF |
| DOI | 10.1016/0022-4049(90)90121-W | Publisher-deposited cached Crossref record; PDF metadata supplies the corresponding PII |

The current bibliography matches all these values. The Crossref record uses a lowercase terminal `w`; DOI case does not change the identifier. October 1990 appears in Crossref, but the manuscript does not give a month and needs none. A web recheck of the Crossref endpoint was unavailable; no secondary web result was substituted for the cached publisher-deposited record. The supplied original PDF directly supplies all bibliographic fields except the issue and explicit DOI string.

## Primary evidence and translation

PDF pages coincide with printed journal pages: this PDF has no added cover. The following results and their immediate context were read, with the principal mathematics visually checked against the page images.

1. **Section 2, pp.5–6; Proposition 2.1, p.6.** Cockett defines rec(A,B) with maps r₀:B→rec(A,B) and r₁:A×rec(A,B)→rec(A,B), universal among A-actions supplied with a map from B. Proposition 2.1(iv) identifies this as the initial algebra for B+A×−. Thus list(A)=rec(A,1) is an initial algebra for 1+A×−. Mere unparameterized initiality is distinguished from parameterized recursion in the following paragraphs on p.6.

2. **Lemma 2.2 and Definition 2.3, p.7.** For an object P, Cockett defines I_P:D→D/P by I_P(X)=(X×P→P), the product projection. Lemma 2.2 identifies the recursive object on I_P(A),I_P(B) with the appropriate projection from rec(A,B×P). The following displayed comparison has type

   χ_{A,B,P}: rec(A,B×P) → rec(A,B)×P.

   Definition 2.3 calls recursion parameterized when I_P preserves recursion; the preceding paragraph says exactly that this comparison being invertible expresses that preservation. The statement concerns the pullback functor along P→1, written with the product factors in the opposite order from the manuscript.

3. **The paragraph after Definition 2.3 and Definition 2.4, p.7.** The source identifies list(A)=rec(A,1), obtains rec(A,B)≅list(A)×B under parameterized recursion, and defines list arithmetic by the existence and parameterization of rec(A,B) for all A,B. These statements directly support the manuscript's term “parameterized recursion” for lists.

For a precise comparison with the manuscript, put B=1 in Lemma 2.2 and Definition 2.3. In D/P the relevant endofunctor is

   Z ↦ 1_P + (A×P→P)×_P Z.

Its recursive object is the slice object furnished by rec(A,P). Definition 2.3 identifies this, via χ_{A,1,P}, with (list(A)×P→P). This is exactly initiality of the pullback of list(A) for the slice list endofunctor. Swapping the product factors gives the manuscript's (P×list(A)→P) and (P×A→P). These are canonical product isomorphisms, not an additional assumption.

Cockett's composition convention is explicit on **p.4**: categorical composition runs in diagram order. His f·g means first f, then g; in the manuscript convention gf=g∘f, this is gf. For h=act(x,y), Cockett's universal-property diagram on p.6 therefore says, in manuscript notation,

   h r₀ = y,    h r₁ = x(1_A×h).

The comparison χ on p.7 has seed r₀×1_P and action (a,(r,p))↦(r₁(a,r),p). This typed description avoids reversing the source's projection/composition strings. Its type, action, and invertibility agree with the preservation claim above.

## Distinction from the stronger slice theorem

**Proposition 6.1, pp.24–25**, shows a locos is list arithmetic. **Proposition 6.6, pp.27–28**, establishes connected-limit closure of prerecursives. **Proposition 6.7, p.28**, then establishes local list arithmetic: the slice D/P has recursive/list objects on **arbitrary slice objects** f:A→P, obtained by a pullback construction. The paragraph immediately before Proposition 6.7 explicitly separates recursive objects on parameterized objects, already supplied by Lemma 2.2, from arbitrary objects of the slice.

This is a stronger issue than the manuscript's requirement that an ambient list initial algebra remain initial after pulling it into a slice. The current attribution at lines 155–157 uses the p.7 definition, and does not rely on or claim the full conclusion of Proposition 6.7. There is no conflation to repair. This citation check verifies the claim-bearing definition and its relation to the manuscript; it does not certify all proofs in the source article.

## Audit transition and action

- Metadata status: retain `verified`; replace the obsolete caveat “Original fulltext support remains unverified” with this original-PDF evidence.
- Citation-use status: change `existence verified/fulltext unavailable` to `verified`, with `fulltext_status: verified_primary_claim_bearing_text_read`.
- Exact locator: **Section 2, pp.5–7, especially Lemma 2.2 and Definition 2.3, p.7**. Definition 2.4 on p.7 supplies the name “list arithmetic.”
- Required correction: **none**.
- Optional local improvement: `Cockett~\cite[Definition~2.3]{CockettLists}`. The unqualified existing citation is accurate.
- Combined audit: the sole CockettLists open-access check can be closed. This report does not alter any other row, status, count, or finding.

The attached journal PDF was read directly at `upload/cockettListarithmeticDistributiveCategories1990.pdf`; no Library tool was used. Its SHA-256 is `498c616cde927654db68da87b0c838aced4e852a2199f3cb34e78fcf5ba146cc`. `provenance.json` and `sha256sums.txt` record source, source snapshots, prior audit evidence, and visually inspected page images. *Mathematical Writing* §1 was consulted from the existing local copy for the narrow review method; the mathematical comparison above is an independent primary-source check, not a mathematical assertion attributed to that writing guide.
