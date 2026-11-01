# Independent source-proof observation: Cockett p.18

This is separate from `primary_citation_check.md`. It records only an independent visual and typed check of the printed proof of Lemma 5.6, requested after the citation check. It does not establish that Lemma 5.6 or Theorem 5.5 is false, and does not affect the manuscript's supported citation to Definition 2.3.

The original printed page 18 was visually inspected in `rendered/sourceproof-18.png`. Cockett composes in diagram order, so f·g denotes g∘f.

- **Statement:** The action-preservation equation is correctly printed as (1_A×a)·g=r₁·a, with g:A×X→X. An OCR transcription that substitutes r₁ for that occurrence of g is inaccurate. There is a separate minor naming typo: the statement introduces f:B→X but writes r₀·a=b, with b undefined; f is the intended seed.
- **Proof display:** It places r₁ after 1_A×a (and similarly after 1_A×a′). But 1_A×a:A×R→A×X while r₁:A×R→R, so these printed composites are ill typed. The well-typed action map at that position is g:A×X→X.
- **Cancellation:** With g substituted for those occurrences of r₁, the displayed argument gives g∘⟨y_A,a∘y′⟩=g∘⟨y_A,a′∘y′⟩. The next line needs to conclude a∘y′=a′∘y′. This cancellation would follow from monicity of g, which is not among the hypotheses: g is an arbitrary target action. Monicity of the source constructor r₁ does not justify canceling g.

Thus the proof of the pullback assertion in this particular printed uniqueness argument is not justified as written. This is more than the f/b naming typo, because a direct type correction of the display leaves a missing cancellation hypothesis. A different uniqueness proof or a substantive repair may establish the stated theorem; no claim about impossibility of such a repair is made here. Do not import the printed proof verbatim as an already checked argument.

Source: *List-arithmetic distributive categories: Locoi*, J. R. B. Cockett, Journal of Pure and Applied Algebra 66 (1990), 1–29, printed p.18. PDF page = printed page. Original PDF SHA-256: `498c616cde927654db68da87b0c838aced4e852a2199f3cb34e78fcf5ba146cc`.
