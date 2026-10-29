# Source checks and prior work

## Current committed sources

The local sources used were checked against Git blob identifiers in the
recursive tree of base commit `b20c3d89757a692314413e7d83fcf4511a4f3b22`:

| Source | Git blob |
| --- | --- |
| Original 23-page note | `8f7c64d204f7a94672bf0e8bfb55adc63d4941ce` |
| General-construction supplement | `2b19c8f4adb98aa6b28b803bb5191d00cc63c53a` |
| Iteration and cosheaf note | `6abcef6efd42c64266cf9b1f681ccfc1247169cc` |
| Range completion and three-point note | `67c6d5637dca6439998caff66ea06b137750ea08` |

The supplement's Corollary 6.3 contains the one-node proof equations and
atomic inequalities. Its syntax constructors are θ:U→S and ν:S→S.
The original Theorem 6.1 is already the incompleteness-transfer theorem;
the new note isolates its small hypotheses and derives the stronger
inseparability conclusion. The initial draft's incorrect external result
numbers were corrected by inspecting section and shared theorem counters,
without rebuilding unchanged notes.

## Heller 1990

The original scans of printed pp.1261 and 1265 were inspected directly.
Section 9, spanning pp.1264–1265, defines a recursion category as a
prodominical isotype with a Turing morphism and explicitly distinguishes
the earlier dominical requirement. Proposition 5.1(ii), p.1261, gives the
extra dominical implication `f×g=0 ⇒ f=0 or g=0`.

The product example was checked from these definitions, not inferred from
an unproved general closure claim. P-category equations, restriction zeros,
isotypy, and parameter-universality were verified componentwise. In
particular a pair of computations receives a pair of total compilers.
The nonzero arrows `(1,0)` and `(0,1)` show why this source is not dominical.
No formula from the defective p.1262 proof of Proposition 6.2 is used.

## Related functor results

The complete range-functor section (§13) of the older
[Lengyel2004 repair v6](https://github.com/flengyel/Categorical_Rice_Shapiro/blob/main/research/notes/lengyel2004_repair/lengyel2004_repairs_v6.tex)
was read. It attributes a different theorem to *Locally connected recursion
categories*, revised 10 October 2026. That theorem constructs source
inseparability by lifting target decision sections and then using weak
universal computation. It does not assume an already-inseparable image
pair. Its decision-lifting hypothesis is therefore not the elementary
reflection statement proved here. This earlier theorem is neither imported
nor re-proved in the new note, and this check is not a full verification
of the older repair document.

For *Six Classical Theorems in P-Recursion Categories*, only the
[author's abstract](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3177577)
was accessible. It discusses related structure-preserving functors; no
numbered theorem or detailed hypothesis is attributed on that basis.
The present note claims no priority for its elementary transport results.

## Mathematical-writing source

Fresh attempts to read the official Stanford report and bibliography page
timed out. The separate editorial report follows the provisional-review
protocol and distinguishes direct manuscript checks from unavailable fresh
verification against the governing source. Earlier source consultation is
recorded in the preceding review folders but is not presented as a new
consultation here.
