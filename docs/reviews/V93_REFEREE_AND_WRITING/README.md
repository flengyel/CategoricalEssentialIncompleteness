# Appendix C notation and the §1 copairing

The reviewer traced the earlier findings through v92 at `6c1c3a8`. The two remaining Appendix C notation changes and the type of the copairing in §1 are included in v93. An independent reader reconstructed Proposition C.1 from the paper before comparing it with the Lean statements. [Changed manuscript at the source commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/ad257d1333d01d210a2ffe45ec53707a42bba9c4/manuscript/latex) · [Mathematical review](INDEPENDENT.md)

## Proposition C.1

The ordinary index $e$ supplies the partial recursive extension $\varphi_e$. The oracle-machine index $m$ supplies its allowed domain $W_m^K$. For a morphism $v$ on a product, $m_v$ indexes its domain in the paired coding. The halting reduction uses one computable $h$ for every $n,m$: membership of $\langle h(n),m\rangle$ in $A$ depends only on the even output of the ordinary diagonal. The two idempotent domains $D_{a_0},D_{a_1}$ also impose the oracle-domain test. The weak Turing parameter of $u\pi_2$ is $r_u$. The no-lift assertion continues to cover every partial function whose summand inverse images are $A^c$ and $A$. [Arbitrary second coordinate](../../../Lean/CategoricalEssentialIncompleteness/V46OracleSeparatorLift.lean#L59) · [Universal no-lift claim](../../../Lean/CategoricalEssentialIncompleteness/V46MachineOracleTuring.lean#L154)

## The copairing in §1

The complementary restriction idempotents $c,d$ on $X$ have copairing $[c,d]:X+X\rightharpoonup X$. Hence $\operatorname{ran}(g)[c,d]$ has type $X+X\rightharpoonup X$, and $\operatorname{ran}[c,d]=c\vee d=1_X$. The preceding paragraph obtains the range of $f$ from its section. [Introduction](../../../manuscript/latex/sections/01-introduction.tex#L215)

## Verification

The revised PDF has 102 pages. All 161 labels retain their numbers, the 26 archive members agree with their sources, and the 20 Lean hyperlinks embedded in the PDF match their intended destinations. The manuscript verifier and all six axiom-parser tests passed. The WSL2 handoff’s Bash blocks passed syntax checking, both embedded Python programs parsed, and the standard-input query digest matched the earlier receipt.

The v93 Lean tree matches v92. The only four Lean files differing from the v85 tree changed in v86. Their differences are confined to documentation. No new mathematical or Lean obligation was found. The latest complete kernel receipt is for v84. The v93 WSL2 assignment runs and records a fresh replay for the tested revision before the next Palomar registration. [Comparison of Lean sources](LEAN_SOURCES.md) · [WSL2 replay instructions](../../CODEX_WSL2_CEI_V93_LEAN_HANDOFF.md)
