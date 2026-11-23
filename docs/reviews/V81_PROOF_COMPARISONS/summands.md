# The join of the two summand domains

**Finding.** The assertion in `manuscript/latex/sections/03-sections-and-inseparability.tex:9–17` at `986dee4d54d202a452009146cc29d19a544b0000` holds with restriction zeros and the displayed binary restriction coproduct. The two summand domains have the identity as their least upper bound even when other binary joins have not been assumed. The manuscript's proof closes this point. In the setting of Theorem 3.1, the existing Lean declaration also applies directly, because the assumed ranges and coproducts give all binary joins. The pair-specific argument below identifies the additional Lean statement needed to certify the unnumbered observation in isolation.

## Independent derivation

In a restriction category, take objects $Y,Z$, a coproduct $W=Y+Z$ with total injections $j_0:Y\to W$, $j_1:Z\to W$, and restriction zeros. Write $e_0=1_Y+0_Z$ and $e_1=0_Y+1_Z$, both endomorphisms of $W$. As copairings, their two components are $(j_0,0_{Z,W})$ and $(0_{Y,W},j_1)$ respectively. In particular $e_0j_0=j_0$, $e_0j_1=0_{Z,W}$, $e_1j_0=0_{Y,W}$, $e_1j_1=j_1$. The restriction of either $e_k$ is $e_k$ (restriction commutes with the sum of arrows for total coproduct injections). Thus they lie in $\operatorname{Idem}(W)$, where meet is composition. The two restrictions commute; the composite vanishes after both injections by the four component equations and absorption by zero. Joint epimorphy gives $e_0\wedge e_1=0_W$.

The identity $1_W$ bounds both $e_i$. If $r\in\operatorname{Idem}(W)$ is any upper bound, then $re_0=e_0$ and $re_1=e_1$. For $i=0,1$, $rj_i=r(e_i j_i)=(re_i)j_i=e_i j_i=j_i$. Since $1_Wj_i=j_i$, the coproduct's universal property gives $r=1_W$. This proves that $1_W$ is the least upper bound, and in fact the unique upper bound. Writing $e_0\vee e_1=1_W$ therefore agrees with the convention for partial existence of joins in `manuscript/latex/sections/02-categorical-preliminaries.tex:28–30`. The proof also works when $Y$, $Z$, or $W$ is a zero object.

## Lean source and exact type

Import `CategoricalEssentialIncompleteness.RestrictionRanges`. Its two public imports are `CategoricalEssentialIncompleteness.RestrictionIdempotents` and `PCats.Coproducts` (lines 8–9). The source namespaces are `CategoricalEssentialIncompleteness.LocalConnectedness`, `CategoryTheory.CoprodStruct`, and `CategoryTheory.HasCoproducts`. Lean's `f ≫ g` applies $f$ first. Thus $re_i=e_i$ reads `(summandᵢ Y Z).hom ≫ r.hom = (summandᵢ Y Z).hom`.

| Ingredient | Source in the pinned checkout |
|---|---|
| Chosen coproduct and injection types; equality of maps out of it can be checked on both injections | `Lean/PCats/Coproducts.lean:48–53,196–203`. The `omit` at line 196 (on the line immediately preceding the docstring for `hom_ext`) removes any need for P-category or product hypotheses. |
| Restriction of a sum; the two actual idempotents and their four injection equations | `Lean/CategoricalEssentialIncompleteness/RestrictionRanges.lean:65–90,123–143`. |
| Disjointness for the pair, without ranges or global joins | `Lean/CategoricalEssentialIncompleteness/RestrictionRanges.lean:145–148` (`summands_disjoint`). |
| Restriction order, identity at top, formulation of pair-specific leastness | `Lean/CategoricalEssentialIncompleteness/RestrictionIdempotents.lean:56–89,160–165`. In `PairComplementary.cover` the upper bound is arbitrary; `le_top` already supplies both inequalities into the identity. |
| Result when the ambient category has ranges and coproducts | `Lean/CategoricalEssentialIncompleteness/RestrictionRanges.lean:99–116` supplies `joinsOfRanges`. Lines 150–165 give `summands_complementary` on the induced or any chosen binary joins. |

The following standalone candidate spells out the general statement and its proof using these declarations. It reproduces the two injection calculations from the existing source with an arbitrary upper bound in place of a preselected join. It was inspected against the source and has **not** been elaborated or replayed.

```lean
import CategoricalEssentialIncompleteness.RestrictionRanges

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

universe v u

example {C : Type u} [Category.{v} C] [RestrictionCategory C]
    [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]
    [CategoryTheory.Limits.HasZeroMorphisms C] [RestrictionZero C] (Y Z : C) :
    PairComplementary (summand0 Y Z) (summand1 Y Z) := by
  refine ⟨summands_disjoint Y Z, ?_⟩
  intro r h₀ h₁
  change (𝟙 (coprod Y Z)) ≫ r.hom = 𝟙 _
  rw [Category.id_comp]
  apply CategoryTheory.HasCoproducts.hom_ext
  · have h := congrArg (fun k => i0 Y Z ≫ k) (Idem.le_def.mp h₀)
    simpa only [← Category.assoc, i0_summand0, Category.comp_id] using h
  · have h := congrArg (fun k => i1 Y Z ≫ k) (Idem.le_def.mp h₁)
    simpa only [← Category.assoc, i1_summand1, Category.comp_id] using h

end CategoricalEssentialIncompleteness.LocalConnectedness
```

**Verification status.** The mathematical statement is settled at the printed hypotheses; no manuscript correction is needed. The existing `summands_complementary` covers the theorem's ambient hypotheses. For the statement independent of ranges and global joins, the checked ingredients and the required application are specified above. This source inspection did not identify an already assembled declaration at the weaker type or generate kernel evidence for the candidate. The latter requires a host check if claimed as a formalized endpoint.
