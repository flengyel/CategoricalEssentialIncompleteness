/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariablesRoots
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionPayload

/-! Actual numerical roots of named term/formula substitution. The first
quantifier branch retains the original body independently of recursive failure. -/

@[expose] public section
noncomputable section
local instance primitiveNamedRootsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

/-- Parameters are (name,(replacement,replacement free-variable list)). -/
def captureGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “out param value. ∃ x tail fvterm quant y body fvbody mx my,
    !pi₁Def.val x param ∧ !pi₂Def.val tail param ∧ !pi₂Def.val fvterm tail ∧
    !pi₁Def.val quant value ∧ !pi₁Def.val y quant ∧ !pi₂Def.val body quant ∧
    !occurrencesGraph.val fvbody body ∧ !memberValueGraph.val mx x fvbody ∧
    !memberValueGraph.val my y fvterm ∧
    (((mx = 0 ∨ my = 0) ∧ out = 1) ∨ (mx ≠ 0 ∧ my ≠ 0 ∧ out = 0))”

def termRootGraph (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) : 𝚺₁.Semisentence 3 :=
  let q := SyntaxPolynomial.termExpression V σ d
  let O := mapChildrenGraph originalGraph originalGraph q
  let FV := mapChildrenGraph occurrencesGraph occurrencesGraph q
  let S := mapChildrenGraph resultGraph successfulValueGraph q
  let C := constructorGraph false q
  let F := freeVarsTermRootGraph σ d
  .mkSigma “out param value. ∃ oi fi si old fv rebuilt x tail replacement tag name res,
    !O.val oi value ∧ !FV.val fi value ∧ !S.val si value ∧
    !C.val old oi ∧ !F.val fv param fi ∧ !C.val rebuilt si ∧
    !pi₁Def.val x param ∧ !pi₂Def.val tail param ∧ !pi₁Def.val replacement tail ∧
    !pi₂Def.val tag value ∧ !pi₁Def.val name value ∧
    ((tag = 0 ∧ name = x ∧ res = replacement) ∨
      (tag = 0 ∧ name ≠ x ∧ res = old) ∨ (tag ≠ 0 ∧ res = rebuilt)) ∧
    !payloadGraph.val out old fv res 1”

def formulaRootGraph (V : Carrier) (π : ℕ → Carrier) (d : ℕ) : 𝚺₁.Semisentence 3 :=
  let q := SyntaxPolynomial.formulaExpression V π d
  let O := mapChildrenGraph originalGraph originalGraph q
  let FV := mapChildrenGraph occurrencesGraph occurrencesGraph q
  let S := mapChildrenGraph resultGraph successfulValueGraph q
  let C := constructorGraph true q
  let F := freeVarsFormulaRootGraph π d
  let B := allChildrenGraph trueGraph successGraph q
  let A := allChildrenGraph trueGraph freeForGraph q
  .mkSigma “out param value. ∃ oi fi si old fv rebuilt allok allff tag quant y body x cap bodyok bodyff res ff,
    !O.val oi value ∧ !FV.val fi value ∧ !S.val si value ∧
    !C.val old oi ∧ !F.val fv param fi ∧ !C.val rebuilt si ∧
    !B.val allok value ∧ !A.val allff value ∧ !pi₂Def.val tag value ∧
    !pi₁Def.val quant value ∧ !pi₁Def.val y quant ∧ !pi₂Def.val body quant ∧
    !pi₁Def.val x param ∧ !captureGraph.val cap param value ∧
    !successGraph.val bodyok body ∧ !freeForGraph.val bodyff body ∧
    ((tag = 0 ∧
        ((allok = 1 ∧ !pairDef.val res rebuilt 1) ∨ (allok ≠ 1 ∧ res = 0)) ∧
        ((allff = 1 ∧ ff = 1) ∨ (allff ≠ 1 ∧ ff = 0))) ∨
      (tag ≠ 0 ∧ y = x ∧ !pairDef.val res old 1 ∧ ff = 1) ∨
      (tag ≠ 0 ∧ y ≠ x ∧
        ((cap = 1 ∧ bodyok = 1 ∧ !pairDef.val res rebuilt 1) ∨
          ((cap ≠ 1 ∨ bodyok ≠ 1) ∧ res = 0)) ∧
        ((cap = 1 ∧ bodyff = 1 ∧ ff = 1) ∨
          ((cap ≠ 1 ∨ bodyff ≠ 1) ∧ ff = 0)))) ∧
    !payloadGraph.val out old fv res ff”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedRootsModelDecidableEq : DecidableEq M := Classical.decEq M

def capture (param value : M) : M :=
  if member (π₁ param) (occurrences (π₂ (π₁ value))) = 0 ∨
      member (π₁ (π₁ value)) (π₂ (π₂ param)) = 0 then 1 else 0

def termRoot (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (param value : M) : M :=
  let q := SyntaxPolynomial.termExpression V σ d
  let old := constructor false q (mapChildren original original q value)
  let fv := freeVarsTermRoot σ d param (mapChildren occurrences occurrences q value)
  let rebuilt := constructor false q (mapChildren result successfulValue q value)
  let res := if π₂ value = 0 then
    if π₁ value = π₁ param then π₁ (π₂ param) else old else rebuilt
  payload old fv res 1

def formulaRoot (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param value : M) : M :=
  let q := SyntaxPolynomial.formulaExpression V π d
  let old := constructor true q (mapChildren original original q value)
  let fv := freeVarsFormulaRoot π d param (mapChildren occurrences occurrences q value)
  let rebuilt := constructor true q (mapChildren result successfulValue q value)
  let quant := π₁ value
  let body := π₂ quant
  let res := if π₂ value = 0 then
    if allChildren (fun _ => 1) success q value = 1 then ok rebuilt else 0
    else if π₁ quant = π₁ param then ok old
    else if capture param value = 1 ∧ success body = 1 then ok rebuilt else 0
  let ff := if π₂ value = 0 then
    if allChildren (fun _ => 1) freeFor q value = 1 then 1 else 0
    else if π₁ quant = π₁ param then 1
    else if capture param value = 1 ∧ freeFor body = 1 then 1 else 0
  payload old fv res ff

@[simp] theorem payloadGraph_eval_any (v : Fin 5 → M) :
    payloadGraph.val.Evalb v ↔ v 0 = payload (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0,v 1,v 2,v 3,v 4] = v := by funext i; fin_cases i <;> rfl
  simpa [hv] using payloadGraph_eval (v 0) (v 1) (v 2) (v 3) (v 4)

@[simp] theorem captureGraph_eval (out param value : M) :
    captureGraph.val.Evalb ![out,param,value] ↔ out = capture param value := by
  by_cases hx : member (π₁ param) (occurrences (π₂ (π₁ value))) = 0 <;>
  by_cases hy : member (π₁ (π₁ value)) (π₂ (π₂ param)) = 0 <;>
    simp [captureGraph,capture,hx,hy,memberValueGraph]

instance capture_defined : 𝚺₁-Function₂ (capture : M → M → M) via captureGraph := .mk fun v => by
  have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using captureGraph_eval (v 0) (v 1) (v 2)

@[simp] theorem termRootGraph_eval (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (out param value : M) :
    (termRootGraph V σ d).val.Evalb ![out,param,value] ↔ out = termRoot V σ d param value := by
  by_cases htag : π₂ value = 0 <;> by_cases hvar : π₁ value = π₁ param <;>
    simp [termRootGraph,termRoot,htag,hvar,mapChildrenGraph_eval _ _ original original,
      mapChildrenGraph_eval _ _ occurrences occurrences,mapChildrenGraph_eval _ _ result successfulValue]

private theorem choosePayload (out old fv rebuilt allok allff tag y x cap bodyok bodyff : M) :
    (∃ res ff : M,
      ((tag = 0 ∧
          ((allok = 1 ∧ res = ok rebuilt) ∨ (allok ≠ 1 ∧ res = 0)) ∧
          ((allff = 1 ∧ ff = 1) ∨ (allff ≠ 1 ∧ ff = 0))) ∨
        (tag ≠ 0 ∧ y = x ∧ res = ok old ∧ ff = 1) ∨
        (tag ≠ 0 ∧ y ≠ x ∧
          ((cap = 1 ∧ bodyok = 1 ∧ res = ok rebuilt) ∨ ((cap ≠ 1 ∨ bodyok ≠ 1) ∧ res = 0)) ∧
          ((cap = 1 ∧ bodyff = 1 ∧ ff = 1) ∨ ((cap ≠ 1 ∨ bodyff ≠ 1) ∧ ff = 0)))) ∧
      out = payload old fv res ff) ↔
      out = payload old fv
        (if tag = 0 then if allok = 1 then ok rebuilt else 0
          else if y = x then ok old else if cap = 1 ∧ bodyok = 1 then ok rebuilt else 0)
        (if tag = 0 then if allff = 1 then 1 else 0
          else if y = x then 1 else if cap = 1 ∧ bodyff = 1 then 1 else 0) := by
  by_cases htag : tag = 0
  · by_cases hok : allok = 1 <;> by_cases hff : allff = 1 <;> simp [htag,hok,hff]
  · by_cases hvar : y = x
    · simp [htag,hvar]
    · by_cases hcap : cap = 1 <;> by_cases hok : bodyok = 1 <;>
      by_cases hff : bodyff = 1 <;> simp [htag,hvar,hcap,hok,hff]

@[simp] theorem formulaRootGraph_eval (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (out param value : M) :
    (formulaRootGraph V π d).val.Evalb ![out,param,value] ↔ out = formulaRoot V π d param value := by
  simpa [formulaRootGraph,formulaRoot,ok,
    mapChildrenGraph_eval _ _ original original,mapChildrenGraph_eval _ _ occurrences occurrences,
    mapChildrenGraph_eval _ _ result successfulValue,
    allChildrenGraph_eval _ _ (fun _ : M => 1) success,
    allChildrenGraph_eval _ _ (fun _ : M => 1) freeFor] using
    choosePayload out
      (constructor true (SyntaxPolynomial.formulaExpression V π d)
        (mapChildren original original (SyntaxPolynomial.formulaExpression V π d) value))
      (freeVarsFormulaRoot π d param
        (mapChildren occurrences occurrences (SyntaxPolynomial.formulaExpression V π d) value))
      (constructor true (SyntaxPolynomial.formulaExpression V π d)
        (mapChildren result successfulValue (SyntaxPolynomial.formulaExpression V π d) value))
      (allChildren (fun _ : M => 1) success (SyntaxPolynomial.formulaExpression V π d) value)
      (allChildren (fun _ : M => 1) freeFor (SyntaxPolynomial.formulaExpression V π d) value)
      (π₂ value) (π₁ (π₁ value)) (π₁ param) (capture param value)
      (success (π₂ (π₁ value))) (freeFor (π₂ (π₁ value)))

instance termRoot_defined (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) :
    𝚺₁-Function₂ (termRoot V σ d : M → M → M) via termRootGraph V σ d := .mk fun v => by
  have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using termRootGraph_eval V σ d (v 0) (v 1) (v 2)
instance formulaRoot_defined (V : Carrier) (π : ℕ → Carrier) (d : ℕ) :
    𝚺₁-Function₂ (formulaRoot V π d : M → M → M) via formulaRootGraph V π d := .mk fun v => by
  have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using formulaRootGraph_eval V π d (v 0) (v 1) (v 2)

@[simp] theorem termRoot_original (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (param value : M) :
    original (termRoot V σ d param value) = constructor false (SyntaxPolynomial.termExpression V σ d)
      (mapChildren original original (SyntaxPolynomial.termExpression V σ d) value) := by
  simp only [termRoot,original_payload]

@[simp] theorem formulaRoot_original (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param value : M) :
    original (formulaRoot V π d param value) = constructor true (SyntaxPolynomial.formulaExpression V π d)
      (mapChildren original original (SyntaxPolynomial.formulaExpression V π d) value) := by
  simp only [formulaRoot,original_payload]

@[simp] theorem termRoot_occurrences (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (param value : M) :
    occurrences (termRoot V σ d param value) = freeVarsTermRoot σ d param
      (mapChildren occurrences occurrences (SyntaxPolynomial.termExpression V σ d) value) := by
  simp only [termRoot,occurrences_payload]

@[simp] theorem formulaRoot_occurrences (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param value : M) :
    occurrences (formulaRoot V π d param value) = freeVarsFormulaRoot π d param
      (mapChildren occurrences occurrences (SyntaxPolynomial.formulaExpression V π d) value) := by
  simp only [formulaRoot,occurrences_payload]

/-- The literal binder-equality branch uses only the original projection.
No assumption says that the recursively computed body option succeeds. -/
theorem formulaRoot_equal_binder_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ)
    (x replacement fvterm body : M) :
    result (formulaRoot V π d ⟪x,⟪replacement,fvterm⟫⟫ ⟪⟪x,body⟫,1⟫) =
      ok (constructor true (SyntaxPolynomial.formulaExpression V π d) ⟪⟪x,original body⟫,1⟫) := by
  simp [formulaRoot,SyntaxPolynomial.formulaExpression,mapChildren]

theorem formulaRoot_equal_binder_freeFor (V : Carrier) (π : ℕ → Carrier) (d : ℕ)
    (x replacement fvterm body : M) :
    freeFor (formulaRoot V π d ⟪x,⟪replacement,fvterm⟫⟫ ⟪⟪x,body⟫,1⟫) = 1 := by
  simp [formulaRoot]

end Models
open SyntacticSyntax.NatVectors

theorem capture_primrec : Primrec₂ (capture : ℕ → ℕ → ℕ) := by
  have hx := pi1_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1))
  have hy := pi1_primrec.comp (pi1_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2)))
  have hb := occurrences_primrec.comp
    (pi2_primrec.comp (pi1_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))))
  have ht := pi2_primrec.comp (pi2_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1)))
  exact Primrec.ite ((Primrec.eq.comp (member_primrec.comp hx hb) (Primrec.const 0)).or
    (Primrec.eq.comp (member_primrec.comp hy ht) (Primrec.const 0)))
    (Primrec.const 1) (Primrec.const 0)

theorem termRoot_primrec (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (termRoot V σ d : ℕ → ℕ → ℕ) := by
  let q := SyntaxPolynomial.termExpression V σ d
  have hi := (mapChildren_primrec q original original original_primrec original_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hv := (mapChildren_primrec q occurrences occurrences occurrences_primrec occurrences_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hs := (mapChildren_primrec q result successfulValue result_primrec successfulValue_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hold := (constructor_primrec false q).comp hi
  have hfv := (freeVarsTermRoot_primrec σ d).comp Primrec.fst hv
  have hrebuilt := (constructor_primrec false q).comp hs
  have htag := pi2_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hname := pi1_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hx := pi1_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1))
  have ht := pi1_primrec.comp (pi2_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1)))
  have hres := Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hname hx) ht hold) hrebuilt
  exact payload_primrec.comp (Primrec.pair hold (Primrec.pair hfv
    (Primrec.pair hres (Primrec.const 1))))

theorem formulaRoot_primrec (V : Carrier) (π : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (formulaRoot V π d : ℕ → ℕ → ℕ) := by
  let q := SyntaxPolynomial.formulaExpression V π d
  have hi := (mapChildren_primrec q original original original_primrec original_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hv := (mapChildren_primrec q occurrences occurrences occurrences_primrec occurrences_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hs := (mapChildren_primrec q result successfulValue result_primrec successfulValue_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hold := (constructor_primrec true q).comp hi
  have hfv := (freeVarsFormulaRoot_primrec π d).comp Primrec.fst hv
  have hrebuilt := (constructor_primrec true q).comp hs
  have hokold := pair_primrec.comp hold (Primrec.const 1)
  have hokrebuilt := pair_primrec.comp hrebuilt (Primrec.const 1)
  have htag := pi2_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hy := pi1_primrec.comp (pi1_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2)))
  have hx := pi1_primrec.comp (Primrec.fst : Primrec (fun p : ℕ × ℕ => p.1))
  have hbody := pi2_primrec.comp (pi1_primrec.comp (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2)))
  have hbodyok := success_primrec.comp hbody
  have hbodyff := freeFor_primrec.comp hbody
  have hallok := (allChildren_primrec q (fun _ => 1) success (Primrec.const 1) success_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hallff := (allChildren_primrec q (fun _ => 1) freeFor (Primrec.const 1) freeFor_primrec).comp
    (Primrec.snd : Primrec (fun p : ℕ × ℕ => p.2))
  have hres := Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hallok (Primrec.const 1)) hokrebuilt (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hy hx) hokold
      (Primrec.ite ((Primrec.eq.comp capture_primrec (Primrec.const 1)).and
        (Primrec.eq.comp hbodyok (Primrec.const 1))) hokrebuilt (Primrec.const 0)))
  have hff := Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hallff (Primrec.const 1)) (Primrec.const 1) (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hy hx) (Primrec.const 1)
      (Primrec.ite ((Primrec.eq.comp capture_primrec (Primrec.const 1)).and
        (Primrec.eq.comp hbodyff (Primrec.const 1))) (Primrec.const 1) (Primrec.const 0)))
  exact payload_primrec.comp (Primrec.pair hold (Primrec.pair hfv (Primrec.pair hres hff)))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
