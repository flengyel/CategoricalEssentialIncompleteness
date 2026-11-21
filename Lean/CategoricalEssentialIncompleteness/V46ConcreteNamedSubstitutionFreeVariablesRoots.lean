/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionGather
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversalTyped

/-!
Numerical free-variable root functions on the manuscript's named charts. The traversal
keeps repeated occurrences in left-to-right order.
-/

@[expose] public section
noncomputable section
local instance primitiveNamedFreeVariablesRootsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

/-- The four nonquantified alternatives of the literal formula polynomial. -/
def formulaLeft (π : ℕ → Carrier) (d : ℕ) : RawPolynomial :=
  .sum (.sum (.sum (SyntaxPolynomial.power .term 2)
    (SyntaxPolynomial.constructors π d)) .formula) (SyntaxPolynomial.power .formula 2)

def freeVarsTermRootGraph (σ : ℕ → Carrier) (d : ℕ) : 𝚺₁.Semisentence 3 :=
  let A := gatherGraph (SyntaxPolynomial.constructors σ d)
  .mkSigma “out param value. ∃ tag payload, !pi₁Def.val payload value ∧ !pi₂Def.val tag value ∧
    ((tag = 0 ∧ !adjoinDef.val out payload 0) ∨ (tag ≠ 0 ∧ !A.val out payload))”

def freeVarsFormulaRootGraph (π : ℕ → Carrier) (d : ℕ) : 𝚺₁.Semisentence 3 :=
  let A := gatherGraph (formulaLeft π d)
  .mkSigma “out param value. ∃ tag payload name body, !pi₁Def.val payload value ∧
    !pi₂Def.val tag value ∧ !pi₁Def.val name payload ∧ !pi₂Def.val body payload ∧
    ((tag = 0 ∧ !A.val out payload) ∨ (tag ≠ 0 ∧ !deleteValueGraph.val out name body))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedFreeVariablesRootsModelDecidableEq : DecidableEq M := Classical.decEq M

def freeVarsTermRoot (σ : ℕ → Carrier) (d : ℕ) (_param value : M) : M :=
  if π₂ value = 0 then adjoin (π₁ value) 0 else
    gather (SyntaxPolynomial.constructors σ d) (π₁ value)

def freeVarsFormulaRoot (π : ℕ → Carrier) (d : ℕ) (_param value : M) : M :=
  if π₂ value = 0 then gather (formulaLeft π d) (π₁ value) else
    delete (π₁ (π₁ value)) (π₂ (π₁ value))

@[simp] theorem freeVarsTermRootGraph_eval (σ : ℕ → Carrier) (d : ℕ) (out param value : M) :
    (freeVarsTermRootGraph σ d).val.Evalb ![out,param,value] ↔
      out = freeVarsTermRoot σ d param value := by
  by_cases h : π₂ value = 0 <;> simp [freeVarsTermRootGraph, freeVarsTermRoot, h]

@[simp] theorem freeVarsFormulaRootGraph_eval (π : ℕ → Carrier) (d : ℕ) (out param value : M) :
    (freeVarsFormulaRootGraph π d).val.Evalb ![out,param,value] ↔
      out = freeVarsFormulaRoot π d param value := by
  by_cases h : π₂ value = 0 <;> simp [freeVarsFormulaRootGraph, freeVarsFormulaRoot, h,
    deleteValueGraph]

instance freeVarsTermRoot_defined (σ : ℕ → Carrier) (d : ℕ) :
    𝚺₁-Function₂ (freeVarsTermRoot σ d : M → M → M) via freeVarsTermRootGraph σ d :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
    simpa [hv] using freeVarsTermRootGraph_eval σ d (v 0) (v 1) (v 2)
instance freeVarsFormulaRoot_defined (π : ℕ → Carrier) (d : ℕ) :
    𝚺₁-Function₂ (freeVarsFormulaRoot π d : M → M → M) via freeVarsFormulaRootGraph π d :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
    simpa [hv] using freeVarsFormulaRootGraph_eval π d (v 0) (v 1) (v 2)

@[simp] theorem freeVarsTermRoot_variable (σ : ℕ → Carrier) (d : ℕ) (param x : M) :
    freeVarsTermRoot σ d param ⟪x,0⟫ = adjoin x 0 := by simp [freeVarsTermRoot]
@[simp] theorem freeVarsTermRoot_function (σ : ℕ → Carrier) (d : ℕ) (param u : M) :
    freeVarsTermRoot σ d param ⟪u,1⟫ = gather (SyntaxPolynomial.constructors σ d) u := by
  simp [freeVarsTermRoot]
@[simp] theorem freeVarsFormulaRoot_nonquantified (π : ℕ → Carrier) (d : ℕ) (param u : M) :
    freeVarsFormulaRoot π d param ⟪u,0⟫ = gather (formulaLeft π d) u := by
  simp [freeVarsFormulaRoot]
@[simp] theorem freeVarsFormulaRoot_quantifier (π : ℕ → Carrier) (d : ℕ) (param y body : M) :
    freeVarsFormulaRoot π d param ⟪⟪y,body⟫,1⟫ = delete y body := by
  simp [freeVarsFormulaRoot]

/-- Ordered collection preserves the selected variable list carrier;
coefficient membership remains a positive input assertion. -/
theorem gather_carrier (V : Carrier) (q : RawPolynomial) (u : M)
    (hu : (rawCarrier (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V) q).val.Evalb ![u]) :
    (SyntacticLists.listCarrier V).val.Evalb ![gather q u] := by
  induction q generalizing u with
  | term => exact hu
  | formula => exact hu
  | coefficient _ => exact SyntacticLists.listCarrier_nil V
  | unit => exact SyntacticLists.listCarrier_nil V
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ :=
        (rawCarrier_product_eval (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V) a b u).mp hu
      simpa [gather] using append_carrier V (gather a x) (gather b y) (ia x hx) (ib y hy)
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V) a b u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · simpa [gather] using ia x hx
      · simpa [gather] using ib y hy

theorem freeVarsTermRoot_carrier (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (param u : M)
    (hu : (rawCarrier (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u]) :
    (SyntacticLists.listCarrier V).val.Evalb ![freeVarsTermRoot σ d param u] := by
  rcases (rawCarrier_sum_eval (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
    (.coefficient V) (SyntaxPolynomial.constructors σ d) u).mp hu with
    ⟨x,rfl,hx⟩ | ⟨v,rfl,hv⟩
  · rw [freeVarsTermRoot_variable]
    exact (SyntacticLists.listCarrier_cons V x 0).mpr ⟨hx,SyntacticLists.listCarrier_nil V⟩
  · rw [freeVarsTermRoot_function]
    exact gather_carrier V _ v hv

theorem freeVarsFormulaRoot_carrier (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param u : M)
    (hu : (rawCarrier (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u]) :
    (SyntacticLists.listCarrier V).val.Evalb ![freeVarsFormulaRoot π d param u] := by
  rcases (rawCarrier_sum_eval (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
    (formulaLeft π d) (.product (.coefficient V) .formula) u).mp hu with
    ⟨v,rfl,hv⟩ | ⟨v,rfl,hv⟩
  · rw [freeVarsFormulaRoot_nonquantified]
    exact gather_carrier V _ v hv
  · obtain ⟨y,body,rfl,_,hb⟩ :=
      (rawCarrier_product_eval (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
        (.coefficient V) .formula v).mp hv
    rw [freeVarsFormulaRoot_quantifier]
    exact delete_carrier V y body hb

end Models

open SyntacticSyntax.NatVectors

theorem freeVarsTermRoot_primrec (σ : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (freeVarsTermRoot σ d : ℕ → ℕ → ℕ) :=
  Primrec.ite (Primrec.eq.comp (pi2_primrec.comp Primrec.snd) (Primrec.const 0))
    (adjoin_primrec.comp (pi1_primrec.comp Primrec.snd) (Primrec.const 0))
    ((gather_primrec _).comp (pi1_primrec.comp Primrec.snd))

theorem freeVarsFormulaRoot_primrec (π : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (freeVarsFormulaRoot π d : ℕ → ℕ → ℕ) :=
  Primrec.ite (Primrec.eq.comp (pi2_primrec.comp Primrec.snd) (Primrec.const 0))
    ((gather_primrec _).comp (pi1_primrec.comp Primrec.snd))
    (delete_primrec.comp (pi1_primrec.comp (pi1_primrec.comp Primrec.snd))
      (pi2_primrec.comp (pi1_primrec.comp Primrec.snd)))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
