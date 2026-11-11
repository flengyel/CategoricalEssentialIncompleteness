/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRoots
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! Positive Sigma-one payload invariants. The formula flag/result relation
is proved for the actual numerical roots before the traversal invariant is
instantiated; no validity or recursive result is supplied as an input field. -/

@[expose] public section
noncomputable section
local instance primitiveNamedCarriersDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def termPayloadCarrier : Carrier :=
  let Tm := Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let L := SyntacticLists.listCarrier V
  .mkSigma “value. ∃ old fv res, !payloadGraph.val value old fv res 1 ∧
    !Tm.val old ∧ !L.val fv ∧ !Tm.val res”

def formulaPayloadCarrier : Carrier :=
  let Fm := Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let L := SyntacticLists.listCarrier V
  .mkSigma “value. ∃ old fv res ff, !payloadGraph.val value old fv res ff ∧
    !Fm.val old ∧ !L.val fv ∧
    ((res = 0 ∧ ff = 0) ∨ ∃ substituted, !Fm.val substituted ∧
      !pairDef.val res substituted 1 ∧ ff = 1)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedCarriersModelDecidableEq : DecidableEq M := Classical.decEq M

@[simp] theorem payload_inj (old fv res ff old' fv' res' ff' : M) :
    payload old fv res ff = payload old' fv' res' ff' ↔
      old = old' ∧ fv = fv' ∧ res = res' ∧ ff = ff' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg original h,by simpa using congrArg occurrences h,
      by simpa using congrArg result h,by simpa using congrArg freeFor h⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

@[simp] theorem termPayloadCarrier_payload (old fv res ff : M) :
    (termPayloadCarrier V σ π d).val.Evalb ![payload old fv res ff] ↔
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![old] ∧
      (SyntacticLists.listCarrier V).val.Evalb ![fv] ∧
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![res] ∧ ff = 1 := by
  simp [termPayloadCarrier]
  tauto

@[simp] theorem formulaPayloadCarrier_payload (old fv res ff : M) :
    (formulaPayloadCarrier V σ π d).val.Evalb ![payload old fv res ff] ↔
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![old] ∧
      (SyntacticLists.listCarrier V).val.Evalb ![fv] ∧
      ((res = 0 ∧ ff = 0) ∨ ∃ substituted : M,
        (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![substituted] ∧
          res = ok substituted ∧ ff = 1) := by
  simp [formulaPayloadCarrier,ok]

theorem payload_decomposition (value : M) :
    value = payload (original value) (occurrences value) (result value) (freeFor value) := by
  simp [payload,original,occurrences,result,freeFor,pair_unpair]

theorem termPayload_original (value : M)
    (h : (termPayloadCarrier V σ π d).val.Evalb ![value]) :
    (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![original value] := by
  simp [termPayloadCarrier] at h
  obtain ⟨old,fv,res,hp,ho,_,_⟩ := h
  subst value
  simpa using ho

theorem termPayload_occurrences (value : M)
    (h : (termPayloadCarrier V σ π d).val.Evalb ![value]) :
    (SyntacticLists.listCarrier V).val.Evalb ![occurrences value] := by
  simp [termPayloadCarrier] at h
  obtain ⟨old,fv,res,hp,_,hl,_⟩ := h
  subst value
  simpa using hl

theorem termPayload_result (value : M)
    (h : (termPayloadCarrier V σ π d).val.Evalb ![value]) :
    (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![result value] := by
  simp [termPayloadCarrier] at h
  obtain ⟨old,fv,res,hp,_,_,hr⟩ := h
  subst value
  simpa using hr

theorem formulaPayload_original (value : M)
    (h : (formulaPayloadCarrier V σ π d).val.Evalb ![value]) :
    (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![original value] := by
  simp [formulaPayloadCarrier] at h
  obtain ⟨old,fv,res,ff,hp,ho,_,_⟩ := h
  subst value
  simpa using ho

theorem formulaPayload_occurrences (value : M)
    (h : (formulaPayloadCarrier V σ π d).val.Evalb ![value]) :
    (SyntacticLists.listCarrier V).val.Evalb ![occurrences value] := by
  simp [formulaPayloadCarrier] at h
  obtain ⟨old,fv,res,ff,hp,_,hl,_⟩ := h
  subst value
  simpa using hl

theorem formulaPayload_success (value : M)
    (h : (formulaPayloadCarrier V σ π d).val.Evalb ![value]) :
    freeFor value = success value := by
  simp [formulaPayloadCarrier] at h
  obtain ⟨old,fv,res,ff,hp,_,_,hr⟩ := h
  subst value
  rcases hr with ⟨rfl,rfl⟩ | ⟨new,_,rfl,rfl⟩ <;> simp [success,pi₂_zero]

theorem formulaPayload_successfulValue (value : M)
    (h : (formulaPayloadCarrier V σ π d).val.Evalb ![value]) (hs : success value = 1) :
    (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![successfulValue value] := by
  simp [formulaPayloadCarrier] at h
  obtain ⟨old,fv,res,ff,hp,_,_,hr⟩ := h
  subst value
  rcases hr with ⟨rfl,rfl⟩ | ⟨new,hn,rfl,rfl⟩
  · simp [success,pi₂_zero] at hs
  · simpa [successfulValue,ok] using hn

/-- The independently computed child flags agree with the option tags
on the positive payload carrier constructed above. -/
theorem allChildren_flags (q : RawPolynomial) (u : M)
    (hu : (rawCarrier (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) q).val.Evalb ![u]) :
    allChildren (fun _ => 1) freeFor q u = allChildren (fun _ => 1) success q u := by
  induction q generalizing u with
  | term => rfl
  | formula => exact formulaPayload_success V σ π d u hu
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ :=
        (rawCarrier_product_eval (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) a b u).mp hu
      simp [allChildren,ia x hx,ib y hy]
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) a b u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · simpa [allChildren] using ia x hx
      · simpa [allChildren] using ib y hy

theorem originalMap_carrier (q : RawPolynomial) (u : M)
    (hu : (rawCarrier (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) q).val.Evalb ![u]) :
    (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)) q).val.Evalb
      ![mapChildren original original q u] :=
  rawCarrier_mapChildren q original original (termPayload_original V σ π d)
    (formulaPayload_original V σ π d) u hu

theorem occurrencesMap_carrier (q : RawPolynomial) (u : M)
    (hu : (rawCarrier (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) q).val.Evalb ![u]) :
    (rawCarrier (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V) q).val.Evalb
      ![mapChildren occurrences occurrences q u] :=
  rawCarrier_mapChildren q occurrences occurrences (termPayload_occurrences V σ π d)
    (formulaPayload_occurrences V σ π d) u hu

/-- Successful formula leaves expose valid formula values. The hypothesis
is the numerical conjunction computed by allChildren, rather than an assumed
complement of a Sigma-one carrier. -/
theorem successfulMap_carrier (q : RawPolynomial) (u : M)
    (hu : (rawCarrier (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) q).val.Evalb ![u])
    (hs : allChildren (fun _ => 1) success q u = 1) :
    (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)) q).val.Evalb
      ![mapChildren result successfulValue q u] := by
  induction q generalizing u with
  | term => exact termPayload_result V σ π d u hu
  | formula => exact formulaPayload_successfulValue V σ π d u hu hs
  | coefficient _ => exact hu
  | unit => simp [mapChildren,rawCarrier]
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ :=
        (rawCarrier_product_eval (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) a b u).mp hu
      have hab : allChildren (fun _ : M => 1) success a x = 1 ∧
          allChildren (fun _ : M => 1) success b y = 1 := by
        by_cases h : allChildren (fun _ : M => 1) success a x = 1 ∧
          allChildren (fun _ : M => 1) success b y = 1
        · exact h
        · simp [allChildren,h] at hs
      have hp := (rawCarrier_product_eval
        (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
        (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)) a b
        ⟪mapChildren result successfulValue a x,mapChildren result successfulValue b y⟫).mpr
          ⟨_,_,rfl,ia x hx hab.1,ib y hy hab.2⟩
      simpa [mapChildren] using hp
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d) a b u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · have ha : allChildren (fun _ : M => 1) success a x = 1 := by simpa [allChildren] using hs
        exact (rawCarrier_sum_eval _ _ a b _).mpr
          (Or.inl ⟨_,by simp [mapChildren],ia x hx ha⟩)
      · have hb : allChildren (fun _ : M => 1) success b y = 1 := by simpa [allChildren] using hs
        exact (rawCarrier_sum_eval _ _ a b _).mpr
          (Or.inr ⟨_,by simp [mapChildren],ib y hy hb⟩)

/-- No formula positions occur in the literal term-power expression. -/
theorem termPower_allChildren (n : ℕ) (g : M → M) (u : M) :
    allChildren (fun _ => 1) g (SyntaxPolynomial.power .term n) u = 1 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp [SyntaxPolynomial.power,allChildren,ih]

theorem constructors_allChildren (R : ℕ → Carrier) (N : ℕ) (g : M → M) (u : M) :
    allChildren (fun _ => 1) g (SyntaxPolynomial.constructors R N) u = 1 := by
  induction N generalizing u with
  | zero => simp [SyntaxPolynomial.constructors,allChildren,termPower_allChildren]
  | succ N ih =>
      by_cases ht : π₂ u = 0 <;>
        simp [SyntaxPolynomial.constructors,allChildren,ht,ih,termPower_allChildren]

theorem termExpression_allChildren (g : M → M) (u : M) :
    allChildren (fun _ => 1) g (SyntaxPolynomial.termExpression V σ d) u = 1 := by
  by_cases ht : π₂ u = 0 <;>
    simp [SyntaxPolynomial.termExpression,allChildren,ht,constructors_allChildren]

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
