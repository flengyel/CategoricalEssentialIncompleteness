/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertReplacement
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Named proofs from arbitrary external axiom sets

The original named Hilbert relation is reused on a finite PA Sigma-one carrier. The
surrounding axiom set is an arbitrary set of natural codes; it need not be PA
definable, computably enumerable, or sound. Axioms still have the original sentence
guard. The carrier comparison below concerns standard natural codes and makes no
assertion about nonstandard finite-carrier evaluations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller
open NamedFiniteSyntax NamedPostfixEncoding

private theorem finiteMembership_re (L:List ℕ) : REPred (fun n:ℕ => n∈L) := by
  induction L with
  | nil => exact (REPred.const False).of_eq (fun _ => by simp)
  | cons c L ih =>
    simpa only [List.mem_cons,id_eq] using
      (((Primrec.eq.comp Primrec.id (Primrec.const c)).computablePred.to_re).or ih)

/-- A PA Sigma-one carrier for the given finite numerical list. -/
def finiteCarrier (L:List ℕ) : SyntacticPredicates.Carrier :=
  .mkSigma (codeOfREPred (fun n:ℕ => n∈L)) (by simp [codeOfREPred,codeOfPartrec'])

theorem finiteCarrier_eval (L:List ℕ) (n:ℕ) :
    (finiteCarrier L).val.Evalb (M:=ℕ) ![n] ↔ n∈L :=
  codeOfREPred_spec (finiteMembership_re L)

theorem finiteCarrier_empty (n:ℕ) : ¬(finiteCarrier []).val.Evalb (M:=ℕ) ![n] := by
  rw [finiteCarrier_eval]
  simp

theorem finiteCarrier_append (L K:List ℕ) (n:ℕ) :
    (finiteCarrier (L++K)).val.Evalb (M:=ℕ) ![n] ↔
      (finiteCarrier L).val.Evalb (M:=ℕ) ![n] ∨ (finiteCarrier K).val.Evalb (M:=ℕ) ![n] := by
  simp only [finiteCarrier_eval,List.mem_append]

variable (σ π:ℕ→SyntacticPredicates.Carrier) (d:ℕ)
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula
  (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

/-- External finitary provability reuses the existing literal proof relation.
Membership witnesses are support witnesses, not additional syntax labels. -/
def FiniteAxiomProof (A:Set ℕ) (φ:Fm) : Prop :=
  ∃L:List ℕ,(∀c∈L,c∈A) ∧ SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ

namespace FiniteAxiomProof

/-- Finite-carrier transport uses the Hilbert axiom replacement. -/
theorem finite_native_mono (L K:List ℕ) (hLK:∀c∈L,c∈K) {φ:Fm}
    (h:SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) :
    SyntacticNamedHilbert.Derives σ π d (finiteCarrier K) φ := by
  apply SyntacticNamedHilbert.replace_axioms σ π d (finiteCarrier L) (finiteCarrier K) ?_ h
  intro ψ hψ hclosed
  exact .axiom ψ ((finiteCarrier_eval K _).mpr (hLK _ ((finiteCarrier_eval L _).mp hψ))) hclosed

theorem of_finite {A:Set ℕ} (L:List ℕ) (hL:∀c∈L,c∈A) {φ:Fm}
    (h:SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) :
    FiniteAxiomProof σ π d A φ := ⟨L,hL,h⟩

theorem monotone {A B:Set ℕ} (hAB:A⊆B) {φ:Fm} (h:FiniteAxiomProof σ π d A φ) :
    FiniteAxiomProof σ π d B φ := by
  obtain ⟨L,hL,hφ⟩ := h
  exact ⟨L,fun c hc => hAB (hL c hc),hφ⟩

theorem of_empty {A:Set ℕ} {φ:Fm}
    (h:SyntacticNamedHilbert.Derives σ π d (finiteCarrier []) φ) :
    FiniteAxiomProof σ π d A φ := ⟨[],fun _ hc => False.elim (List.not_mem_nil hc),h⟩

theorem empty_iff {φ:Fm} : FiniteAxiomProof σ π d ∅ φ ↔
    SyntacticNamedHilbert.Derives σ π d (finiteCarrier []) φ := by
  constructor
  · rintro ⟨L,hL,h⟩
    exact finite_native_mono σ π d L [] (fun c hc => False.elim (hL c hc)) h
  · exact of_empty σ π d

theorem axiom_of_mem {A:Set ℕ} (φ:Fm) (hφ:formulaCode φ∈A) (hclosed:φ.freeVariables=[]) :
    FiniteAxiomProof σ π d A φ := by
  refine ⟨[formulaCode φ],?_,.axiom φ ?_ hclosed⟩
  · intro c hc
    have he:c=formulaCode φ := by simpa only [List.mem_singleton] using hc
    exact he.symm ▸ hφ
  · exact (finiteCarrier_eval _ _).mpr (by simp)

/-- Two proofs have one finite support in the union of their external axiom sets. -/
theorem common_support {A B:Set ℕ} {φ ψ:Fm}
    (hφ:FiniteAxiomProof σ π d A φ) (hψ:FiniteAxiomProof σ π d B ψ) :
    ∃L:List ℕ,(∀c∈L,c∈A∪B) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) ψ := by
  obtain ⟨L,hLA,hLφ⟩ := hφ
  obtain ⟨K,hKB,hKψ⟩ := hψ
  refine ⟨L++K,?_,?_,?_⟩
  · intro c hc
    exact (List.mem_append.mp hc).elim (fun hc => Or.inl (hLA c hc)) (fun hc => Or.inr (hKB c hc))
  · exact finite_native_mono σ π d L (L++K) (fun _ hc => List.mem_append.mpr (Or.inl hc)) hLφ
  · exact finite_native_mono σ π d K (L++K) (fun _ hc => List.mem_append.mpr (Or.inr hc)) hKψ

theorem one {A:Set ℕ} (φ ψ:Fm) :
    FiniteAxiomProof σ π d A (.imp φ (.imp ψ φ)) := of_empty σ π d (.one φ ψ)

theorem two {A:Set ℕ} (φ ψ χ:Fm) :
    FiniteAxiomProof σ π d A (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))) :=
  of_empty σ π d (.two φ ψ χ)

theorem three {A:Set ℕ} (φ ψ:Fm) :
    FiniteAxiomProof σ π d A (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) :=
  of_empty σ π d (.three φ ψ)

theorem instantiation {A:Set ℕ} (x:ℕ) (φ:Fm) (t:Tm) (ψ:Fm)
    (hfree:φ.FreeFor x t) (hsub:φ.substitute x t=some ψ) :
    FiniteAxiomProof σ π d A (.imp (.all x φ) ψ) :=
  of_empty σ π d (.instantiation x φ t ψ hfree hsub)

theorem distribution {A:Set ℕ} (x:ℕ) (φ ψ:Fm) (habsent:x∉φ.freeVariables) :
    FiniteAxiomProof σ π d A (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) :=
  of_empty σ π d (.distribution x φ ψ habsent)

theorem reflexivity {A:Set ℕ} (t:Tm) : FiniteAxiomProof σ π d A (.equal t t) :=
  of_empty σ π d (.reflexivity t)

theorem equality {A:Set ℕ} (x:ℕ) (φ:Fm) (u t:Tm) (ψ χ:Fm)
    (hu:φ.FreeFor x u) (ht:φ.FreeFor x t)
    (hsubu:φ.substitute x u=some ψ) (hsubt:φ.substitute x t=some χ) :
    FiniteAxiomProof σ π d A (.imp (.equal u t) (.imp ψ χ)) :=
  of_empty σ π d (.equality x φ u t ψ χ hu ht hsubu hsubt)

theorem generalization {A:Set ℕ} (x:ℕ) {φ:Fm} (h:FiniteAxiomProof σ π d A φ) :
    FiniteAxiomProof σ π d A (.all x φ) := by
  obtain ⟨L,hL,hφ⟩ := h
  exact ⟨L,hL,.generalization x hφ⟩

/-- The antecedent and implication remain ordered as in the original calculus. -/
theorem modusPonens {A:Set ℕ} {φ ψ:Fm}
    (hφ:FiniteAxiomProof σ π d A φ) (himp:FiniteAxiomProof σ π d A (.imp φ ψ)) :
    FiniteAxiomProof σ π d A ψ := by
  obtain ⟨L,hL,hφ,himp⟩ := common_support σ π d hφ himp
  refine ⟨L,?_,.modusPonens hφ himp⟩
  intro c hc
  exact (hL c hc).elim id id

/-- Each finite list needs at most one proof for each closed literal code.
Code injectivity is proved for this presentation, not inferred semantically. -/
private theorem finite_family_support {A:Set ℕ} (L:List ℕ)
    (h:∀ψ:Fm,formulaCode ψ∈L → ψ.freeVariables=[] → FiniteAxiomProof σ π d A ψ) :
    ∃K:List ℕ,(∀c∈K,c∈A) ∧
      ∀ψ:Fm,formulaCode ψ∈L → ψ.freeVariables=[] →
        SyntacticNamedHilbert.Derives σ π d (finiteCarrier K) ψ := by
  classical
  induction L with
  | nil =>
    refine ⟨[],fun _ hc => False.elim (List.not_mem_nil hc),?_⟩
    intro ψ hψ _
    exact False.elim (List.not_mem_nil hψ)
  | cons c L ih =>
    obtain ⟨K,hKA,hK⟩ := ih (fun ψ hψ hclosed => h ψ (List.mem_cons_of_mem c hψ) hclosed)
    by_cases hc:∃ψ:Fm,formulaCode ψ=c ∧ ψ.freeVariables=[]
    · obtain ⟨ψ,hcode,hclosed⟩ := hc
      obtain ⟨H,hHA,hHψ⟩ := h ψ (List.mem_cons.mpr (Or.inl hcode)) hclosed
      refine ⟨K++H,?_,?_⟩
      · intro z hz
        exact (List.mem_append.mp hz).elim (hKA z) (hHA z)
      · intro χ hχ hχclosed
        rcases List.mem_cons.mp hχ with hχcode | hχ
        · have he:χ=ψ := NamedPostfixEncoding.formulaCode_injective (hχcode.trans hcode.symm)
          subst χ
          exact finite_native_mono σ π d H (K++H) (fun _ hz => List.mem_append.mpr (Or.inr hz)) hHψ
        · exact finite_native_mono σ π d K (K++H) (fun _ hz => List.mem_append.mpr (Or.inl hz))
            (hK χ hχ hχclosed)
    · refine ⟨K,hKA,?_⟩
      intro χ hχ hclosed
      rcases List.mem_cons.mp hχ with hχcode | hχ
      · exact False.elim (hc ⟨χ,hχcode,hclosed⟩)
      · exact hK χ hχ hclosed

/-- External axiom replacement is implemented by a common finite target support followed
by the axiom-replacement theorem. -/
theorem replace_axioms {A B:Set ℕ}
    (hAxiom:∀ψ:Fm,formulaCode ψ∈A → ψ.freeVariables=[] → FiniteAxiomProof σ π d B ψ)
    {φ:Fm} (hφ:FiniteAxiomProof σ π d A φ) : FiniteAxiomProof σ π d B φ := by
  obtain ⟨L,hLA,hLφ⟩ := hφ
  obtain ⟨K,hKB,hK⟩ := finite_family_support σ π d L
    (fun ψ hψ hclosed => hAxiom ψ (hLA _ hψ) hclosed)
  refine ⟨K,hKB,?_⟩
  apply SyntacticNamedHilbert.replace_axioms σ π d (finiteCarrier L) (finiteCarrier K) ?_ hLφ
  intro ψ hψ hclosed
  exact hK ψ ((finiteCarrier_eval L _).mp hψ) hclosed

/-- Non-sentence and non-formula codes in an external set create no axioms. The comparison
is by literal formula code, and transfers proofs. -/
theorem congr_axioms {A B:Set ℕ}
    (h:∀ψ:Fm,ψ.freeVariables=[] → (formulaCode ψ∈A ↔ formulaCode ψ∈B)) (φ:Fm) :
    FiniteAxiomProof σ π d A φ ↔ FiniteAxiomProof σ π d B φ := by
  constructor
  · exact replace_axioms σ π d
      (fun ψ hψ hclosed => axiom_of_mem σ π d ψ ((h ψ hclosed).mp hψ) hclosed)
  · exact replace_axioms σ π d
      (fun ψ hψ hclosed => axiom_of_mem σ π d ψ ((h ψ hclosed).mpr hψ) hclosed)

/-- Support may be chosen entirely among closed literal axioms. The additional witnesses
describe support membership, not syntax labels. -/
theorem closed_support {A:Set ℕ} {φ:Fm} (h:FiniteAxiomProof σ π d A φ) :
    ∃L:List ℕ,(∀c∈L,c∈A) ∧ (∀c∈L,∃ψ:Fm,formulaCode ψ=c ∧ ψ.freeVariables=[]) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ := by
  let B:Set ℕ := {c | c∈A ∧ ∃ψ:Fm,formulaCode ψ=c ∧ ψ.freeVariables=[]}
  have hB:FiniteAxiomProof σ π d B φ := replace_axioms σ π d (A:=A) (B:=B)
    (fun ψ hψ hclosed => axiom_of_mem σ π d ψ ⟨hψ,ψ,rfl,hclosed⟩ hclosed) h
  obtain ⟨L,hL,hφ⟩ := hB
  exact ⟨L,fun c hc => (hL c hc).1,fun c hc => (hL c hc).2,hφ⟩

/-- Finiteness extraction from an existing Hilbert proof retains its sentence-axiom filter
and every substitution/generalization/MP premise. -/
theorem of_native (Γ:SyntacticPredicates.Carrier) {φ:Fm}
    (h:SyntacticNamedHilbert.Derives σ π d Γ φ) :
    FiniteAxiomProof σ π d {c:ℕ | Γ.val.Evalb (M:=ℕ) ![c]} φ := by
  induction h with
  | «axiom» ψ hψ hclosed => exact axiom_of_mem σ π d ψ hψ hclosed
  | one φ ψ => exact one σ π d φ ψ
  | two φ ψ χ => exact two σ π d φ ψ χ
  | three φ ψ => exact three σ π d φ ψ
  | instantiation x φ t ψ hfree hsub => exact instantiation σ π d x φ t ψ hfree hsub
  | distribution x φ ψ habsent => exact distribution σ π d x φ ψ habsent
  | reflexivity t => exact reflexivity σ π d t
  | equality x φ u t ψ χ hu ht hsubu hsubt => exact equality σ π d x φ u t ψ χ hu ht hsubu hsubt
  | generalization x _ ih => exact generalization σ π d x ih
  | modusPonens _ _ ihφ ihimp => exact modusPonens σ π d ihφ ihimp

theorem native_finite_support (Γ:SyntacticPredicates.Carrier) {φ:Fm}
    (h:SyntacticNamedHilbert.Derives σ π d Γ φ) :
    ∃L:List ℕ,(∀c∈L,Γ.val.Evalb (M:=ℕ) ![c]) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ := of_native σ π d Γ h

theorem to_native (Γ:SyntacticPredicates.Carrier) {A:Set ℕ}
    (hA:∀ψ:Fm,formulaCode ψ∈A → ψ.freeVariables=[] → Γ.val.Evalb (M:=ℕ) ![formulaCode ψ])
    {φ:Fm} (hφ:FiniteAxiomProof σ π d A φ) : SyntacticNamedHilbert.Derives σ π d Γ φ := by
  obtain ⟨L,hL,hφ⟩ := hφ
  apply SyntacticNamedHilbert.replace_axioms σ π d (finiteCarrier L) Γ ?_ hφ
  intro ψ hψ hclosed
  exact .axiom ψ (hA ψ (hL _ ((finiteCarrier_eval L _).mp hψ)) hclosed) hclosed

theorem native_iff (Γ:SyntacticPredicates.Carrier) (φ:Fm) :
    SyntacticNamedHilbert.Derives σ π d Γ φ ↔
      FiniteAxiomProof σ π d {c:ℕ | Γ.val.Evalb (M:=ℕ) ![c]} φ :=
  ⟨of_native σ π d Γ,to_native σ π d Γ (fun _ h _ => h)⟩

end FiniteAxiomProof
end CategoricalEssentialIncompleteness.V46.Miller
