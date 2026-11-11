/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser
public import CategoricalEssentialIncompleteness.V46SyntacticLists
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! Numeric named-variable list operations, with PA equations and actual
standard primitive-recursion certificates. Every repeated variable is retained
until an explicitly named deletion. No predicate membership is decided. -/

@[expose] public section
noncomputable section
local instance primitiveNamedListsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution

/-- The Boolean values are the literal numerals zero and one. -/
def memberBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “o x. o = 0”
  adjoin := .mkSigma “o y ys ih x. (y = x ∧ o = 1) ∨ (y ≠ x ∧ o = ih)”

def deleteBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “o x. o = 0”
  adjoin := .mkSigma “o y ys ih x. (y = x ∧ o = ih) ∨ (y ≠ x ∧ !adjoinDef.val o y ih)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedListsModelDecidableEq : DecidableEq M := Classical.decEq M

def memberConstruction : VecRec.Construction M memberBlueprint where
  nil _ := 0
  adjoin p y _ ih := if y = p 0 then 1 else ih
  nil_defined := .mk fun v => by simp [memberBlueprint]
  adjoin_defined := .mk fun v => by
    by_cases h : v 1 = v 4 <;> simp [memberBlueprint, h]

def deleteConstruction : VecRec.Construction M deleteBlueprint where
  nil _ := 0
  adjoin p y _ ih := if y = p 0 then ih else adjoin y ih
  nil_defined := .mk fun v => by simp [deleteBlueprint]
  adjoin_defined := .mk fun v => by
    by_cases h : v 1 = v 4 <;> simp [deleteBlueprint, h]

def member (x list : M) : M := memberConstruction.result ![x] list

def delete (x list : M) : M := deleteConstruction.result ![x] list

@[simp] theorem member_nil (x : M) : member x 0 = 0 := by
  simp [member, memberConstruction]
@[simp] theorem member_adjoin (x y list : M) :
    member x (adjoin y list) = if y = x then 1 else member x list := by
  simp [member, memberConstruction]
@[simp] theorem delete_nil (x : M) : delete x 0 = 0 := by
  simp [delete, deleteConstruction]
@[simp] theorem delete_adjoin (x y list : M) :
    delete x (adjoin y list) = if y = x then delete x list else adjoin y (delete x list) := by
  simp [delete, deleteConstruction]
end Models

/-- Variable order: output, list, variable. -/
def memberGraph : 𝚺₁.Semisentence 3 := memberBlueprint.resultDef
/-- Variable order: output, list, variable. -/
def deleteGraph : 𝚺₁.Semisentence 3 := deleteBlueprint.resultDef

def memberValueGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “out x list. !memberGraph.val out list x”
def deleteValueGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “out x list. !deleteGraph.val out list x”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem memberGraph_eval (out list x : M) :
    memberGraph.val.Evalb ![out,list,x] ↔ out = member x list := by
  simpa [memberGraph, member, Matrix.constant_eq_singleton] using
    (memberConstruction (M := M)).eval_resultDef ![out,list,x]
@[simp] theorem deleteGraph_eval (out list x : M) :
    deleteGraph.val.Evalb ![out,list,x] ↔ out = delete x list := by
  simpa [deleteGraph, delete, Matrix.constant_eq_singleton] using
    (deleteConstruction (M := M)).eval_resultDef ![out,list,x]

instance member_defined : 𝚺₁-Function₂ (member : M → M → M) via memberValueGraph :=
  .mk fun v => by simp [memberValueGraph]
instance delete_defined : 𝚺₁-Function₂ (delete : M → M → M) via deleteValueGraph :=
  .mk fun v => by simp [deleteValueGraph]
instance member_definable : 𝚺₁-Function₂ (member : M → M → M) := member_defined.to_definable
instance delete_definable : 𝚺₁-Function₂ (delete : M → M → M) := delete_defined.to_definable
instance member_definable' (Γ m) : Γ-[m + 1]-Function₂ (member : M → M → M) :=
  member_definable.of_sigmaOne
instance delete_definable' (Γ m) : Γ-[m + 1]-Function₂ (delete : M → M → M) :=
  delete_definable.of_sigmaOne

/-- The computation is Boolean in every PA model, including on vectors
whose length is nonstandard. -/
theorem member_boolean (x list : M) : member x list = 0 ∨ member x list = 1 := by
  induction list using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin y list ih =>
    by_cases h : y = x <;> simp [h, ih]

/-- The first appendix membership identity, proved by internal induction
on the numerical list rather than by testing global points. -/
theorem member_append (x left right : M) :
    member x (SyntacticSyntax.Words.append left right) =
      if member x left = 1 then 1 else member x right := by
  have h : member x (SyntacticSyntax.Words.append left right) = 1 ↔
      member x left = 1 ∨ member x right = 1 := by
    induction left using adjoin_ISigma1.pi1_succ_induction
    · definability
    case nil => simp
    case adjoin y left ih =>
      by_cases he : y = x <;> simp [he,ih]
  rcases member_boolean x left with hl | hl <;>
    rcases member_boolean x right with hr | hr <;>
    rcases member_boolean x (SyntacticSyntax.Words.append left right) with ho | ho <;>
      simp [hl,hr,ho] at h ⊢

/-- Deleting a name removes all occurrences, preserving all other
entries and their original order. -/
theorem member_delete (x y list : M) :
    member x (delete y list) = if x = y then 0 else member x list := by
  by_cases hxy : x = y
  · simp only [ite_eq_left hxy]
    subst y
    induction list using adjoin_ISigma1.pi1_succ_induction
    · definability
    case nil => simp
    case adjoin z list ih =>
      by_cases hz : z = x <;> simp [hz,ih]
  · simp only [ite_eq_right hxy]
    induction list using adjoin_ISigma1.pi1_succ_induction
    · definability
    case nil => simp
    case adjoin z list ih =>
      by_cases hzy : z = y <;> by_cases hzx : z = x <;> simp_all

/-- The membership test is a bounded numerical occurrence assertion,
independent of any Sigma-one predicate selecting the variable names. -/
theorem member_eq_one_iff (x list : M) :
    member x list = 1 ↔ ∃ i < len list,nth list i = x := by
  induction list using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin y list ih =>
    constructor
    · intro h
      by_cases he : y = x
      · exact ⟨0,by simp,by simpa using he⟩
      · have hm : member x list = 1 := by simpa [he] using h
        obtain ⟨i,hi,hix⟩ := ih.mp hm
        exact ⟨i+1,by simpa using hi,by simpa using hix⟩
    · rintro ⟨i,hi,hix⟩
      rcases zero_or_succ i with rfl | ⟨j,rfl⟩
      · have he : y = x := by simpa using hix
        simp [he]
      · have hj : j < len list := by simpa using hi
        have hm : member x list = 1 := ih.mpr ⟨j,hj,by simpa using hix⟩
        by_cases he : y = x <;> simp [he,hm]

/-- Appending preserves every positive variable-membership witness. -/
theorem append_carrier (V : SyntacticPredicates.Carrier) (left right : M)
    (hl : (SyntacticLists.listCarrier V).val.Evalb ![left])
    (hr : (SyntacticLists.listCarrier V).val.Evalb ![right]) :
    (SyntacticLists.listCarrier V).val.Evalb ![SyntacticSyntax.Words.append left right] :=
  SyntacticSyntax.Postfix.finiteMembership_append V left right hl hr

/-- Carrier preservation follows from the numerical membership identity,
without needing an induction formula that negates V. -/
theorem delete_carrier (V : SyntacticPredicates.Carrier) (x list : M)
    (hl : (SyntacticLists.listCarrier V).val.Evalb ![list]) :
    (SyntacticLists.listCarrier V).val.Evalb ![delete x list] := by
  rw [SyntacticLists.listCarrier_eval] at hl ⊢
  intro i hi
  have hm : member (nth (delete x list) i) (delete x list) = 1 :=
    (member_eq_one_iff _ _).mpr ⟨i,hi,rfl⟩
  rw [member_delete] at hm
  have hx : nth (delete x list) i ≠ x := by
    intro he
    simp [he] at hm
  rw [ite_eq_right hx] at hm
  obtain ⟨j,hj,he⟩ := (member_eq_one_iff _ _).mp hm
  simpa [he] using hl j hj

end Models

open SyntacticSyntax.NatVectors

/-- This certificate concerns the actual standard numerical computation,
separately from the all-model PA equations above. -/
theorem member_primrec : Primrec₂ (member : ℕ → ℕ → ℕ) := by
  have hn : Primrec (fun x : ℕ => (memberConstruction (M := ℕ)).nil ![x]) := Primrec.const 0
  have hs : Primrec₂ (fun x (t : ℕ × List ℕ × ℕ) =>
      (memberConstruction (M := ℕ)).adjoin ![x] t.1 (pack t.2.1) t.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.const 1) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact vecRec_primrec _ (fun x : ℕ => ![x]) hn hs

theorem delete_primrec : Primrec₂ (delete : ℕ → ℕ → ℕ) := by
  have hn : Primrec (fun x : ℕ => (deleteConstruction (M := ℕ)).nil ![x]) := Primrec.const 0
  have hs : Primrec₂ (fun x (t : ℕ × List ℕ × ℕ) =>
      (deleteConstruction (M := ℕ)).adjoin ![x] t.1 (pack t.2.1) t.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (adjoin_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact vecRec_primrec _ (fun x : ℕ => ![x]) hn hs

theorem member_natPrimrec : Nat.Primrec (Nat.unpaired (member : ℕ → ℕ → ℕ)) :=
  Primrec₂.unpaired'.mpr member_primrec

theorem delete_natPrimrec : Nat.Primrec (Nat.unpaired (delete : ℕ → ℕ → ℕ)) :=
  Primrec₂.unpaired'.mpr delete_primrec

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
