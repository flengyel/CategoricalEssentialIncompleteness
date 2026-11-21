/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! Literal ordered mapping of the recursive positions of a raw polynomial.
Coefficient labels remain unchanged. This supplies the original/result
projections for the paired named-substitution traversal. -/

@[expose] public section
noncomputable section
local instance primitiveNamedMapDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

def mapChildrenGraph (F G : 𝚺₁.Semisentence 2) : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => F
  | .formula => G
  | .coefficient _ => .mkSigma “out value. out = value”
  | .unit => .mkSigma “out value. out = 0”
  | .product a b =>
    let A := mapChildrenGraph F G a
    let B := mapChildrenGraph F G b
    .mkSigma “out value. ∃ l r x y, !pi₁Def.val l value ∧ !pi₂Def.val r value ∧
      !A.val x l ∧ !B.val y r ∧ !pairDef.val out x y”
  | .sum a b =>
    let A := mapChildrenGraph F G a
    let B := mapChildrenGraph F G b
    .mkSigma “out value. ∃ tag payload mapped, !pi₁Def.val payload value ∧ !pi₂Def.val tag value ∧
      ((tag = 0 ∧ !A.val mapped payload) ∨ (tag ≠ 0 ∧ !B.val mapped payload)) ∧
      !pairDef.val out mapped tag”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedMapModelDecidableEq : DecidableEq M := Classical.decEq M

def mapChildren (f g : M → M) : RawPolynomial → M → M
  | .term, value => f value
  | .formula, value => g value
  | .coefficient _, value => value
  | .unit, _ => 0
  | .product a b, value => ⟪mapChildren f g a (π₁ value), mapChildren f g b (π₂ value)⟫
  | .sum a b, value =>
    ⟪if π₂ value = 0 then mapChildren f g a (π₁ value) else mapChildren f g b (π₁ value), π₂ value⟫

/-- Mapping recursive values leaves every node tag and coefficient label
unchanged, on arbitrary numerical inputs. -/
@[simp] theorem shape_mapChildren (q : RawPolynomial) (f g : M → M) (u : M) :
    shape q (mapChildren f g q u) = shape q u := by
  induction q generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib => simp [mapChildren,shape,ia,ib]
  | sum a b ia ib =>
      by_cases h : π₂ u = 0 <;> simp [mapChildren,shape,ia,ib,h]

/-- This is a local polynomial chart lemma. The later applications prove the two
leaf-preservation hypotheses for their numeric functions. -/
theorem rawCarrier_mapChildren {X Y Z W : SyntacticPredicates.Carrier}
    (q : RawPolynomial) (f g : M → M)
    (hf : ∀ x : M,X.val.Evalb ![x] → Z.val.Evalb ![f x])
    (hg : ∀ y : M,Y.val.Evalb ![y] → W.val.Evalb ![g y])
    (u : M) (hu : (rawCarrier X Y q).val.Evalb ![u]) :
    (rawCarrier Z W q).val.Evalb ![mapChildren f g q u] := by
  induction q generalizing u with
  | term => exact hf u hu
  | formula => exact hg u hu
  | coefficient _ => exact hu
  | unit => simp [mapChildren,rawCarrier]
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ := (rawCarrier_product_eval X Y a b u).mp hu
      have hp := (rawCarrier_product_eval Z W a b
        ⟪mapChildren f g a x,mapChildren f g b y⟫).mpr ⟨_,_,rfl,ia x hx,ib y hy⟩
      simpa [mapChildren] using hp
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval X Y a b u).mp hu with ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · exact (rawCarrier_sum_eval Z W a b _).mpr (Or.inl ⟨_,by simp [mapChildren],ia x hx⟩)
      · exact (rawCarrier_sum_eval Z W a b _).mpr (Or.inr ⟨_,by simp [mapChildren],ib y hy⟩)

/-- No numerical unit normalization is used without its chart guard. -/
theorem mapChildren_id {X Y : SyntacticPredicates.Carrier} (q : RawPolynomial)
    (u : M) (hu : (rawCarrier X Y q).val.Evalb ![u]) :
    mapChildren id id q u = u := by
  induction q generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit =>
      have h : u = 0 := by simpa [rawCarrier] using hu
      simpa [mapChildren] using h.symm
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ := (rawCarrier_product_eval X Y a b u).mp hu
      simp [mapChildren,ia x hx,ib y hy]
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval X Y a b u).mp hu with ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · simp [mapChildren,ia x hx]
      · simp [mapChildren,ib y hy]

@[simp] theorem mapChildren_comp (q : RawPolynomial) (f g h k : M → M) (u : M) :
    mapChildren h k q (mapChildren f g q u) = mapChildren (h ∘ f) (k ∘ g) q u := by
  induction q generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib => simp [mapChildren,ia,ib]
  | sum a b ia ib =>
      by_cases htag : π₂ u = 0 <;> simp [mapChildren,ia,ib,htag]

variable (F G : 𝚺₁.Semisentence 2) (f g : M → M)
  [𝚺₁-Function₁ f via F] [𝚺₁-Function₁ g via G]

@[simp] theorem mapChildrenGraph_eval (q : RawPolynomial) (out value : M) :
    (mapChildrenGraph F G q).val.Evalb ![out,value] ↔ out = mapChildren f g q value := by
  induction q generalizing out value with
  | term => exact (show 𝚺₁-Function₁ f via F from inferInstance).iff
  | formula => exact (show 𝚺₁-Function₁ g via G from inferInstance).iff
  | coefficient _ => simp [mapChildrenGraph, mapChildren]
  | unit => simp [mapChildrenGraph, mapChildren]
  | product a b ia ib => simp [mapChildrenGraph, mapChildren, ia, ib]
  | sum a b ia ib =>
      by_cases h : π₂ value = 0 <;> simp [mapChildrenGraph, mapChildren, ia, ib, h]

theorem mapChildren_defined (q : RawPolynomial) :
    𝚺₁-Function₁ (mapChildren f g q : M → M) via mapChildrenGraph F G q :=
  .mk fun v => by
    have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
    simpa [hv] using mapChildrenGraph_eval F G f g q (v 0) (v 1)

end Models

open SyntacticSyntax.NatVectors

theorem mapChildren_primrec (q : RawPolynomial) (f g : ℕ → ℕ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (mapChildren f g q : ℕ → ℕ) := by
  induction q with
  | term => exact hf
  | formula => exact hg
  | coefficient _ => exact Primrec.id
  | unit => exact Primrec.const 0
  | product a b ia ib => exact pair_primrec.comp (ia.comp pi1_primrec) (ib.comp pi2_primrec)
  | sum a b ia ib =>
      exact pair_primrec.comp
        (Primrec.ite (Primrec.eq.comp pi2_primrec (Primrec.const 0))
          (ia.comp pi1_primrec) (ib.comp pi1_primrec)) pi2_primrec

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
