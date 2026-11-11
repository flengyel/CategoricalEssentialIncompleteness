/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Ultrapower
public import CategoricalEssentialIncompleteness.V46SyntacticSearch

/-! # Arithmetic on the quotient of natural-number families -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter

namespace CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower

variable {I : Type} (U : Ultrafilter I)

abbrev Model := Ultrapower.Obj U ℕ

/-- Arithmetic operations are coordinatewise and strict order holds on
an ultrafilter-large set of coordinates. -/
instance arithmeticStructure : ORingStructure (Model U) where
  toZero := inferInstance
  toOne := inferInstance
  toAdd := inferInstance
  toMul := inferInstance
  toLT := ⟨Germ.LiftRel (· < ·)⟩

theorem term_representative {n : ℕ} (t : ArithmeticSemiterm Empty n)
    (b : Fin n → I → ℕ) :
    t.val (M := Model U) (fun j => Germ.ofFun (b j)) Empty.elim =
      Germ.ofFun (fun i => t.val (M := ℕ) (fun j => b j i) Empty.elim) := by
  induction t with
  | bvar j => rfl
  | fvar j => exact j.elim
  | func f ts ih =>
    cases f with
    | zero => rfl
    | one => rfl
    | add =>
      change (ts 0).val _ _ + (ts 1).val _ _ =
        Germ.ofFun (fun i => (ts 0).val _ _ + (ts 1).val _ _)
      rw [ih 0, ih 1]
      rfl
    | mul =>
      change (ts 0).val _ _ * (ts 1).val _ _ =
        Germ.ofFun (fun i => (ts 0).val _ _ * (ts 1).val _ _)
      rw [ih 0, ih 1]
      rfl

theorem germ_cons {n : ℕ} (x : I → ℕ) (b : Fin n → I → ℕ) :
    (fun j => (Germ.ofFun ((x :> b) j) : Model U)) =
      Germ.ofFun x :> fun j => Germ.ofFun (b j) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

theorem coordinate_cons {n : ℕ} (x : I → ℕ) (b : Fin n → I → ℕ) (i : I) :
    (fun j => (x :> b) j i) = x i :> fun j => b j i := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

/-- Los's theorem for the arithmetic quotient, at arbitrary finite
families of bound variables. Quantified values range over the whole quotient. -/
theorem eval_representative {n : ℕ} (φ : ArithmeticSemisentence n)
    (b : Fin n → I → ℕ) :
    φ.Evalb (M := Model U) (fun j => Germ.ofFun (b j)) ↔
      ∀ᶠ i in (U : Filter I), φ.Evalb (M := ℕ) (fun j => b j i) := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum =>
    change False ↔ ∀ᶠ _ in (U : Filter I), False
    constructor
    · exact False.elim
    · intro h
      obtain ⟨i, hi⟩ := h.exists
      exact hi
  | hrel r ts =>
    cases r with
    | eq =>
      change (ts 0).val _ _ = (ts 1).val _ _ ↔
        ∀ᶠ i in (U : Filter I), (ts 0).val _ _ = (ts 1).val _ _
      rw [term_representative, term_representative]
      exact Germ.coe_eq
    | lt =>
      change Germ.LiftRel (l := (U : Filter I)) (fun a b : ℕ => a < b)
        ((ts 0).val (M := Model U) (fun j => Germ.ofFun (b j)) Empty.elim)
        ((ts 1).val (M := Model U) (fun j => Germ.ofFun (b j)) Empty.elim) ↔
        ∀ᶠ i in (U : Filter I),
          (ts 0).val (M := ℕ) (fun j => b j i) Empty.elim <
            (ts 1).val (M := ℕ) (fun j => b j i) Empty.elim
      rw [term_representative, term_representative]
      rfl
  | hnrel r ts =>
    cases r with
    | eq =>
      change (¬(ts 0).val _ _ = (ts 1).val _ _) ↔
        ∀ᶠ i in (U : Filter I), ¬(ts 0).val _ _ = (ts 1).val _ _
      rw [term_representative, term_representative, Germ.coe_eq]
      exact Ultrafilter.eventually_not.symm
    | lt =>
      change (¬Germ.LiftRel (l := (U : Filter I)) (fun a b : ℕ => a < b)
        ((ts 0).val (M := Model U) (fun j => Germ.ofFun (b j)) Empty.elim)
        ((ts 1).val (M := Model U) (fun j => Germ.ofFun (b j)) Empty.elim)) ↔
        ∀ᶠ i in (U : Filter I),
          ¬(ts 0).val (M := ℕ) (fun j => b j i) Empty.elim <
            (ts 1).val (M := ℕ) (fun j => b j i) Empty.elim
      rw [term_representative, term_representative, Germ.liftRel_coe]
      exact Ultrafilter.eventually_not.symm
  | hand φ ψ hp hq =>
    change (φ.Evalb (M := Model U) (fun j => Germ.ofFun (b j)) ∧
      ψ.Evalb (M := Model U) (fun j => Germ.ofFun (b j))) ↔ _
    rw [hp, hq]
    exact Filter.eventually_and.symm
  | hor φ ψ hp hq =>
    change (φ.Evalb (M := Model U) (fun j => Germ.ofFun (b j)) ∨
      ψ.Evalb (M := Model U) (fun j => Germ.ofFun (b j))) ↔ _
    rw [hp, hq]
    exact Ultrafilter.eventually_or.symm
  | hall φ ih =>
    change (∀ x : Model U, φ.Evalb (x :> fun j => Germ.ofFun (b j))) ↔
      ∀ᶠ i in (U : Filter I), ∀ x : ℕ, φ.Evalb (x :> fun j => b j i)
    constructor
    · intro h
      let x : I → ℕ := fun i => Classical.epsilon
        (fun a => ¬φ.Evalb (M := ℕ) (a :> fun j => b j i))
      have ihx := ih (x :> b)
      simp only [germ_cons, coordinate_cons] at ihx
      have hx := ihx.mp (h (Germ.ofFun x))
      filter_upwards [hx] with i hi a
      by_contra ha
      have hn := Classical.epsilon_spec (p := fun z =>
        ¬φ.Evalb (M := ℕ) (z :> fun j => b j i)) ⟨a, ha⟩
      exact hn hi
    · intro h x
      induction x using Germ.inductionOn with | _ x =>
        have ihx := ih (x :> b)
        simp only [germ_cons, coordinate_cons] at ihx
        apply ihx.mpr
        filter_upwards [h] with i hi
        exact hi (x i)
  | hexs φ ih =>
    change (∃ x : Model U, φ.Evalb (x :> fun j => Germ.ofFun (b j))) ↔
      ∀ᶠ i in (U : Filter I), ∃ x : ℕ, φ.Evalb (x :> fun j => b j i)
    constructor
    · rintro ⟨x, hx⟩
      induction x using Germ.inductionOn with | _ x =>
        have ihx := ih (x :> b)
        simp only [germ_cons, coordinate_cons] at ihx
        have hx' := ihx.mp hx
        filter_upwards [hx'] with i hi
        exact ⟨x i, hi⟩
    · intro h
      let x : I → ℕ := fun i => Classical.epsilon
        (fun a => φ.Evalb (M := ℕ) (a :> fun j => b j i))
      refine ⟨Germ.ofFun x, ?_⟩
      have hx : ∀ᶠ i in (U : Filter I),
          φ.Evalb (M := ℕ) (x i :> fun j => b j i) := by
        filter_upwards [h] with i hi
        exact Classical.epsilon_spec (p := fun a =>
          φ.Evalb (M := ℕ) (a :> fun j => b j i)) hi
      have ihx := ih (x :> b)
      simp only [germ_cons, coordinate_cons] at ihx
      exact ihx.mpr hx

/-- Every arithmetic sentence has its standard truth value in this
ultrapower; in particular the quotient is a model of PA. -/
theorem sentence_iff (φ : ArithmeticSentence) :
    (Model U)↓[ℒₒᵣ] ⊧ φ ↔ ℕ↓[ℒₒᵣ] ⊧ φ := by
  simpa only [models_iff, Matrix.empty_eq, Filter.eventually_const] using
    eval_representative U φ ![]

instance modelsPA : (Model U)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ⟨by
  intro φ hφ
  exact (sentence_iff U φ).mpr (models_of_mem hφ)⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower
