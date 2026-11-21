/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionCharts

/-! # Ordered children in the finite powers of derivation objects -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
open SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The projection convention agrees with the chosen left-associated
finite powers; there is no projection from the nullary unit. -/
def powerProjection (U : ArithmeticTheory) [𝗣𝗔 ⪯ U] (X Y : PredicateCategory U) : (n : ℕ) → (i : Fin n) →
    (SyntaxPolynomial.power .term n).eval.obj (X,Y) ⟶ X
  | 0, i => i.elim0
  | 1, _ => 𝟙 X
  | n + 2, i => Fin.lastCases prod.snd
      (fun j => prod.fst ≫ powerProjection U X Y (n + 1) j) i

@[simp] theorem powerProjection_last (X Y : PredicateCategory T) (n : ℕ) :
    powerProjection T X Y (n + 2) (Fin.last (n + 1)) =
      (prod.snd : (SyntaxPolynomial.power .term (n + 1)).eval.obj (X,Y) ⨯ X ⟶ X) := by
  simp only [powerProjection, Fin.lastCases_last]
  rfl

@[simp] theorem powerProjection_castSucc (X Y : PredicateCategory T) (n : ℕ) (i : Fin (n + 1)) :
    powerProjection T X Y (n + 2) i.castSucc =
      (prod.fst : (SyntaxPolynomial.power .term (n + 1)).eval.obj (X,Y) ⨯ X ⟶ _) ≫
        powerProjection T X Y (n + 1) i := by
  simp only [powerProjection, Fin.lastCases_castSucc]
  rfl

theorem powerProjection_natural {X Y X' Y' : PredicateCategory T}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (i : Fin n) :
    (SyntaxPolynomial.power .term n).eval.map ((f,g) : (X,Y) ⟶ (X',Y')) ≫
      powerProjection T X' Y' n i = powerProjection T X Y n i ≫ f := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      cases n with
      | zero => simp [SyntaxPolynomial.power, SyntaxPolynomial.eval, powerProjection]
      | succ n =>
          refine Fin.lastCases ?_ (fun j => ?_) i
          · rw [powerProjection_last, powerProjection_last]
            change prod.map _ f ≫ prod.snd = prod.snd ≫ f
            exact prod.map_snd _ _
          · rw [powerProjection_castSucc, powerProjection_castSucc]
            change prod.map
                ((SyntaxPolynomial.power .term (n + 1)).eval.map ((f,g) : (X,Y) ⟶ (X',Y'))) f ≫
                (prod.fst ≫ powerProjection T X' Y' (n + 1) j) =
              (prod.fst ≫ powerProjection T X Y (n + 1) j) ≫ f
            simp only [prod.map_fst_assoc, Category.assoc, ih]

/-- Chosen finite-power coordinates are read through the proved finite-power/polynomial
isomorphism. -/
def finiteChild (X : PredicateCategory T) (n : ℕ) (i : Fin n) : finitePower X n ⟶ X :=
  (PolynomialComparison.powerIso X n).hom ≫ powerProjection T X (⊤_ (PredicateCategory T)) n i

theorem finiteChild_natural {X Y : PredicateCategory T} (f : X ⟶ Y) (n : ℕ) (i : Fin n) :
    finitePowerMap f n ≫ finiteChild T Y n i = finiteChild T X n i ≫ f := by
  rw [finiteChild, ← Category.assoc, PolynomialComparison.powerIso_natural,
    Category.assoc, powerProjection_natural, ← Category.assoc]
  rfl

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A represented raw power with the internal child-size certificate bounds every
interpreted categorical projection. -/
theorem power_children_smaller (X Y : PredicateCategory T) (n : ℕ) (bound u : M)
    (z : Obj T M ((SyntaxPolynomial.power .term n).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.power .term n)).val.Evalb ![u,z.val])
    (hs : Coding.ChildSize (SyntaxPolynomial.power .term n) bound u) :
    ∀ i : Fin n, len ((F T M).map (powerProjection T X Y n i) z).val < bound := by
  induction n generalizing u with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      cases n with
      | zero =>
          intro i
          have he := (baseRepresentation_term_eval T M X Y u z.val).mp hz
          change len ((F T M).map (𝟙 X) z).val < bound
          rw [(F T M).map_id]
          change len z.val < bound
          rw [he.2]
          exact hs
      | succ n =>
          obtain ⟨v,w,r,s,he,hr,ht,hzr,hzs⟩ :=
            (baseRepresentation_product_eval T M X Y
              (SyntaxPolynomial.power .term (n + 1)) .term u z.val).mp hz
          let left : Obj T M ((SyntaxPolynomial.power .term (n + 1)).eval.obj (X,Y)) :=
            ⟨r,(baseRepresentation_support T M X Y _ v r hr).2⟩
          let right : Obj T M X := ⟨s,(baseRepresentation_support T M X Y .term w s ht).2⟩
          have hl : (F T M).map (prod.fst : _ ⟶ (SyntaxPolynomial.power .term (n + 1)).eval.obj (X,Y)) z = left :=
            (chosenGraph_map_iff T M prod.fst z left).mp hzr
          have hh : (F T M).map (prod.snd : _ ⟶ X) z = right :=
            (chosenGraph_map_iff T M prod.snd z right).mp hzs
          have hsize : Coding.ChildSize (SyntaxPolynomial.power .term (n + 1)) bound v ∧ len w < bound := by
            simpa only [SyntaxPolynomial.power, Coding.ChildSize, he, pi₁_pair, pi₂_pair] using hs
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · rw [powerProjection_last]
            change len ((F T M).map prod.snd z).val < bound
            have hre := (baseRepresentation_term_eval T M X Y w s).mp ht
            have hb : len right.val < bound := by
              change len s < bound
              rw [hre.2]
              exact hsize.2
            exact (congrArg (fun t : Obj T M X => len t.val) hh).trans_lt hb
          · rw [powerProjection_castSucc]
            change len ((F T M).map (prod.fst ≫ powerProjection T X Y (n + 1) j) z).val < bound
            rw [Functor.map_comp_apply, hl]
            exact ih v left hr hsize.1 j

/-- Nested coproduct tags retain the selected rule arity in the raw input. -/
def ruleTag (A : Type) [ORingStructure A] [A↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] : (n : ℕ) → Fin (n + 1) → A → A
  | 0, _, payload => payload
  | n + 1, i, payload => Fin.lastCases (Arithmetic.pair payload 1)
      (fun j => Arithmetic.pair (ruleTag A n j payload) 0) i

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
/-- The size condition at the arity branch is exactly the condition on
its ordered child power; the coefficient label contributes no children. -/
theorem ruleTag_childSize (labels : ℕ → PredicateCategory T) (n : ℕ)
    (i : Fin (n + 1)) (bound label tuple : M)
    (hs : Coding.ChildSize (SyntaxPolynomial.constructors labels n) bound
      (ruleTag M n i (Arithmetic.pair label tuple))) :
    Coding.ChildSize (SyntaxPolynomial.power .term i.val) bound tuple := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      trivial
  | succ n ih =>
      revert hs
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hs
        simpa [ruleTag, SyntaxPolynomial.constructors, Coding.ChildSize] using hs
      · intro hs
        apply ih j
        simpa [ruleTag, SyntaxPolynomial.constructors, Coding.ChildSize] using hs

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
