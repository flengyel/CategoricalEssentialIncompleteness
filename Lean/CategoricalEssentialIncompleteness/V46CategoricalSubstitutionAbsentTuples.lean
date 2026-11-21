/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentInvariant

/-! Finite argument tuples propagate absence to every recursive argument. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.AbsentTuples
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P : D} (A : Over P × Over P)

abbrev family (n : ℕ) : Over P :=
  ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).withParameters P).eval.obj A

abbrev value (Y Z : D) (n : ℕ) : D :=
  (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.obj (Y,Z)

/-- Traverse a finite recursive tuple in the parameter slice, reading a
base-category value from every recursive coordinate. -/
def tupleMap {Y Z : D} (f : A.1.left ⟶ Y) : (n : ℕ) →
    (family A n).left ⟶ value Y Z n
  | 0 => terminal.from _
  | 1 => f
  | n+2 => prod.lift
      ((prod.fst : family A (n+1) ⨯ A.1 ⟶ family A (n+1)).left ≫ tupleMap f (n+1))
      ((prod.snd : family A (n+1) ⨯ A.1 ⟶ A.1).left ≫ f)

theorem tupleMap_natural {Y Z Y' Z' : D} (f : A.1.left ⟶ Y)
    (g : (Y,Z) ⟶ (Y',Z')) (n : ℕ) :
    tupleMap A (Z := Z) f n ≫ (SyntaxPolynomial.power .term n).eval.map g =
      tupleMap A (Z := Z') (f ≫ g.1) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact terminalIsTerminal.hom_ext _ _
  | one => rfl
  | more n _ ih =>
    change prod.lift _ _ ≫ prod.map _ _ = prod.lift _ _
    rw [prod.lift_map, Category.assoc, Category.assoc, ih]
    rfl

omit [FinitaryExtensive D] in
theorem product_comparison_value {X Y : Over P} {U W : D}
    (f : X ⟶ constantFamily P U) (g : Y ⟶ constantFamily P W) :
    (prod.map f g ≫ constantProductComparison P U W).left ≫ prod.snd =
      prod.lift ((prod.fst : X ⨯ Y ⟶ X).left ≫ f.left ≫ prod.snd)
        ((prod.snd : X ⨯ Y ⟶ Y).left ≫ g.left ≫ prod.snd) := by
  have hf := congrArg (fun h => h.left ≫ prod.snd) (prod.map_fst f g)
  have hg := congrArg (fun h => h.left ≫ prod.snd) (prod.map_snd f g)
  simp only [Over.comp_left, Category.assoc] at hf hg
  simp only [Over.comp_left, constantProductComparison, Over.homMk_left,
    prod.lift_snd, prod.comp_lift]
  exact congrArg₂ prod.lift hf hg

/-- The traversal is the value coordinate of the polynomial comparison. -/
theorem tupleMap_comparison {Y Z : D}
    (f : A ⟶ (constantFamily P Y, constantFamily P Z)) (n : ℕ) :
    (((SyntaxPolynomial.power .term n).withParameters P).eval.map f ≫
      SyntaxPolynomial.parameterComparison P (Y,Z) (SyntaxPolynomial.power .term n)).left ≫
        prod.snd = tupleMap A (Z := Z) (f.1.left ≫ prod.snd) n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [SyntaxPolynomial.power, SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
      SyntaxPolynomial.parameterComparison, constantUnitComparison, tupleMap, family]
  | one =>
    simp [SyntaxPolynomial.power, SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
      SyntaxPolynomial.parameterComparison, tupleMap]
  | more n _ ih =>
    change (prod.map _ f.1 ≫ (prod.map _ (𝟙 _) ≫
      constantProductComparison P (value Y Z (n+1)) Y)).left ≫ prod.snd = _
    rw [← Category.assoc, prod.map_map, Category.comp_id, product_comparison_value]
    change prod.lift _ _ =
      prod.lift
        ((prod.fst : family A (n+1) ⨯ A.1 ⟶ family A (n+1)).left ≫
          tupleMap A (Z := Z) (f.1.left ≫ prod.snd) (n+1))
        ((prod.snd : family A (n+1) ⨯ A.1 ⟶ A.1).left ≫ f.1.left ≫ prod.snd)
    apply prod.hom_ext
    · simp only [prod.lift_fst]
      simpa only [Over.comp_left, Category.assoc, tupleMap, prod.lift_fst, family, value,
        CategoryTheory.Prod.fst] using
          congrArg (fun h =>
            (prod.fst : family A (n+1) ⨯ A.1 ⟶ family A (n+1)).left ≫ h) ih
    · simp only [prod.lift_snd]

/-- If each recursive value is fixed whenever its name is absent, an entire
finite tuple is fixed whenever that name is absent from its concatenated FV list. -/
theorem tuple_absence {V T Z : D} (L : StableListAlgebra V) (E : DecidableVariables V)
    (name : P ⟶ V) (FV : T ⟶ L.algebra.carrier)
    (original result : A.1.left ⟶ T)
    (good : ∀ {X : D} (k : X ⟶ A.1.left),
      prod.lift (k ≫ A.1.hom ≫ name) (k ≫ original ≫ FV) ≫ L.membership E =
        Two.constant X false → k ≫ result = k ≫ original)
    (n : ℕ) : ∀ {X : D} (k : X ⟶ (family A n).left),
      prod.lift (k ≫ (family A n).hom ≫ name)
        (k ≫ tupleMap A (Z := L.algebra.carrier) (original ≫ FV) n ≫ L.tupleAppend n) ≫
          L.membership E = Two.constant X false →
      k ≫ tupleMap A (Z := Z) result n = k ≫ tupleMap A (Z := Z) original n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro X k _
    exact terminalIsTerminal.hom_ext _ _
  | one =>
    intro X k hk
    exact good k (by simpa [tupleMap, StableListAlgebra.tupleAppend, Category.assoc, family,
      SyntaxPolynomial.power, SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
      CategoryTheory.Prod.fst] using hk)
  | more n _ ih =>
    intro X k hk
    let kl := k ≫ (prod.fst : family A (n+1) ⨯ A.1 ⟶ family A (n+1)).left
    let kr := k ≫ (prod.snd : family A (n+1) ⨯ A.1 ⟶ A.1).left
    let x := k ≫ (family A (n+2)).hom ≫ name
    let wl := kl ≫ tupleMap A (Z := L.algebra.carrier) (original ≫ FV) (n+1) ≫
      L.tupleAppend (n+1)
    let wr := kr ≫ original ≫ FV
    have haggregate : prod.lift x (prod.lift wl wr ≫ L.append) ≫ L.membership E =
        Two.constant X false := by
      simpa only [tupleMap, StableListAlgebra.tupleAppend, prod.lift_map_assoc,
        Category.comp_id, prod.comp_lift_assoc, Category.assoc, x, wl, wr, kl, kr, family, value,
        SyntaxPolynomial.power, SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
        SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst] using hk
    have hor : (prod.lift x wl ≫ L.membership E) ⊔
        (prod.lift x wr ≫ L.membership E) = (⊥ : X ⟶ Two D) := by
      change Two.binary Bool.or _ _ = Two.constant X false
      rw [← L.membership_append E x wl wr]
      exact haggregate
    have hl : prod.lift x wl ≫ L.membership E = Two.constant X false :=
      bot_unique (le_trans le_sup_left hor.le)
    have hr : prod.lift x wr ≫ L.membership E = Two.constant X false :=
      bot_unique (le_trans le_sup_right hor.le)
    have hbl : kl ≫ (family A (n+1)).hom ≫ name = x := by
      have hb := Over.w (prod.fst : family A (n+1) ⨯ A.1 ⟶ family A (n+1))
      simpa only [kl, x, family, SyntaxPolynomial.power, SyntaxPolynomial.withParameters,
        SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst,
        Category.assoc] using
          congrArg (fun h => k ≫ h ≫ name) hb
    have hbr : kr ≫ A.1.hom ≫ name = x := by
      have hb := Over.w (prod.snd : family A (n+1) ⨯ A.1 ⟶ A.1)
      simpa only [kr, x, family, SyntaxPolynomial.power, SyntaxPolynomial.withParameters,
        SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst,
        Category.assoc] using
          congrArg (fun h => k ≫ h ≫ name) hb
    have hkl := ih kl (by rw [hbl]; exact hl)
    have hkr := good kr (by rw [hbr]; exact hr)
    apply prod.hom_ext
    · simpa only [tupleMap, Category.assoc, prod.lift_fst, kl, family, value,
        SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
        CategoryTheory.Prod.fst] using hkl
    · simpa only [tupleMap, Category.assoc, prod.lift_snd, kr, family, value,
        SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
        CategoryTheory.Prod.fst] using hkr

end CategoricalEssentialIncompleteness.V46.AbsentTuples
