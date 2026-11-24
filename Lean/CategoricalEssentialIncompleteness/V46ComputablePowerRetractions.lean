/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputablePowerProducts

/-! # Each formal finite power of a partial combinatory algebra is a retract of the algebra

The code for the polynomial sending (x,y,z) to (z x) y gives the pairing morphism
after its first two applications. Feeding it the codes of the two projections retrieves
x and y, as in Cockett and Hofstra, Theorem 4.7.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory PCategoryStruct PCategory RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)
variable (unit : IsRestrictionTerminal t)

include unit in
theorem IsRestrictionTerminal.naturality_of_total {X Y : C} {f : X ⟶ Y} (hf : isTotal f) :
    f ≫ t Y = t X := by
  have h : PCategoryStruct.rst (f ≫ t Y) = 𝟙 X := isTotal_comp hf (unit.total Y)
  rw [unit.domain (f ≫ t Y), h, Category.id_comp]

def applyPolynomial {X : C} (f g : X ⟶ A) : X ⟶ A := partialPairing f g ≫ app

theorem comp_applyPolynomial {W X : C} (a : W ⟶ X) (f g : X ⟶ A) :
    a ≫ applyPolynomial app f g = applyPolynomial app (a ≫ f) (a ≫ g) := by
  rw [applyPolynomial, applyPolynomial, ← Category.assoc, comp_partialPairing]

theorem Polynomial.apply {n : ℕ} {f g : power Z A n ⟶ A}
    (hf : Polynomial app t n 1 f) (hg : Polynomial app t n 1 g) :
    Polynomial app t n 1 (applyPolynomial app f g) :=
  (hf.pair hg).comp .application

def pairingPolynomial : positivePower A 2 ⟶ A :=
  let X := nearProd A A
  applyPolynomial app (applyPolynomial app (p1 X A) (p0 X A ≫ p0 A A))
    (p0 X A ≫ p1 A A)

theorem pairingPolynomial_mem : Polynomial app t 3 1 (pairingPolynomial app) :=
  ((Polynomial.last 1).apply app t ((Polynomial.first 1).comp (.first 0))).apply app t
    ((Polynomial.first 1).comp (.last 0))

include unit in
theorem pairing_specialization (pair : nearProd A A ⟶ A) (hp : isTotal pair)
    (eqn : nearProd_map pair (𝟙 A) ≫ app = pairingPolynomial app)
    (q : Z ⟶ A) (hq : isTotal q) :
    pair ≫ applyPolynomial app (𝟙 A) (t A ≫ q) = applyPositive app t q 1 := by
  let P := nearProd A A
  let atPoint := partialPairing (𝟙 P) (t P ≫ q)
  have left : atPoint ≫ p0 P A = 𝟙 P :=
    p0_partialPairing_of_isTotal _ (isTotal_comp (unit.total P) hq)
  have right : atPoint ≫ p1 P A = t P ≫ q :=
    p1_partialPairing_of_isTotal _ (RestrictionCategory.rst_id P)
  have lhs : atPoint ≫ (nearProd_map pair (𝟙 A) ≫ app) =
      pair ≫ applyPolynomial app (𝟙 A) (t A ≫ q) := by
    rw [← Category.assoc, partialPairing_comp_nearProd_map, comp_applyPolynomial,
      Category.id_comp, Category.comp_id, ← Category.assoc pair,
      IsRestrictionTerminal.naturality_of_total t unit hp]
    simp only [Category.comp_id, applyPolynomial, P]
  have rhs : atPoint ≫ pairingPolynomial app = applyPositive app t q 1 := by
    change atPoint ≫ applyPolynomial app
      (applyPolynomial app (p1 P A) (p0 P A ≫ p0 A A)) (p0 P A ≫ p1 A A) =
      nearProd_map (applyPolynomial app (t A ≫ q) (𝟙 A)) (𝟙 A) ≫ app
    rw [comp_applyPolynomial, comp_applyPolynomial, right, ← Category.assoc atPoint,
      left, Category.id_comp, ← Category.assoc atPoint, left, Category.id_comp,
      nearProd_eq_partialPairing, Category.comp_id, comp_applyPolynomial, Category.comp_id,
      ← Category.assoc (p0 A A), IsRestrictionTerminal.naturality_of_total t unit (p0_isTotal A A)]
    rfl
  exact lhs.symm.trans ((congrArg (fun k => atPoint ≫ k) eqn).trans rhs)

include unit in
theorem square_retract (complete : CombinatoriallyComplete app t) :
    ∃ (m : formal app t 2 ⟶ formal app t 1) (r : formal app t 1 ⟶ formal app t 2),
      isTotal m ∧ m ≫ r = 𝟙 _ := by
  obtain ⟨p, hp, total, eqn⟩ := complete 3 _ (pairingPolynomial_mem app t)
  obtain ⟨a, ha, _, ea⟩ := complete 2 _ (Polynomial.first 0)
  obtain ⟨b, hb, _, eb⟩ := complete 2 _ (Polynomial.last 0)
  let pair := applyPositive app t p 1
  let first := applyPolynomial app (𝟙 A) (t A ≫ a)
  let last := applyPolynomial app (𝟙 A) (t A ≫ b)
  have poly {q : Z ⟶ A} (hq : isTotal q) :
      Polynomial app t 1 1 (applyPolynomial app (𝟙 A) (t A ≫ q)) :=
    (Polynomial.ident 1).apply app t ((Polynomial.terminate 1).comp (.point q hq))
  refine ⟨⟨pair, applyPositive_polynomial app t p hp 1⟩,
    ⟨partialPairing first last, (poly ha).pair (poly hb)⟩, Subtype.ext total, Subtype.ext ?_⟩
  change pair ≫ partialPairing first last = 𝟙 _
  rw [comp_partialPairing, (pairing_specialization app t unit pair total eqn a ha).trans ea,
    (pairing_specialization app t unit pair total eqn b hb).trans eb]
  exact partialPairing_p0_p1 A A

/-- Extend a polynomial morphism by the identity on the last coordinate. -/
def withLast {m n : ℕ} (f : formal app t (m+1) ⟶ formal app t (n+1)) :
    formal app t (m+2) ⟶ formal app t (n+2) :=
  ⟨nearProd_map f.val (𝟙 A), by
    rw [nearProd_eq_partialPairing, Category.comp_id]
    exact ((Polynomial.first m).comp f.property).pair (.last m)⟩

include unit in
theorem powers_retract (complete : CombinatoriallyComplete app t) (X : Powers app t) :
    ∃ (m : X ⟶ formal app t 1) (r : formal app t 1 ⟶ X),
      isTotal m ∧ m ≫ r = 𝟙 X := by
  obtain ⟨encode, decode, hencode, cancel⟩ := square_retract app t unit complete
  obtain ⟨n⟩ := X
  cases n with
  | zero =>
    obtain ⟨p, hp⟩ := complete 1 (𝟙 A) (Polynomial.ident 1)
    have total : isTotal p := hp.1
    have unit_id : t Z = 𝟙 Z := by
      simpa only [PCategory.rst_id, Category.id_comp] using (unit.domain (𝟙 Z)).symm
    exact ⟨⟨p, .point p total⟩, terminate app t _, Subtype.ext total,
      Subtype.ext ((IsRestrictionTerminal.naturality_of_total t unit total).trans unit_id)⟩
  | succ k =>
    induction k with
    | zero => exact ⟨𝟙 _, 𝟙 _, RestrictionCategory.rst_id _, Category.comp_id _⟩
    | succ k ih =>
      obtain ⟨m, r, hm, hmr⟩ := ih
      have lifts : withLast app t m ≫ withLast app t r = 𝟙 _ := by
        apply Subtype.ext
        change nearProd_map m.val (𝟙 A) ≫ nearProd_map r.val (𝟙 A) = 𝟙 _
        have e : m.val ≫ r.val = 𝟙 _ := congrArg Subtype.val hmr
        rw [PCategory.nearProd_comp, e, Category.comp_id, PCategory.nearProd_id]
      refine ⟨withLast app t m ≫ encode, decode ≫ withLast app t r, ?_, ?_⟩
      · have total : isTotal (withLast app t m) :=
          Subtype.ext (isTotal_nearProd_map (congrArg Subtype.val hm) (PCategory.rst_id A))
        exact isTotal_comp total hencode
      · rw [Category.assoc, ← Category.assoc encode, cancel, Category.id_comp, lifts]
        rfl

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
