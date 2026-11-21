/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageDecoding
public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionBranches

/-! # Finite polynomial inputs at a fixed uniform parameter

The recursive leaves are morphisms in the parameter slice. Coefficients remain points
of their original objects. Realization uses ordered products and coproduct injections
and commutes with the polynomial action on morphisms, including powers and arity zero.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding

section Geometry
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)

/-- Evaluate the represented global point only in the uniform target.
No PA global point is inferred from standard coefficient membership. -/
theorem at_point {X : Total.TotalCategory P} (x : (U).obj X) :
    (U).map (Total.underlyingPoint x) ⟨0,rfl⟩=x := by
  apply Subtype.ext
  exact Part.mem_unique (Total.totalFunction_mem (Total.underlyingPoint x) ⟨0,rfl⟩)
    (Part.eq_some_iff.mp (Total.underlyingPoint_value x 0 rfl))

end Geometry

namespace PointFrame
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)

/-- The source of a point calculation in the parameter slice. -/
def source (R : Total.TotalCategory P) (r : (U).obj R) : Over R :=
  Over.mk (Total.underlyingPoint r)

theorem point_natural {X Y : Total.TotalCategory P}
    (f : X ⟶ Y) (x : (U).obj X) :
    Total.underlyingPoint ((U).map f x)=Total.underlyingPoint x ≫ f :=
  ConcreteCategory.congr_hom ((Total.underlyingHomComparison (P := P)).hom.naturality f) x

/-- A point of an arbitrary family over the fixed frame gives a slice morphism. Only a
point of the uniform target is used here. -/
def family (R : Total.TotalCategory P) (r : (U).obj R)
    (X : Over R) (x : (U).obj X.left) (hx : (U).map X.hom x=r) : source R r ⟶ X :=
  Over.homMk (Total.underlyingPoint x)
    ((point_natural X.hom x).symm.trans (congrArg Total.underlyingPoint hx))

theorem family_point (R : Total.TotalCategory P) (r : (U).obj R)
    (X : Over R) (x : (U).obj X.left) (hx : (U).map X.hom x=r) :
    (U).map (family R r X x hx).left ⟨0,rfl⟩=x := at_point x

def constant (R : Total.TotalCategory P) (r : (U).obj R)
    (X : Total.TotalCategory P) (x : (U).obj X) : source R r ⟶ constantFamily R X :=
  Over.homMk (prod.lift (Total.underlyingPoint r) (Total.underlyingPoint x)) (by
    change prod.lift (Total.underlyingPoint r) (Total.underlyingPoint x) ≫ prod.fst=
      Total.underlyingPoint r
    exact prod.lift_fst _ _)

theorem constant_point (R : Total.TotalCategory P) (r : (U).obj R)
    (X : Total.TotalCategory P) (x : (U).obj X) :
    (U).map (constant R r X x).left ⟨0,rfl⟩=Points.pairPoint r x := by
  change (U).map (prod.lift (Total.underlyingPoint r) (Total.underlyingPoint x)) ⟨0,rfl⟩=_
  exact (Points.lift_point _ _ _).trans (congrArg₂ Points.pairPoint (at_point r) (at_point x))

/-- Finite constructor data at one fixed frame. Coefficients retain their own target
points; recursive leaves are slice morphisms. -/
def Data (R : Total.TotalCategory P) (r : (U).obj R) (A : Over R × Over R) :
    SyntaxPolynomial (Total.TotalCategory P) → Type
  | .term => source R r ⟶ A.1
  | .formula => source R r ⟶ A.2
  | .coefficient C => (U).obj C
  | .unit => PUnit
  | .product p q => Data R r A p × Data R r A q
  | .sum p q => Sum (Data R r A p) (Data R r A q)

def realize (R : Total.TotalCategory P) (r : (U).obj R) (A : Over R × Over R) :
    (p : SyntaxPolynomial (Total.TotalCategory P)) →
      Data R r A p → (source R r ⟶ (p.withParameters R).eval.obj A)
  | .term, f => f
  | .formula, f => f
  | .coefficient C, x => constant R r C x
  | .unit, _ => terminal.from _
  | .product p q, z => prod.lift (realize R r A p z.1) (realize R r A q z.2)
  | .sum p _, .inl x => realize R r A p x ≫ coprod.inl
  | .sum _ q, .inr y => realize R r A q y ≫ coprod.inr

def mapData (R : Total.TotalCategory P) (r : (U).obj R)
    {A B : Over R × Over R} (f : A ⟶ B) :
    (p : SyntaxPolynomial (Total.TotalCategory P)) → Data R r A p → Data R r B p
  | .term, z => z ≫ f.1
  | .formula, z => z ≫ f.2
  | .coefficient _, z => z
  | .unit, z => z
  | .product p q, z => (mapData R r f p z.1,mapData R r f q z.2)
  | .sum p _, .inl z => .inl (mapData R r f p z)
  | .sum _ q, .inr z => .inr (mapData R r f q z)

/-- The existing ordered finite-power convention, with no chosen
pullback-point code introduced for its entries. -/
def powerData (R : Total.TotalCategory P) (r : (U).obj R) (A : Over R × Over R) :
    (n : ℕ) → (Fin n → (source R r ⟶ A.1)) →
      Data R r A (SyntaxPolynomial.power .term n)
  | 0, _ => PUnit.unit
  | 1, f => f 0
  | n+2, f => (powerData R r A (n+1) (fun i => f i.castSucc),f (Fin.last (n+1)))

/-- The selected arity and label are retained, including arity zero. -/
def arityData (R : Total.TotalCategory P) (r : (U).obj R) (A : Over R × Over R)
    (τ : ℕ → Total.TotalCategory P) :
    (d : ℕ) → (k : Fin (d+1)) → (U).obj (τ k.val) →
      (Fin k.val → (source R r ⟶ A.1)) → Data R r A (SyntaxPolynomial.constructors τ d)
  | 0, k => by
      have hk : k=0 := Fin.eq_zero k
      subst k
      exact fun c _ => (c,PUnit.unit)
  | d+1, k => Fin.lastCases
      (fun c f => Sum.inr (c,powerData R r A (d+1) f))
      (fun j c f => Sum.inl (arityData R r A τ d j c f)) k

theorem powerData_natural (R : Total.TotalCategory P) (r : (U).obj R)
    {A B : Over R × Over R} (f : A ⟶ B) (n : ℕ)
    (children : Fin n → (source R r ⟶ A.1)) :
    mapData R r f (SyntaxPolynomial.power .term n) (powerData R r A n children)=
      powerData R r B n (fun i => children i ≫ f.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change (mapData R r f (SyntaxPolynomial.power .term (n+1))
            (powerData R r A (n+1) (fun i => children i.castSucc)),
              children (Fin.last (n+1)) ≫ f.1)=_
          rw [ih]
          rfl

theorem arityData_natural (R : Total.TotalCategory P) (r : (U).obj R)
    {A B : Over R × Over R} (f : A ⟶ B) (τ : ℕ → Total.TotalCategory P)
    (d : ℕ) (k : Fin (d+1)) (c : (U).obj (τ k.val))
    (children : Fin k.val → (source R r ⟶ A.1)) :
    mapData R r f (SyntaxPolynomial.constructors τ d) (arityData R r A τ d k c children)=
      arityData R r B τ d k c (fun i => children i ≫ f.1) := by
  induction d with
  | zero =>
      have hk : k=0 := Fin.eq_zero k
      subst k
      rfl
  | succ d ih =>
      revert c children
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro c children
        simp only [arityData,Fin.lastCases_last]
        change Sum.inr (c,mapData R r f (SyntaxPolynomial.power .term (d+1))
          (powerData R r A (d+1) children))=_
        rw [powerData_natural]
        rfl
      · intro c children
        simp only [arityData,Fin.lastCases_castSucc]
        change Sum.inl (mapData R r f (SyntaxPolynomial.constructors τ d)
          (arityData R r A τ d j c children))=_
        rw [ih]
        rfl

/-- Polynomial action on the finite input is derived from its products and injections. No
source-to-target slice chart is involved. -/
theorem realize_natural (R : Total.TotalCategory P) (r : (U).obj R)
    {A B : Over R × Over R} (f : A ⟶ B)
    (p : SyntaxPolynomial (Total.TotalCategory P)) (z : Data R r A p) :
    realize R r A p z ≫ (p.withParameters R).eval.map f=
      realize R r B p (mapData R r f p z) := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient C =>
      change constant R r C z ≫ 𝟙 _=constant R r C z
      exact Category.comp_id _
  | unit =>
      change terminal.from (source R r) ≫ 𝟙 _=terminal.from (source R r)
      exact Category.comp_id _
  | product p q hp hq =>
      change prod.lift (realize R r A p z.1) (realize R r A q z.2) ≫
        prod.map ((p.withParameters R).eval.map f) ((q.withParameters R).eval.map f)=_
      rw [prod.lift_map,hp,hq]
      rfl
  | sum p q hp hq =>
      cases z with
      | inl x =>
          change (realize R r A p x ≫ coprod.inl) ≫
            coprod.map ((p.withParameters R).eval.map f) ((q.withParameters R).eval.map f)=_
          rw [Category.assoc,coprod.inl_map,← Category.assoc,hp]
          rfl
      | inr y =>
          change (realize R r A q y ≫ coprod.inr) ≫
            coprod.map ((p.withParameters R).eval.map f) ((q.withParameters R).eval.map f)=_
          rw [Category.assoc,coprod.inr_map,← Category.assoc,hq]
          rfl

theorem realize_map_point (R : Total.TotalCategory P) (r : (U).obj R)
    {A B : Over R × Over R} (f : A ⟶ B)
    (p : SyntaxPolynomial (Total.TotalCategory P)) (z : Data R r A p) :
    (U).map ((p.withParameters R).eval.map f).left
      ((U).map (realize R r A p z).left ⟨0,rfl⟩)=
        (U).map (realize R r B p (mapData R r f p z)).left ⟨0,rfl⟩ := by
  have h := congrArg (fun k : source R r ⟶ (p.withParameters R).eval.obj B =>
    (U).map k.left ⟨0,rfl⟩) (realize_natural R r f p z)
  simpa only [Over.comp_left,CategoryTheory.Functor.map_comp_apply] using h

end PointFrame

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
