/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationEncoderIsos
public import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding
public import CategoricalEssentialIncompleteness.V46CategoricalListLawsParameters
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints

/-! # Finite standard-model inputs and their actual parameterized points

Only interpreted standard points are used. No coefficient membership is
promoted to an internal PA global point.
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

namespace Standard
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

/-- Finite polynomial data consist of standard interpreted points. -/
def Data (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    SyntaxPolynomial (PredicateCategory 𝗣𝗔) → Type
  | .term => (N).obj X.1
  | .formula => (N).obj X.2
  | .coefficient C => (N).obj C
  | .unit => PUnit
  | .product p q => Data X p × Data X q
  | .sum p q => Sum (Data X p) (Data X q)

def realize (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) → Data X p → (N).obj (p.eval.obj X)
  | .term, z => z
  | .formula, z => z
  | .coefficient _, z => z
  | .unit, _ => SyntacticSyntax.modelTerminalPoint 𝗣𝗔 ℕ
  | .product p q, z => SyntacticLists.pairPoint 𝗣𝗔 ℕ (realize X p z.1) (realize X q z.2)
  | .sum p _, .inl z => (N).map coprod.inl (realize X p z)
  | .sum _ q, .inr z => (N).map coprod.inr (realize X q z)

def mapData {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : (N).obj X.1 → (N).obj Y.1) (g : (N).obj X.2 → (N).obj Y.2) :
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) → Data X p → Data Y p
  | .term, z => f z
  | .formula, z => g z
  | .coefficient _, z => z
  | .unit, z => z
  | .product p q, z => (mapData f g p z.1,mapData f g q z.2)
  | .sum p _, .inl z => .inl (mapData f g p z)
  | .sum _ q, .inr z => .inr (mapData f g q z)

def rawCode (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) → Data X p → ℕ
  | .term, z => z.val
  | .formula, z => z.val
  | .coefficient _, z => z.val
  | .unit, _ => 0
  | .product p q, z => Arithmetic.pair (rawCode X p z.1) (rawCode X q z.2)
  | .sum p _, .inl z => Arithmetic.pair (rawCode X p z) 0
  | .sum _ q, .inr z => Arithmetic.pair (rawCode X q z) 1

def powerData (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (n : ℕ) → (Fin n → (N).obj X.1) → Data X (SyntaxPolynomial.power .term n)
  | 0, _ => PUnit.unit
  | 1, f => f 0
  | n+2, f => (powerData X (n+1) (fun i => f i.castSucc),f (Fin.last (n+1)))

def arityData (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) (τ : ℕ → PredicateCategory 𝗣𝗔) :
    (d : ℕ) → (k : Fin (d+1)) → (N).obj (τ k.val) →
      (Fin k.val → (N).obj X.1) → Data X (SyntaxPolynomial.constructors τ d)
  | 0, k => by
      have hk : k=0 := Fin.eq_zero k
      subst k
      exact fun c _ => (c,PUnit.unit)
  | d+1, k => Fin.lastCases
      (fun c children => Sum.inr (c,powerData X (d+1) children))
      (fun j c children => Sum.inl (arityData X τ d j c children)) k

theorem powerData_rawCode (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (n : ℕ) (f : Fin n → (N).obj X.1) :
    rawCode X (SyntaxPolynomial.power .term n) (powerData X n f)=
      childTuple n (fun i => (f i).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp only [SyntaxPolynomial.power,powerData,rawCode,childTuple,ih]

theorem arityData_rawCode (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (τ : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (k : Fin (d+1)) (c : (N).obj (τ k.val))
    (f : Fin k.val → (N).obj X.1) :
    rawCode X (SyntaxPolynomial.constructors τ d) (arityData X τ d k c f)=
      arityInput d k (Arithmetic.pair c.val (childTuple k.val (fun i => (f i).val))) := by
  induction d with
  | zero =>
      have hk : k=0 := Fin.eq_zero k
      subst k
      rfl
  | succ d ih =>
      revert c f
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro c f
        simp only [arityData,Fin.lastCases_last,SyntaxPolynomial.constructors,rawCode,arityInput,powerData_rawCode]
        rfl
      · intro c f
        simp only [arityData,Fin.lastCases_castSucc,SyntaxPolynomial.constructors,rawCode,arityInput,ih]
        rfl

theorem mapData_powerData {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : (N).obj X.1 → (N).obj Y.1) (g : (N).obj X.2 → (N).obj Y.2)
    (n : ℕ) (children : Fin n → (N).obj X.1) :
    mapData f g (SyntaxPolynomial.power .term n) (powerData X n children)=
      powerData Y n (fun i => f (children i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp only [SyntaxPolynomial.power,powerData,mapData,ih]

theorem mapData_arityData {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : (N).obj X.1 → (N).obj Y.1) (g : (N).obj X.2 → (N).obj Y.2)
    (τ : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (k : Fin (d+1)) (c : (N).obj (τ k.val))
    (children : Fin k.val → (N).obj X.1) :
    mapData f g (SyntaxPolynomial.constructors τ d) (arityData X τ d k c children)=
      arityData Y τ d k c (fun i => f (children i)) := by
  induction d with
  | zero =>
      have hk : k=0 := Fin.eq_zero k
      subst k
      rfl
  | succ d ih =>
      revert c children
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro c children
        simp only [arityData,Fin.lastCases_last,SyntaxPolynomial.constructors,mapData,mapData_powerData]
        rfl
      · intro c children
        simp only [arityData,Fin.lastCases_castSucc,SyntaxPolynomial.constructors,mapData,ih]
        rfl

/-- The literal finite input code is compared with the actual PA chosen
polynomial object by its already proved representation graph. -/
theorem rawCode_represents (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (SyntacticSyntax.baseRepresentation 𝗣𝗔 X.1 X.2 p).val.Evalb
      ![rawCode X p z,(realize X p z).val] := by
  induction p with
  | term => exact (SyntacticSyntax.baseRepresentation_term_eval 𝗣𝗔 ℕ X.1 X.2 _ _).mpr ⟨z.property,rfl⟩
  | formula => exact (SyntacticSyntax.baseRepresentation_formula_eval 𝗣𝗔 ℕ X.1 X.2 _ _).mpr ⟨z.property,rfl⟩
  | coefficient C =>
      exact (SyntacticSyntax.baseRepresentation_coefficient_eval 𝗣𝗔 ℕ X.1 X.2 C _ _).mpr
        ⟨z.property,rfl⟩
  | unit =>
      exact (SyntacticSyntax.baseRepresentation_unit_eval 𝗣𝗔 ℕ X.1 X.2 _ _).mpr
        ⟨(SyntacticSyntax.modelTerminalPoint 𝗣𝗔 ℕ).property,rfl⟩
  | product p q hp hq =>
      apply (SyntacticSyntax.baseRepresentation_product_eval 𝗣𝗔 ℕ X.1 X.2 p q _ _).mpr
      refine ⟨_,_,_,_,rfl,hp z.1,hq z.2,?_,?_⟩
      · exact (SyntacticLists.chosenGraph_map_iff 𝗣𝗔 ℕ prod.fst _ _).mpr
          (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _)
      · exact (SyntacticLists.chosenGraph_map_iff 𝗣𝗔 ℕ prod.snd _ _).mpr
          (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _)
  | sum p q hp hq =>
      cases z with
      | inl x =>
          apply (SyntacticSyntax.baseRepresentation_sum_eval 𝗣𝗔 ℕ X.1 X.2 p q _ _).mpr
          exact Or.inl ⟨_,_,rfl,hp x,(SyntacticLists.chosenGraph_map_iff 𝗣𝗔 ℕ coprod.inl _ _).mpr rfl⟩
      | inr y =>
          apply (SyntacticSyntax.baseRepresentation_sum_eval 𝗣𝗔 ℕ X.1 X.2 p q _ _).mpr
          exact Or.inr ⟨_,_,rfl,hq y,(SyntacticLists.chosenGraph_map_iff 𝗣𝗔 ℕ coprod.inr _ _).mpr rfl⟩

def Fiber (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (A : Over R) :=
  {x : (N).obj A.left // (N).map A.hom x=r}

def fiberPair {R : PredicateCategory 𝗣𝗔} {r : (N).obj R}
    (A B : Over R) (x : Fiber R r A) (y : Fiber R r B) : Fiber R r (A ⨯ B) := by
  let h := SyntacticLists.modelOverProduct_exists 𝗣𝗔 ℕ A B x.val y.val
    (x.property.trans y.property.symm)
  let z := Classical.choose h
  have hz := Classical.choose_spec h
  refine ⟨z,?_⟩
  exact (SyntacticLists.over_value 𝗣𝗔 ℕ (prod.fst : A ⨯ B ⟶ A) z).symm.trans
    ((congrArg ((N).map A.hom) hz.1).trans x.property)

theorem fiberPair_fst {R : PredicateCategory 𝗣𝗔} {r : (N).obj R}
    (A B : Over R) (x : Fiber R r A) (y : Fiber R r B) :
    (N).map (prod.fst : A ⨯ B ⟶ A).left (fiberPair A B x y).val=x.val :=
  (Classical.choose_spec (SyntacticLists.modelOverProduct_exists 𝗣𝗔 ℕ A B x.val y.val
    (x.property.trans y.property.symm))).1

theorem fiberPair_snd {R : PredicateCategory 𝗣𝗔} {r : (N).obj R}
    (A B : Over R) (x : Fiber R r A) (y : Fiber R r B) :
    (N).map (prod.snd : A ⨯ B ⟶ B).left (fiberPair A B x y).val=y.val :=
  (Classical.choose_spec (SyntacticLists.modelOverProduct_exists 𝗣𝗔 ℕ A B x.val y.val
    (x.property.trans y.property.symm))).2

def fiberInl {R : PredicateCategory 𝗣𝗔} {r : (N).obj R}
    (A B : Over R) (x : Fiber R r A) : Fiber R r (A ⨿ B) :=
  ⟨(N).map (coprod.inl : A ⟶ A ⨿ B).left x.val,
    (SyntacticLists.over_value 𝗣𝗔 ℕ (coprod.inl : A ⟶ A ⨿ B) x.val).trans x.property⟩

def fiberInr {R : PredicateCategory 𝗣𝗔} {r : (N).obj R}
    (A B : Over R) (y : Fiber R r B) : Fiber R r (A ⨿ B) :=
  ⟨(N).map (coprod.inr : B ⟶ A ⨿ B).left y.val,
    (SyntacticLists.over_value 𝗣𝗔 ℕ (coprod.inr : B ⟶ A ⨿ B) y.val).trans y.property⟩

def liftData (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) → Data X p →
      Fiber R r ((p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2))
  | .term, z => ⟨SyntacticLists.pairPoint 𝗣𝗔 ℕ r z,SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ r z⟩
  | .formula, z => ⟨SyntacticLists.pairPoint 𝗣𝗔 ℕ r z,SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ r z⟩
  | .coefficient _, z => ⟨SyntacticLists.pairPoint 𝗣𝗔 ℕ r z,SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ r z⟩
  | .unit, _ => ⟨Classical.choose (SyntacticSyntax.modelOverTerminal_existsUnique 𝗣𝗔 ℕ R r),
      (Classical.choose_spec (SyntacticSyntax.modelOverTerminal_existsUnique 𝗣𝗔 ℕ R r)).1⟩
  | .product p q, z => fiberPair _ _ (liftData R r X p z.1) (liftData R r X q z.2)
  | .sum p _q, .inl z => fiberInl _ _ (liftData R r X p z)
  | .sum _p q, .inr z => fiberInr _ _ (liftData R r X q z)

theorem liftData_parameter (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (N).map ((p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)).hom
      (liftData R r X p z).val=r := (liftData R r X p z).property

/-- Only the standard interpreted value is read from a parameterized
polynomial point; its chosen code is retained in the actual point. -/
theorem liftData_value (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (N).map (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p)
      (liftData R r X p z).val=realize X p z := by
  induction p with
  | term =>
      rw [SyntacticSyntax.parameterValueMap_term]
      exact SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ r z
  | formula =>
      rw [SyntacticSyntax.parameterValueMap_formula]
      exact SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ r z
  | coefficient C =>
      rw [SyntacticSyntax.parameterValueMap_coefficient]
      exact SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ r z
  | unit => exact SyntacticDerivation.modelTerminal_ext 𝗣𝗔 ℕ _ _
  | product p q hp hq =>
      let A := (p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
      let B := (q.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
      let w : (N).obj (A ⨯ B).left := (liftData R r X (.product p q) z).val
      apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
      · have h := ConcreteNamedComparison.parameterPoint_product_fst 𝗣𝗔 ℕ R X.1 X.2 p q w
        have hw : (N).map (prod.fst : A ⨯ B ⟶ A).left w=(liftData R r X p z.1).val :=
          fiberPair_fst A B (liftData R r X p z.1) (liftData R r X q z.2)
        exact h.trans ((congrArg ((N).map (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p)) hw).trans
          ((hp z.1).trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _).symm))
      · have h := ConcreteNamedComparison.parameterPoint_product_snd 𝗣𝗔 ℕ R X.1 X.2 p q w
        have hw : (N).map (prod.snd : A ⨯ B ⟶ B).left w=(liftData R r X q z.2).val :=
          fiberPair_snd A B (liftData R r X p z.1) (liftData R r X q z.2)
        exact h.trans ((congrArg ((N).map (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 q)) hw).trans
          ((hq z.2).trans (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _).symm))
  | sum p q hp hq =>
      cases z with
      | inl x =>
          let A := (p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
          let B := (q.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
          have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ
            (coprod.inl : A ⟶ A ⨿ B).left (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 (.sum p q))
            (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p)
            (coprod.inl : p.eval.obj X ⟶ p.eval.obj X ⨿ q.eval.obj X)
            (SyntacticSyntax.parameterValueMap_sum_inl 𝗣𝗔 R X.1 X.2 p q) (liftData R r X p x).val
          exact h.trans (congrArg ((N).map (coprod.inl : p.eval.obj X ⟶ p.eval.obj X ⨿ q.eval.obj X)) (hp x))
      | inr y =>
          let A := (p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
          let B := (q.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
          have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ
            (coprod.inr : B ⟶ A ⨿ B).left (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 (.sum p q))
            (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 q)
            (coprod.inr : q.eval.obj X ⟶ p.eval.obj X ⨿ q.eval.obj X)
            (SyntacticSyntax.parameterValueMap_sum_inr 𝗣𝗔 R X.1 X.2 p q) (liftData R r X q y).val
          exact h.trans (congrArg ((N).map (coprod.inr : q.eval.obj X ⟶ p.eval.obj X ⨿ q.eval.obj X)) (hq y))

theorem liftData_comparison (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (N).map (SyntaxPolynomial.parameterComparison R X p).left (liftData R r X p z).val=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ r (realize X p z) := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · exact (SyntacticLists.over_value 𝗣𝗔 ℕ (SyntaxPolynomial.parameterComparison R X p)
      (liftData R r X p z).val).trans
        ((liftData_parameter R r X p z).trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _).symm)
  · exact (Functor.map_comp_apply (N) (SyntaxPolynomial.parameterComparison R X p).left
      (prod.snd : R ⨯ p.eval.obj X ⟶ _) (liftData R r X p z).val).symm.trans
        ((liftData_value R r X p z).trans (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _).symm)

def leafValue {R : PredicateCategory 𝗣𝗔} (r : (N).obj R)
    {X Y : PredicateCategory 𝗣𝗔} (f : constantFamily R X ⟶ constantFamily R Y)
    (x : (N).obj X) : (N).obj Y :=
  (N).map (prod.snd : R ⨯ Y ⟶ Y) ((N).map f.left (SyntacticLists.pairPoint 𝗣𝗔 ℕ r x))

theorem map_constant_point {R : PredicateCategory 𝗣𝗔} (r : (N).obj R)
    {X Y : PredicateCategory 𝗣𝗔} (f : constantFamily R X ⟶ constantFamily R Y)
    (x : (N).obj X) :
    (N).map f.left (SyntacticLists.pairPoint 𝗣𝗔 ℕ r x)=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ r (leafValue r f x) := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · exact (SyntacticLists.over_value 𝗣𝗔 ℕ f _).trans
      ((SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ r x).trans (SyntacticLists.pairPoint_fst 𝗣𝗔 ℕ _ _).symm)
  · exact (SyntacticLists.pairPoint_snd 𝗣𝗔 ℕ _ _).symm

/-- Source naturality is proved at standard interpreted points. In
particular, this does not manufacture an internal PA frame point. -/
theorem liftData_natural {R : PredicateCategory 𝗣𝗔} (r : (N).obj R)
    {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : (constantFamily R X.1,constantFamily R X.2) ⟶
      (constantFamily R Y.1,constantFamily R Y.2))
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Data X p) :
    (N).map ((p.withParameters R).eval.map f).left (liftData R r X p z).val=
      (liftData R r Y p (mapData (leafValue r f.1) (leafValue r f.2) p z)).val := by
  induction p with
  | term => exact map_constant_point r f.1 z
  | formula => exact map_constant_point r f.2 z
  | coefficient C =>
      change (N).map (𝟙 _) (SyntacticLists.pairPoint 𝗣𝗔 ℕ r z)=_
      rw [Functor.map_id_apply]
      rfl
  | unit =>
      change (N).map (𝟙 _) _=_
      rw [Functor.map_id_apply]
      rfl
  | product p q hp hq =>
      let A := (p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
      let B := (q.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)
      let C := (p.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2)
      let D := (q.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2)
      let fp : A ⟶ C := (p.withParameters R).eval.map f
      let fq : B ⟶ D := (q.withParameters R).eval.map f
      let w : (N).obj (A ⨯ B).left := (liftData R r X (.product p q) z).val
      apply SyntacticLists.modelOverProduct_ext 𝗣𝗔 ℕ
        C D
      · have hm := SyntacticLists.modelOverProduct_map_fst 𝗣𝗔 ℕ fp fq w
        have hs : (N).map (prod.fst : A ⨯ B ⟶ A).left w=(liftData R r X p z.1).val :=
          fiberPair_fst A B (liftData R r X p z.1) (liftData R r X q z.2)
        have ht := fiberPair_fst C D
          (liftData R r Y p (mapData (leafValue r f.1) (leafValue r f.2) p z.1))
          (liftData R r Y q (mapData (leafValue r f.1) (leafValue r f.2) q z.2))
        exact hm.trans ((congrArg ((N).map fp.left) hs).trans ((hp z.1).trans ht.symm))
      · have hm := SyntacticLists.modelOverProduct_map_snd 𝗣𝗔 ℕ fp fq w
        have hs : (N).map (prod.snd : A ⨯ B ⟶ B).left w=(liftData R r X q z.2).val :=
          fiberPair_snd A B (liftData R r X p z.1) (liftData R r X q z.2)
        have ht := fiberPair_snd C D
          (liftData R r Y p (mapData (leafValue r f.1) (leafValue r f.2) p z.1))
          (liftData R r Y q (mapData (leafValue r f.1) (leafValue r f.2) q z.2))
        exact hm.trans ((congrArg ((N).map fq.left) hs).trans ((hq z.2).trans ht.symm))
  | sum p q hp hq =>
      cases z with
      | inl x =>
          let fp := (p.withParameters R).eval.map f
          let fq := (q.withParameters R).eval.map f
          have hm := SyntacticSyntax.modelOverSum_map_inl 𝗣𝗔 ℕ fp fq (liftData R r X p x).val
          exact hm.trans (congrArg ((N).map (coprod.inl :
            (p.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2) ⟶
              (p.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2) ⨿
              (q.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2)).left) (hp x))
      | inr y =>
          let fp := (p.withParameters R).eval.map f
          let fq := (q.withParameters R).eval.map f
          have hm := SyntacticSyntax.modelOverSum_map_inr 𝗣𝗔 ℕ fp fq (liftData R r X q y).val
          exact hm.trans (congrArg ((N).map (coprod.inr :
            (q.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2) ⟶
              (p.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2) ⨿
              (q.withParameters R).eval.obj (constantFamily R Y.1,constantFamily R Y.2)).left) (hq y))

theorem operation_value (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    {W : PredicateCategory 𝗣𝗔} (v : R ⨯ p.eval.obj X ⟶ W) (z : Data X p) :
    (N).map (prod.snd : R ⨯ W ⟶ W)
      ((N).map (SyntaxPolynomial.parameterComparison R X p ≫ parameterHom v).left
        (liftData R r X p z).val)=
      (N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r (realize X p z)) := by
  have hp : (parameterHom v).left ≫ (prod.snd : R ⨯ W ⟶ W)=v := prod.lift_snd _ _
  have hc : (SyntaxPolynomial.parameterComparison R X p ≫ parameterHom v).left ≫ prod.snd=
      (SyntaxPolynomial.parameterComparison R X p).left ≫ v := by
    change ((SyntaxPolynomial.parameterComparison R X p).left ≫ (parameterHom v).left) ≫ prod.snd=_
    exact (Category.assoc _ _ _).trans (congrArg (fun arrow =>
      (SyntaxPolynomial.parameterComparison R X p).left ≫ arrow) hp)
  have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ
    (SyntaxPolynomial.parameterComparison R X p ≫ parameterHom v).left
    (prod.snd : R ⨯ W ⟶ W) (SyntaxPolynomial.parameterComparison R X p).left v hc
    (liftData R r X p z).val
  exact h.trans (congrArg ((N).map v) (liftData_comparison R r X p z))

theorem pure_operation_value (R : PredicateCategory 𝗣𝗔) (r : (N).obj R)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    {W : PredicateCategory 𝗣𝗔} (v : p.eval.obj X ⟶ W) (z : Data X p) :
    (N).map (prod.snd : R ⨯ W ⟶ W)
      ((N).map (SyntaxPolynomial.parameterComparison R X p ≫ (constantFamilyFunctor R).map v).left
        (liftData R r X p z).val)=(N).map v (realize X p z) := by
  have hp : ((constantFamilyFunctor R).map v).left ≫ (prod.snd : R ⨯ W ⟶ W)=
      (prod.snd : R ⨯ p.eval.obj X ⟶ p.eval.obj X) ≫ v := prod.map_snd _ _
  have hc : (SyntaxPolynomial.parameterComparison R X p ≫ (constantFamilyFunctor R).map v).left ≫
      (prod.snd : R ⨯ W ⟶ W)=SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p ≫ v := by
    change ((SyntaxPolynomial.parameterComparison R X p).left ≫ ((constantFamilyFunctor R).map v).left) ≫
      prod.snd=((SyntaxPolynomial.parameterComparison R X p).left ≫ prod.snd) ≫ v
    exact (Category.assoc _ _ _).trans ((congrArg (fun arrow =>
      (SyntaxPolynomial.parameterComparison R X p).left ≫ arrow) hp).trans (Category.assoc _ _ _).symm)
  have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ
    (SyntaxPolynomial.parameterComparison R X p ≫ (constantFamilyFunctor R).map v).left
    (prod.snd : R ⨯ W ⟶ W) (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p) v hc
    (liftData R r X p z).val
  exact h.trans (congrArg ((N).map v) (liftData_value R r X p z))

theorem map_pair {A B C D : PredicateCategory 𝗣𝗔} (f : A ⟶ C) (g : B ⟶ D)
    (a : (N).obj A) (b : (N).obj B) :
    (N).map (prod.map f g) (SyntacticLists.pairPoint 𝗣𝗔 ℕ a b)=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ ((N).map f a) ((N).map g b) := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · rw [← Functor.map_comp_apply,prod.map_fst,Functor.map_comp_apply,
      SyntacticLists.pairPoint_fst,SyntacticLists.pairPoint_fst]
  · rw [← Functor.map_comp_apply,prod.map_snd,Functor.map_comp_apply,
      SyntacticLists.pairPoint_snd,SyntacticLists.pairPoint_snd]

theorem braid_pair {A B : PredicateCategory 𝗣𝗔} (a : (N).obj A) (b : (N).obj B) :
    (N).map (prod.braiding A B).hom (SyntacticLists.pairPoint 𝗣𝗔 ℕ a b)=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ b a := by
  apply SyntacticLists.modelProduct_ext 𝗣𝗔 ℕ
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_fst,
      SyntacticLists.pairPoint_snd,SyntacticLists.pairPoint_fst]
  · rw [← Functor.map_comp_apply,prod.braiding_hom,prod.lift_snd,
      SyntacticLists.pairPoint_fst,SyntacticLists.pairPoint_snd]

end Standard

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
