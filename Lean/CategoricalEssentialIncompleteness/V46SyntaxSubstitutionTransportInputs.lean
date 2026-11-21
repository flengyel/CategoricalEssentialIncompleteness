/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransport
public import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransportComponents
public import CategoricalEssentialIncompleteness.V46SyntaxOptionConstructorTransport
public import CategoricalEssentialIncompleteness.V46SyntaxOptionPullbackTransport

/-!
Parameter and original/result carrier comparisons for named substitution. Recursive
formula values use the option comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem substitutionProductIso_braiding {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    E.functor.map (prod.braiding X Y).hom ≫ (SyntaxOptionTransport.productIso E j i).hom =
      (SyntaxOptionTransport.productIso E i j).hom ≫ (prod.braiding X' Y').hom := by
  apply prod.hom_ext
  · calc
      _ = E.functor.map ((prod.braiding X Y).hom ≫ prod.fst) ≫ j.hom := by
        rw [Category.assoc,SyntaxOptionTransport.productIso_fst,
          ← Category.assoc,← E.functor.map_comp]
      _ = E.functor.map prod.snd ≫ j.hom := by simp only [prod.braiding_hom,prod.lift_fst]
      _ = (SyntaxOptionTransport.productIso E i j).hom ≫ prod.snd :=
        (SyntaxOptionTransport.productIso_snd E i j).symm
      _ = _ := by simp only [Category.assoc,prod.braiding_hom,prod.lift_fst]
  · calc
      _ = E.functor.map ((prod.braiding X Y).hom ≫ prod.snd) ≫ i.hom := by
        rw [Category.assoc,SyntaxOptionTransport.productIso_snd,
          ← Category.assoc,← E.functor.map_comp]
      _ = E.functor.map prod.fst ≫ i.hom := by simp only [prod.braiding_hom,prod.lift_snd]
      _ = (SyntaxOptionTransport.productIso E i j).hom ≫ prod.fst :=
        (SyntaxOptionTransport.productIso_fst E i j).symm
      _ = _ := by simp only [Category.assoc,prod.braiding_hom,prod.lift_snd]

/-- Both recursive sorts may have different carriers and different
isomorphisms. In particular the formula carrier retains failure. -/
def substitutionPolynomialIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p : SyntaxPolynomial D) :
    E.functor.obj ((p.mapCoefficients E.inverse.obj).eval.obj A) ≅
      (p.mapCoefficients id).eval.obj B :=
  SyntaxPolynomialTransport.component E E.inverse.obj id (fun X => E.counitIso.app X) p A ≪≫
    (p.mapCoefficients id).eval.mapIso i

def substitutionConstructorsInputIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (σ : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.obj A) ≅
      (SyntaxPolynomial.constructors σ d).eval.obj B := by
  simpa only [mapCoefficients_constructors,id_eq] using
    substitutionPolynomialIso E A B i (SyntaxPolynomial.constructors σ d)

def substitutionPowerInputIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p : SyntaxPolynomial D) (n : ℕ) :
    E.functor.obj ((SyntaxPolynomial.power (p.mapCoefficients E.inverse.obj) n).eval.obj A) ≅
      (SyntaxPolynomial.power (p.mapCoefficients id) n).eval.obj B := by
  simpa only [mapCoefficients_power] using
    substitutionPolynomialIso E A B i (SyntaxPolynomial.power p n)

def substitutionTermInputIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (V : D) (σ : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj A) ≅
      (SyntaxPolynomial.termExpression V σ d).eval.obj B := by
  simpa only [mapCoefficients_termExpression,id_eq] using
    substitutionPolynomialIso E A B i (SyntaxPolynomial.termExpression V σ d)

def substitutionFormulaInputIso (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (V : D) (π : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj A) ≅
      (SyntaxPolynomial.formulaExpression V π d).eval.obj B := by
  simpa only [mapCoefficients_formulaExpression,id_eq] using
    substitutionPolynomialIso E A B i (SyntaxPolynomial.formulaExpression V π d)

theorem substitutionTermInputIso_hom (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (V : D) (σ : ℕ → D) (d : ℕ) :
    (substitutionTermInputIso E A B i V σ d).hom = termInputMap E V σ d A B i.hom := by
  unfold substitutionTermInputIso
  erw [iso_cast_hom (termSourceObjectEquality E V σ d A).symm
    (congrArg (fun p => p.eval.obj B) (termTargetExpressionEquality V σ d))]
  simp only [substitutionPolynomialIso,termInputMap,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]

theorem substitutionFormulaInputIso_hom (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (V : D) (π : ℕ → D) (d : ℕ) :
    (substitutionFormulaInputIso E A B i V π d).hom = formulaInputMap E V π d A B i.hom := by
  unfold substitutionFormulaInputIso
  erw [iso_cast_hom (formulaSourceObjectEquality E V π d A).symm
    (congrArg (fun p => p.eval.obj B) (formulaTargetExpressionEquality V π d))]
  simp only [substitutionPolynomialIso,formulaInputMap,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]

/-- The polynomial comparison respects a square on recursive carriers; this is naturality,
with no assertion about a fold. -/
theorem substitutionPolynomialIso_natural {A A' : C × C} {B B' : D × D}
    (i : (E.prod E).functor.obj A ≅ B) (i' : (E.prod E).functor.obj A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B')
    (h : (E.prod E).functor.map f ≫ i'.hom = i.hom ≫ g) (p : SyntaxPolynomial D) :
    E.functor.map ((p.mapCoefficients E.inverse.obj).eval.map f) ≫
        (substitutionPolynomialIso E A' B' i' p).hom =
      (substitutionPolynomialIso E A B i p).hom ≫ (p.mapCoefficients id).eval.map g := by
  change E.functor.map ((p.mapCoefficients E.inverse.obj).eval.map f) ≫
    ((SyntaxPolynomialTransport.component E E.inverse.obj id _ p A').hom ≫
      (p.mapCoefficients id).eval.map i'.hom) = _
  rw [← Category.assoc,SyntaxPolynomialTransport.component_natural,Category.assoc,
    ← (p.mapCoefficients id).eval.map_comp,h,(p.mapCoefficients id).eval.map_comp]
  simp only [substitutionPolynomialIso,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]

@[reassoc] theorem substitutionPolynomialIso_inl (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    E.functor.map (coprod.inl : (p.mapCoefficients E.inverse.obj).eval.obj A ⟶
      (p.mapCoefficients E.inverse.obj).eval.obj A ⨿
        (q.mapCoefficients E.inverse.obj).eval.obj A) ≫
      (substitutionPolynomialIso E A B i (.sum p q)).hom =
        (substitutionPolynomialIso E A B i p).hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫
    ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.sum p q) A).hom ≫
      coprod.map _ _) = _
  rw [← Category.assoc,SyntaxPolynomialTransport.component_inl,Category.assoc,
    coprod.inl_map,← Category.assoc]
  rfl

@[reassoc] theorem substitutionPolynomialIso_inr (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    E.functor.map (coprod.inr : (q.mapCoefficients E.inverse.obj).eval.obj A ⟶
      (p.mapCoefficients E.inverse.obj).eval.obj A ⨿
        (q.mapCoefficients E.inverse.obj).eval.obj A) ≫
      (substitutionPolynomialIso E A B i (.sum p q)).hom =
        (substitutionPolynomialIso E A B i q).hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫
    ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.sum p q) A).hom ≫
      coprod.map _ _) = _
  rw [← Category.assoc,SyntaxPolynomialTransport.component_inr,Category.assoc,
    coprod.inr_map,← Category.assoc]
  rfl

@[reassoc] theorem substitutionPolynomialIso_fst (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    (substitutionPolynomialIso E A B i (.product p q)).hom ≫ prod.fst =
      E.functor.map prod.fst ≫ (substitutionPolynomialIso E A B i p).hom := by
  change ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.product p q) A).hom ≫
    prod.map _ _) ≫ prod.fst = _
  rw [Category.assoc,prod.map_fst,← Category.assoc,
    SyntaxPolynomialTransport.component_fst,Category.assoc]
  rfl

@[reassoc] theorem substitutionPolynomialIso_snd (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    (substitutionPolynomialIso E A B i (.product p q)).hom ≫ prod.snd =
      E.functor.map prod.snd ≫ (substitutionPolynomialIso E A B i q).hom := by
  change ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.product p q) A).hom ≫
    prod.map _ _) ≫ prod.snd = _
  rw [Category.assoc,prod.map_snd,← Category.assoc,
    SyntaxPolynomialTransport.component_snd,Category.assoc]
  rfl

@[simp] theorem substitutionPolynomialIso_term (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) :
    (substitutionPolynomialIso E A B i .term).hom = i.hom.1 := by
  simp [substitutionPolynomialIso,SyntaxPolynomialTransport.component,
    SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem substitutionPolynomialIso_formula (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) :
    (substitutionPolynomialIso E A B i .formula).hom = i.hom.2 := by
  simp [substitutionPolynomialIso,SyntaxPolynomialTransport.component,
    SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem substitutionPolynomialIso_coefficient (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (X : D) :
    (substitutionPolynomialIso E A B i (.coefficient X)).hom = (E.counitIso.app X).hom := by
  simp [substitutionPolynomialIso,SyntaxPolynomialTransport.component,
    SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

theorem substitutionPolynomialIso_product (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D) :
    (substitutionPolynomialIso E A B i (.product p q)).hom =
      (SyntaxOptionTransport.productIso E (substitutionPolynomialIso E A B i p)
        (substitutionPolynomialIso E A B i q)).hom := by
  apply prod.hom_ext
  · rw [substitutionPolynomialIso_fst,SyntaxOptionTransport.productIso_fst]
  · rw [substitutionPolynomialIso_snd,SyntaxOptionTransport.productIso_snd]

theorem substitution_summand_inl (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D)
    {Y : C} {Y' : D} (j : E.functor.obj Y ≅ Y')
    (s : ((SyntaxPolynomial.sum p q).mapCoefficients E.inverse.obj).eval.obj A ⟶ Y)
    (s' : ((SyntaxPolynomial.sum p q).mapCoefficients id).eval.obj B ⟶ Y')
    (hs : E.functor.map s ≫ j.hom = (substitutionPolynomialIso E A B i (.sum p q)).hom ≫ s') :
    E.functor.map (coprod.inl ≫ s) ≫ j.hom =
      (substitutionPolynomialIso E A B i p).hom ≫ coprod.inl ≫ s' := by
  rw [E.functor.map_comp,Category.assoc,hs,← Category.assoc,
    substitutionPolynomialIso_inl,Category.assoc]

theorem substitution_summand_inr (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B) (p q : SyntaxPolynomial D)
    {Y : C} {Y' : D} (j : E.functor.obj Y ≅ Y')
    (s : ((SyntaxPolynomial.sum p q).mapCoefficients E.inverse.obj).eval.obj A ⟶ Y)
    (s' : ((SyntaxPolynomial.sum p q).mapCoefficients id).eval.obj B ⟶ Y')
    (hs : E.functor.map s ≫ j.hom = (substitutionPolynomialIso E A B i (.sum p q)).hom ≫ s') :
    E.functor.map (coprod.inr ≫ s) ≫ j.hom =
      (substitutionPolynomialIso E A B i q).hom ≫ coprod.inr ≫ s' := by
  rw [E.functor.map_comp,Category.assoc,hs,← Category.assoc,
    substitutionPolynomialIso_inr,Category.assoc]

variable (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def substitutionParameterIso :
    E.functor.obj S₀.substitutionParameters ≅ S₁.substitutionParameters :=
  SyntaxOptionTransport.productIso E (E.counitIso.app V) (syntaxTermIso E V σ π d S₀ c)

def substitutionTermStateIso :
    E.functor.obj S₀.substitutionCarriers.1 ≅ S₁.substitutionCarriers.1 :=
  SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c)
    (syntaxTermIso E V σ π d S₀ c)

def substitutionFormulaStateIso :
    E.functor.obj S₀.substitutionCarriers.2 ≅ S₁.substitutionCarriers.2 :=
  SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c)
    (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c))

def substitutionStateIso :
    (E.prod E).functor.obj S₀.substitutionCarriers ≅ S₁.substitutionCarriers where
  hom := ((substitutionTermStateIso E V σ π d S₀ S₁ c).hom,
    (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom)
  inv := ((substitutionTermStateIso E V σ π d S₀ S₁ c).inv,
    (substitutionFormulaStateIso E V σ π d S₀ S₁ c).inv)
  hom_inv_id := Prod.ext (Iso.hom_inv_id _) (Iso.hom_inv_id _)
  inv_hom_id := Prod.ext (Iso.inv_hom_id _) (Iso.inv_hom_id _)

/-- The two original projections commute with the carrier comparisons. No identity of
syntax or state codes is assumed. -/
theorem substitutionOriginal_comparison :
    (E.prod E).functor.map S₀.originalProjection ≫ (syntaxCarrierIso E V σ π d S₀ c).hom =
      (substitutionStateIso E V σ π d S₀ S₁ c).hom ≫ S₁.originalProjection := by
  apply Prod.ext
  · exact (SyntaxOptionTransport.productIso_fst E
      (syntaxTermIso E V σ π d S₀ c) (syntaxTermIso E V σ π d S₀ c)).symm
  · exact (SyntaxOptionTransport.productIso_fst E
      (syntaxFormulaIso E V σ π d S₀ c)
      (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c))).symm

/-- The term-result projection and the original-formula projection are
the second natural pair used by the function and relation operations. -/
theorem substitutionTermResult_comparison :
    (E.prod E).functor.map S₀.termResultProjection ≫ (syntaxCarrierIso E V σ π d S₀ c).hom =
      (substitutionStateIso E V σ π d S₀ S₁ c).hom ≫ S₁.termResultProjection := by
  apply Prod.ext
  · exact (SyntaxOptionTransport.productIso_snd E
      (syntaxTermIso E V σ π d S₀ c) (syntaxTermIso E V σ π d S₀ c)).symm
  · exact (SyntaxOptionTransport.productIso_fst E
      (syntaxFormulaIso E V σ π d S₀ c)
      (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c))).symm

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
