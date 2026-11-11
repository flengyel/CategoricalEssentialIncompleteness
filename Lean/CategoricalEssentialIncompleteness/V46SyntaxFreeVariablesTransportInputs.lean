/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialNormalization

/-! # The actual polynomial input isomorphisms for occurrence folds -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {X : C} {Y : D} (ℓ : E.functor.obj X ≅ Y)

omit [Regular C] [Regular D] in
def sumInputIso {A B : C} {A' B' : D} (a : E.functor.obj A ≅ A') (b : E.functor.obj B ≅ B') :
    E.functor.obj (A ⨿ B) ≅ A' ⨿ B' :=
  (asIso (coprodComparison E.functor A B)).symm ≪≫ coprod.mapIso a b

omit [Regular C] [Regular D] in
@[reassoc] theorem sumInputIso_inl {A B : C} {A' B' : D}
    (a : E.functor.obj A ≅ A') (b : E.functor.obj B ≅ B') :
    E.functor.map (coprod.inl : A ⟶ A ⨿ B) ≫ (sumInputIso E a b).hom = a.hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫ (inv (coprodComparison E.functor A B) ≫ coprod.map a.hom b.hom) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]

omit [Regular C] [Regular D] in
@[reassoc] theorem sumInputIso_inr {A B : C} {A' B' : D}
    (a : E.functor.obj A ≅ A') (b : E.functor.obj B ≅ B') :
    E.functor.map (coprod.inr : B ⟶ A ⨿ B) ≫ (sumInputIso E a b).hom = b.hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫ (inv (coprodComparison E.functor A B) ≫ coprod.map a.hom b.hom) = _
  rw [← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

def listPairIso : (E.prod E).functor.obj (X,X) ≅ (Y,Y) where
  hom := (ℓ.hom,ℓ.hom)
  inv := (ℓ.inv,ℓ.inv)
  hom_inv_id := Prod.ext ℓ.hom_inv_id ℓ.hom_inv_id
  inv_hom_id := Prod.ext ℓ.inv_hom_id ℓ.inv_hom_id

/-- This is the existing polynomial component followed by its actual
action on the pair of list-carrier isomorphisms. -/
def listInputIso (p : SyntaxPolynomial D) :
    E.functor.obj ((p.mapCoefficients E.inverse.obj).eval.obj (X,X)) ≅
      (p.mapCoefficients id).eval.obj (Y,Y) :=
  SyntaxPolynomialTransport.component E E.inverse.obj id (fun A => E.counitIso.app A) p (X,X) ≪≫
    (p.mapCoefficients id).eval.mapIso (listPairIso E ℓ)

@[reassoc] theorem listInputIso_inl (p q : SyntaxPolynomial D) :
    E.functor.map (coprod.inl : (p.mapCoefficients E.inverse.obj).eval.obj (X,X) ⟶
      (p.mapCoefficients E.inverse.obj).eval.obj (X,X) ⨿
        (q.mapCoefficients E.inverse.obj).eval.obj (X,X)) ≫
      (listInputIso E ℓ (.sum p q)).hom = (listInputIso E ℓ p).hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫
    ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.sum p q) (X,X)).hom ≫ coprod.map _ _) = _
  rw [← Category.assoc,SyntaxPolynomialTransport.component_inl,Category.assoc,coprod.inl_map,← Category.assoc]
  rfl

@[reassoc] theorem listInputIso_inr (p q : SyntaxPolynomial D) :
    E.functor.map (coprod.inr : (q.mapCoefficients E.inverse.obj).eval.obj (X,X) ⟶
      (p.mapCoefficients E.inverse.obj).eval.obj (X,X) ⨿
        (q.mapCoefficients E.inverse.obj).eval.obj (X,X)) ≫
      (listInputIso E ℓ (.sum p q)).hom = (listInputIso E ℓ q).hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫
    ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.sum p q) (X,X)).hom ≫ coprod.map _ _) = _
  rw [← Category.assoc,SyntaxPolynomialTransport.component_inr,Category.assoc,coprod.inr_map,← Category.assoc]
  rfl

@[reassoc] theorem listInputIso_fst (p q : SyntaxPolynomial D) :
    (listInputIso E ℓ (.product p q)).hom ≫ prod.fst =
      E.functor.map prod.fst ≫ (listInputIso E ℓ p).hom := by
  change ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.product p q) (X,X)).hom ≫ prod.map _ _) ≫
    prod.fst = _
  rw [Category.assoc,prod.map_fst,← Category.assoc,SyntaxPolynomialTransport.component_fst,Category.assoc]
  rfl

@[reassoc] theorem listInputIso_snd (p q : SyntaxPolynomial D) :
    (listInputIso E ℓ (.product p q)).hom ≫ prod.snd =
      E.functor.map prod.snd ≫ (listInputIso E ℓ q).hom := by
  change ((SyntaxPolynomialTransport.component E E.inverse.obj id _ (.product p q) (X,X)).hom ≫ prod.map _ _) ≫
    prod.snd = _
  rw [Category.assoc,prod.map_snd,← Category.assoc,SyntaxPolynomialTransport.component_snd,Category.assoc]
  rfl

theorem listInputIso_product (p q : SyntaxPolynomial D) :
    (listInputIso E ℓ (.product p q)).hom =
      (SyntaxOptionTransport.productIso E (listInputIso E ℓ p) (listInputIso E ℓ q)).hom := by
  apply prod.hom_ext
  · rw [listInputIso_fst,SyntaxOptionTransport.productIso_fst]
  · rw [listInputIso_snd,SyntaxOptionTransport.productIso_snd]

theorem listInputIso_sum (p q : SyntaxPolynomial D) :
    (listInputIso E ℓ (.sum p q)).hom = (sumInputIso E (listInputIso E ℓ p) (listInputIso E ℓ q)).hom := by
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit E.functor
      ((p.mapCoefficients E.inverse.obj).eval.obj (X,X))
      ((q.mapCoefficients E.inverse.obj).eval.obj (X,X)))
  · exact (listInputIso_inl E ℓ p q).trans (sumInputIso_inl E _ _).symm
  · exact (listInputIso_inr E ℓ p q).trans (sumInputIso_inr E _ _).symm

@[simp] theorem listInputIso_term : (listInputIso E ℓ .term).hom = ℓ.hom := by
  simp [listInputIso,SyntaxPolynomialTransport.component,SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval,listPairIso]

@[simp] theorem listInputIso_formula : (listInputIso E ℓ .formula).hom = ℓ.hom := by
  simp [listInputIso,SyntaxPolynomialTransport.component,SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval,listPairIso]

@[simp] theorem listInputIso_coefficient (A : D) :
    (listInputIso E ℓ (.coefficient A)).hom = (E.counitIso.app A).hom := by
  simp [listInputIso,SyntaxPolynomialTransport.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem listInputIso_unit :
    (listInputIso E ℓ .unit).hom = terminalComparison E.functor := by
  simp [listInputIso,SyntaxPolynomialTransport.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

def normalizedListInputIso (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C)
    (h₀ : p₀ = p.mapCoefficients E.inverse.obj) :
    E.functor.obj (p₀.eval.obj (X,X)) ≅ p.eval.obj (Y,Y) :=
  normalizedPolynomialIso E (X,X) (Y,Y) (listPairIso E ℓ) p p₀ p h₀ (SyntacticSyntax.mapCoefficients_id p)

theorem normalizedListInputIso_product (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C)
    (hp : p₀ = p.mapCoefficients E.inverse.obj) (hq : q₀ = q.mapCoefficients E.inverse.obj) :
    (normalizedListInputIso E ℓ (.product p q) (.product p₀ q₀)
      (congrArg₂ SyntaxPolynomial.product hp hq)).hom =
      (SyntaxOptionTransport.productIso E
        (normalizedListInputIso E ℓ p p₀ hp) (normalizedListInputIso E ℓ q q₀ hq)).hom :=
  normalizedPolynomialIso_product E (X,X) (Y,Y) (listPairIso E ℓ) p q p₀ q₀ p q hp hq
    (SyntacticSyntax.mapCoefficients_id p) (SyntacticSyntax.mapCoefficients_id q)

theorem normalizedListInputIso_sum (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C)
    (hp : p₀ = p.mapCoefficients E.inverse.obj) (hq : q₀ = q.mapCoefficients E.inverse.obj) :
    (normalizedListInputIso E ℓ (.sum p q) (.sum p₀ q₀)
      (congrArg₂ SyntaxPolynomial.sum hp hq)).hom =
      (sumInputIso E (normalizedListInputIso E ℓ p p₀ hp) (normalizedListInputIso E ℓ q q₀ hq)).hom :=
  normalizedPolynomialIso_sum E (X,X) (Y,Y) (listPairIso E ℓ) p q p₀ q₀ p q hp hq
    (SyntacticSyntax.mapCoefficients_id p) (SyntacticSyntax.mapCoefficients_id q)

theorem normalizedListInputIso_product_iso (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C)
    (hp : p₀ = p.mapCoefficients E.inverse.obj) (hq : q₀ = q.mapCoefficients E.inverse.obj) :
    normalizedListInputIso E ℓ (.product p q) (.product p₀ q₀)
      (congrArg₂ SyntaxPolynomial.product hp hq) =
      SyntaxOptionTransport.productIso E
        (normalizedListInputIso E ℓ p p₀ hp) (normalizedListInputIso E ℓ q q₀ hq) :=
  Iso.ext (normalizedListInputIso_product E ℓ p q p₀ q₀ hp hq)

theorem normalizedListInputIso_sum_iso (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C)
    (hp : p₀ = p.mapCoefficients E.inverse.obj) (hq : q₀ = q.mapCoefficients E.inverse.obj) :
    normalizedListInputIso E ℓ (.sum p q) (.sum p₀ q₀)
      (congrArg₂ SyntaxPolynomial.sum hp hq) =
      sumInputIso E (normalizedListInputIso E ℓ p p₀ hp) (normalizedListInputIso E ℓ q q₀ hq) :=
  Iso.ext (normalizedListInputIso_sum E ℓ p q p₀ q₀ hp hq)

@[simp] theorem normalizedListInputIso_term :
    normalizedListInputIso E ℓ .term .term rfl = ℓ := by
  apply Iso.ext
  exact normalizedPolynomialIso_term E (X,X) (Y,Y) (listPairIso E ℓ)

@[simp] theorem normalizedListInputIso_formula :
    normalizedListInputIso E ℓ .formula .formula rfl = ℓ := by
  apply Iso.ext
  exact normalizedPolynomialIso_formula E (X,X) (Y,Y) (listPairIso E ℓ)

@[simp] theorem normalizedListInputIso_coefficient (A : D) :
    normalizedListInputIso E ℓ (.coefficient A) (.coefficient (E.inverse.obj A)) rfl = E.counitIso.app A := by
  apply Iso.ext
  exact normalizedPolynomialIso_coefficient E (X,X) (Y,Y) (listPairIso E ℓ) A

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
theorem powerSourceEquality (n : ℕ) :
    SyntaxPolynomial.power (.term : SyntaxPolynomial C) n =
      (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).mapCoefficients E.inverse.obj := by
  simp only [mapCoefficients_power,SyntaxPolynomial.mapCoefficients]

def powerInputIso (n : ℕ) :
    E.functor.obj ((SyntaxPolynomial.power (.term : SyntaxPolynomial C) n).eval.obj (X,X)) ≅
      (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.obj (Y,Y) :=
  normalizedListInputIso E ℓ (SyntaxPolynomial.power .term n) (SyntaxPolynomial.power .term n)
    (powerSourceEquality E n)

@[simp] theorem powerInputIso_zero : (powerInputIso E ℓ 0).hom = terminalComparison E.functor := by
  simp [powerInputIso,SyntaxPolynomial.power,normalizedListInputIso,normalizedPolynomialIso,
    substitutionPolynomialIso,SyntaxPolynomialTransport.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem powerInputIso_one : (powerInputIso E ℓ 1).hom = ℓ.hom := by
  simp only [powerInputIso,SyntaxPolynomial.power,normalizedListInputIso_term]

theorem powerInputIso_step (n : ℕ) :
    (powerInputIso E ℓ (n+2)).hom =
      (SyntaxOptionTransport.productIso E (powerInputIso E ℓ (n+1)) ℓ).hom := by
  have h := normalizedListInputIso_product E ℓ
    (SyntaxPolynomial.power .term (n+1)) .term (SyntaxPolynomial.power .term (n+1)) .term
    (powerSourceEquality E (n+1)) rfl
  simpa only [powerInputIso,SyntaxPolynomial.power,normalizedListInputIso_term] using h

@[reassoc] theorem powerInputIso_fst (n : ℕ) :
    (powerInputIso E ℓ (n+2)).hom ≫ prod.fst =
      E.functor.map prod.fst ≫ (powerInputIso E ℓ (n+1)).hom := by
  rw [powerInputIso_step]
  exact SyntaxOptionTransport.productIso_fst E (powerInputIso E ℓ (n+1)) ℓ

@[reassoc] theorem powerInputIso_snd (n : ℕ) :
    (powerInputIso E ℓ (n+2)).hom ≫ prod.snd = E.functor.map prod.snd ≫ ℓ.hom := by
  rw [powerInputIso_step]
  exact SyntaxOptionTransport.productIso_snd E (powerInputIso E ℓ (n+1)) ℓ

theorem powerInputIso_two : (powerInputIso E ℓ 2).hom = (SyntaxOptionTransport.productIso E ℓ ℓ).hom := by
  have h := powerInputIso_step E ℓ 0
  simpa only [powerInputIso,SyntaxPolynomial.power,normalizedListInputIso_term] using h

def symbolInputIso (A : D) (n : ℕ) :
    E.functor.obj (E.inverse.obj A ⨯
      (SyntaxPolynomial.power (.term : SyntaxPolynomial C) n).eval.obj (X,X)) ≅
      A ⨯ (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.obj (Y,Y) :=
  SyntaxOptionTransport.productIso E (E.counitIso.app A) (powerInputIso E ℓ n)

theorem normalizedListInputIso_symbol (A : D) (n : ℕ) :
    (normalizedListInputIso E ℓ (.product (.coefficient A) (SyntaxPolynomial.power .term n))
      (.product (.coefficient (E.inverse.obj A)) (SyntaxPolynomial.power .term n))
      (congrArg₂ SyntaxPolynomial.product rfl (powerSourceEquality E n))).hom =
        (symbolInputIso E ℓ A n).hom := by
  have h := normalizedListInputIso_product E ℓ (.coefficient A) (SyntaxPolynomial.power .term n)
    (.coefficient (E.inverse.obj A)) (SyntaxPolynomial.power .term n) rfl (powerSourceEquality E n)
  simpa only [normalizedListInputIso_coefficient,symbolInputIso,powerInputIso] using h

@[reassoc] theorem symbolInputIso_snd (A : D) (n : ℕ) :
    (symbolInputIso E ℓ A n).hom ≫ prod.snd =
      E.functor.map prod.snd ≫ (powerInputIso E ℓ n).hom :=
  SyntaxOptionTransport.productIso_snd E (E.counitIso.app A) (powerInputIso E ℓ n)

def constructorInputIso (σ : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.obj (X,X)) ≅
      (SyntaxPolynomial.constructors σ d).eval.obj (Y,Y) :=
  normalizedListInputIso E ℓ (SyntaxPolynomial.constructors σ d)
    (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    (mapCoefficients_constructors E.inverse.obj σ d).symm

theorem constructorInputIso_zero (σ : ℕ → D) :
    (constructorInputIso E ℓ σ 0).hom = (symbolInputIso E ℓ (σ 0) 0).hom :=
  normalizedListInputIso_symbol E ℓ (σ 0) 0

theorem constructorInputIso_step (σ : ℕ → D) (n : ℕ) :
    (constructorInputIso E ℓ σ (n+1)).hom =
      (sumInputIso E (constructorInputIso E ℓ σ n) (symbolInputIso E ℓ (σ (n+1)) (n+1))).hom := by
  have h := normalizedListInputIso_sum E ℓ
    (SyntaxPolynomial.constructors σ n)
    (.product (.coefficient (σ (n+1))) (SyntaxPolynomial.power .term (n+1)))
    (SyntaxPolynomial.constructors (fun k => E.inverse.obj (σ k)) n)
    (.product (.coefficient (E.inverse.obj (σ (n+1)))) (SyntaxPolynomial.power .term (n+1)))
    (mapCoefficients_constructors E.inverse.obj σ n).symm
    (congrArg₂ SyntaxPolynomial.product rfl (powerSourceEquality E (n+1)))
  simpa only [constructorInputIso,SyntaxPolynomial.constructors,normalizedListInputIso_symbol,
    sumInputIso,Iso.trans_hom,coprod.mapIso_hom,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,Functor.const_obj_obj] using h

@[reassoc] theorem constructorInputIso_inl (σ : ℕ → D) (n : ℕ) :
    E.functor.map coprod.inl ≫ (constructorInputIso E ℓ σ (n+1)).hom =
      (constructorInputIso E ℓ σ n).hom ≫ coprod.inl := by
  rw [constructorInputIso_step,sumInputIso_inl]
  rfl

@[reassoc] theorem constructorInputIso_inr (σ : ℕ → D) (n : ℕ) :
    E.functor.map coprod.inr ≫ (constructorInputIso E ℓ σ (n+1)).hom =
      (symbolInputIso E ℓ (σ (n+1)) (n+1)).hom ≫ coprod.inr := by
  rw [constructorInputIso_step,sumInputIso_inr]

def termInputIso (V : D) (σ : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj (X,X)) ≅
      (SyntaxPolynomial.termExpression V σ d).eval.obj (Y,Y) :=
  normalizedListInputIso E ℓ (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm

theorem termInputIso_sum (V : D) (σ : ℕ → D) (d : ℕ) :
    (termInputIso E ℓ V σ d).hom =
      (sumInputIso E (E.counitIso.app V) (constructorInputIso E ℓ σ d)).hom := by
  have h := normalizedListInputIso_sum E ℓ (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient (E.inverse.obj V)) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    rfl (mapCoefficients_constructors E.inverse.obj σ d).symm
  simpa only [termInputIso,SyntaxPolynomial.termExpression,constructorInputIso,
    normalizedListInputIso_coefficient] using h

def formulaInputIso (V : D) (π : ℕ → D) (d : ℕ) :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj (X,X)) ≅
      (SyntaxPolynomial.formulaExpression V π d).eval.obj (Y,Y) :=
  normalizedListInputIso E ℓ (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm

theorem formulaInputIso_sum (V : D) (π : ℕ → D) (d : ℕ) :
    (formulaInputIso E ℓ V π d).hom =
      (sumInputIso E
        (sumInputIso E
          (sumInputIso E
            (sumInputIso E (SyntaxOptionTransport.productIso E ℓ ℓ) (constructorInputIso E ℓ π d)) ℓ)
          (SyntaxOptionTransport.productIso E ℓ ℓ))
        (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ)).hom := by
  have h : formulaInputIso E ℓ V π d =
      sumInputIso E
        (sumInputIso E
          (sumInputIso E
            (sumInputIso E (SyntaxOptionTransport.productIso E ℓ ℓ) (constructorInputIso E ℓ π d)) ℓ)
          (SyntaxOptionTransport.productIso E ℓ ℓ))
        (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ) := by
    unfold formulaInputIso SyntaxPolynomial.formulaExpression
    simp only [SyntaxPolynomial.power]
    erw [normalizedListInputIso_sum_iso E ℓ _ _ _ _
      (by simp only [SyntaxPolynomial.mapCoefficients,mapCoefficients_constructors]) rfl]
    erw [normalizedListInputIso_sum_iso E ℓ _ _ _ _
      (by simp only [SyntaxPolynomial.mapCoefficients,mapCoefficients_constructors]) rfl]
    erw [normalizedListInputIso_sum_iso E ℓ _ _ _ _
      (by simp only [SyntaxPolynomial.mapCoefficients,mapCoefficients_constructors]) rfl]
    erw [normalizedListInputIso_sum_iso E ℓ _ _ _ _ rfl
      (mapCoefficients_constructors E.inverse.obj π d).symm]
    simp only [SyntaxPolynomial.mapCoefficients,normalizedListInputIso_product_iso E ℓ .term .term .term .term rfl rfl,
      normalizedListInputIso_product_iso E ℓ .formula .formula .formula .formula rfl rfl,
      normalizedListInputIso_product_iso E ℓ (.coefficient V) .formula (.coefficient (E.inverse.obj V)) .formula rfl rfl,
      normalizedListInputIso_term,normalizedListInputIso_formula,normalizedListInputIso_coefficient,
      constructorInputIso]
  exact congrArg Iso.hom h

theorem termInputIso_hom (V : D) (σ : ℕ → D) (d : ℕ) :
    (termInputIso E ℓ V σ d).hom = termInputMap E V σ d (X,X) (Y,Y) (listPairIso E ℓ).hom := by
  simp only [termInputIso,normalizedListInputIso,normalizedPolynomialIso,
    substitutionPolynomialIso,termInputMap,Iso.trans_hom,eqToIso.hom,Functor.mapIso_hom,Category.assoc]

theorem formulaInputIso_hom (V : D) (π : ℕ → D) (d : ℕ) :
    (formulaInputIso E ℓ V π d).hom = formulaInputMap E V π d (X,X) (Y,Y) (listPairIso E ℓ).hom := by
  simp only [formulaInputIso,normalizedListInputIso,normalizedPolynomialIso,
    substitutionPolynomialIso,formulaInputMap,Iso.trans_hom,eqToIso.hom,Functor.mapIso_hom,Category.assoc]

@[reassoc] theorem language_term_input (V : D) (σ π : ℕ → D) (d : ℕ) :
    ((languageJointIso E V σ π d).hom.app (X,X)).1 ≫
      (SyntaxPolynomial.termExpression V σ d).eval.map (listPairIso E ℓ).hom =
        (termInputIso E ℓ V σ d).hom := by
  rw [language_term_map,termInputIso_hom]

@[reassoc] theorem language_formula_input (V : D) (σ π : ℕ → D) (d : ℕ) :
    ((languageJointIso E V σ π d).hom.app (X,X)).2 ≫
      (SyntaxPolynomial.formulaExpression V π d).eval.map (listPairIso E ℓ).hom =
        (formulaInputIso E ℓ V π d).hom := by
  rw [language_formula_map,formulaInputIso_hom]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
