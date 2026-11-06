/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransport

/-! # Explicit normalized polynomial components at arbitrary sort pairs -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

theorem functor_eqToHom_app {F G : C ⥤ D} (h : F = G) (A : C) :
    (eqToHom h : F ⟶ G).app A = eqToHom (congrArg (fun H => H.obj A) h) := by
  cases h
  rfl

theorem pair_eqToHom_fst {A B : D × D} (h : A = B) :
    (eqToHom h : A ⟶ B).1 = eqToHom (congrArg Prod.fst h) := by
  cases h
  rfl

theorem pair_eqToHom_snd {A B : D × D} (h : A = B) :
    (eqToHom h : A ⟶ B).2 = eqToHom (congrArg Prod.snd h) := by
  cases h
  rfl

/-- An ordinary type cast of a morphism is the corresponding pair of
object equality morphisms. The equality proof itself is irrelevant. -/
theorem hom_cast {A B A' B' : D} (ha : A = A') (hb : B = B')
    {ht : (A ⟶ B) = (A' ⟶ B')} (f : A ⟶ B) :
    cast ht f = eqToHom ha.symm ≫ f ≫ eqToHom hb := by
  cases ha
  cases hb
  have hh : ht = rfl := Subsingleton.elim _ _
  rw [hh]
  simp

theorem iso_cast_hom {A B A' B' : D} (ha : A = A') (hb : B = B')
    {ht : (A ≅ B) = (A' ≅ B')} (i : A ≅ B) :
    (cast ht i).hom = eqToHom ha.symm ≫ i.hom ≫ eqToHom hb := by
  cases ha
  cases hb
  have hh : ht = rfl := Subsingleton.elim _ _
  rw [hh]
  simp

variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] [Category D] in
theorem termTargetExpressionEquality :
    (SyntaxPolynomial.termExpression V σ d).mapCoefficients id = SyntaxPolynomial.termExpression V σ d := by
  simpa only [id_eq] using mapCoefficients_termExpression (id : D → D) V σ d

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] [Category D] in
theorem formulaTargetExpressionEquality :
    (SyntaxPolynomial.formulaExpression V π d).mapCoefficients id = SyntaxPolynomial.formulaExpression V π d := by
  simpa only [id_eq] using mapCoefficients_formulaExpression (id : D → D) V π d

omit [Regular D] [FinitaryExtensive D] in
theorem termSourceObjectEquality (A : C × C) :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj A) =
      E.functor.obj (((SyntaxPolynomial.termExpression V σ d).mapCoefficients E.inverse.obj).eval.obj A) :=
  congrArg (fun p => E.functor.obj (p.eval.obj A))
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm

omit [Regular D] [FinitaryExtensive D] in
theorem formulaSourceObjectEquality (A : C × C) :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj A) =
      E.functor.obj (((SyntaxPolynomial.formulaExpression V π d).mapCoefficients E.inverse.obj).eval.obj A) :=
  congrArg (fun p => E.functor.obj (p.eval.obj A))
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm

def normalizedTermComponent (A : C × C) :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj A) ⟶
      (SyntaxPolynomial.termExpression V σ d).eval.obj ((E.prod E).functor.obj A) :=
  eqToHom (termSourceObjectEquality E V σ d A) ≫
    (SyntaxPolynomialTransport.component E E.inverse.obj id (fun X => E.counitIso.app X)
      (SyntaxPolynomial.termExpression V σ d) A).hom ≫
    eqToHom (congrArg (fun p => p.eval.obj ((E.prod E).functor.obj A)) (termTargetExpressionEquality V σ d))

def normalizedFormulaComponent (A : C × C) :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj A) ⟶
      (SyntaxPolynomial.formulaExpression V π d).eval.obj ((E.prod E).functor.obj A) :=
  eqToHom (formulaSourceObjectEquality E V π d A) ≫
    (SyntaxPolynomialTransport.component E E.inverse.obj id (fun X => E.counitIso.app X)
      (SyntaxPolynomial.formulaExpression V π d) A).hom ≫
    eqToHom (congrArg (fun p => p.eval.obj ((E.prod E).functor.obj A)) (formulaTargetExpressionEquality V π d))

theorem language_term_component (A : C × C) :
    ((languageJointIso E V σ π d).hom.app A).1 = normalizedTermComponent E V σ d A := by
  unfold languageJointIso normalizedTermComponent
  simp only [Iso.trans_hom,eqToIso.hom,NatTrans.comp_app,functor_eqToHom_app]
  simp only [prod_comp_fst, pair_eqToHom_fst]
  rfl

theorem language_formula_component (A : C × C) :
    ((languageJointIso E V σ π d).hom.app A).2 = normalizedFormulaComponent E V π d A := by
  unfold languageJointIso normalizedFormulaComponent
  simp only [Iso.trans_hom,eqToIso.hom,NatTrans.comp_app,functor_eqToHom_app]
  simp only [prod_comp_snd, pair_eqToHom_snd]
  rfl

omit [Regular C] [FinitaryExtensive C] in
theorem polynomial_equality_natural {p q : SyntaxPolynomial D} (h : p = q)
    {A B : D × D} (k : A ⟶ B) :
    eqToHom (congrArg (fun r => r.eval.obj A) h) ≫ q.eval.map k =
      p.eval.map k ≫ eqToHom (congrArg (fun r => r.eval.obj B) h) := by
  cases h
  simp

def termInputMap (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj A) ⟶ (SyntaxPolynomial.termExpression V σ d).eval.obj B :=
  eqToHom (termSourceObjectEquality E V σ d A) ≫
    (SyntaxPolynomialTransport.component E E.inverse.obj id (fun X => E.counitIso.app X)
      (SyntaxPolynomial.termExpression V σ d) A).hom ≫
    ((SyntaxPolynomial.termExpression V σ d).mapCoefficients id).eval.map k ≫
    eqToHom (congrArg (fun p => p.eval.obj B) (termTargetExpressionEquality V σ d))

def formulaInputMap (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj A) ⟶ (SyntaxPolynomial.formulaExpression V π d).eval.obj B :=
  eqToHom (formulaSourceObjectEquality E V π d A) ≫
    (SyntaxPolynomialTransport.component E E.inverse.obj id (fun X => E.counitIso.app X)
      (SyntaxPolynomial.formulaExpression V π d) A).hom ≫
    ((SyntaxPolynomial.formulaExpression V π d).mapCoefficients id).eval.map k ≫
    eqToHom (congrArg (fun p => p.eval.obj B) (formulaTargetExpressionEquality V π d))

@[reassoc] theorem language_term_map (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    ((languageJointIso E V σ π d).hom.app A).1 ≫ (SyntaxPolynomial.termExpression V σ d).eval.map k =
      termInputMap E V σ d A B k := by
  rw [language_term_component]
  unfold normalizedTermComponent termInputMap
  simp only [Category.assoc]
  rw [polynomial_equality_natural (termTargetExpressionEquality V σ d) k]

@[reassoc] theorem language_formula_map (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    ((languageJointIso E V σ π d).hom.app A).2 ≫ (SyntaxPolynomial.formulaExpression V π d).eval.map k =
      formulaInputMap E V π d A B k := by
  rw [language_formula_component]
  unfold normalizedFormulaComponent formulaInputMap
  simp only [Category.assoc]
  rw [polynomial_equality_natural (formulaTargetExpressionEquality V π d) k]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
