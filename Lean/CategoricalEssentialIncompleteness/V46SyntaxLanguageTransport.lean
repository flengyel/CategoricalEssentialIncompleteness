/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport
import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport

/-! # Constructor comparisons for the actual transported syntax language -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46

namespace SyntaxPolynomialTransport
variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (f : I → C) (g : I → D) (χ : ∀ i, E.functor.obj (f i) ≅ g i)

@[reassoc] theorem component_inl (p q : SyntaxPolynomial I) (X : C × C) :
    E.functor.map (coprod.inl : (p.mapCoefficients f).eval.obj X ⟶
      (p.mapCoefficients f).eval.obj X ⨿ (q.mapCoefficients f).eval.obj X) ≫
        (component E f g χ (.sum p q) X).hom = (component E f g χ p X).hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫ (inv (coprodComparison E.functor _ _) ≫ coprod.map _ _) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]

@[reassoc] theorem component_inr (p q : SyntaxPolynomial I) (X : C × C) :
    E.functor.map (coprod.inr : (q.mapCoefficients f).eval.obj X ⟶
      (p.mapCoefficients f).eval.obj X ⨿ (q.mapCoefficients f).eval.obj X) ≫
        (component E f g χ (.sum p q) X).hom = (component E f g χ q X).hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫ (inv (coprodComparison E.functor _ _) ≫ coprod.map _ _) = _
  rw [← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

@[reassoc] theorem component_fst (p q : SyntaxPolynomial I) (X : C × C) :
    (component E f g χ (.product p q) X).hom ≫ prod.fst =
      E.functor.map prod.fst ≫ (component E f g χ p X).hom := by
  simp [component,Category.assoc]

@[reassoc] theorem component_snd (p q : SyntaxPolynomial I) (X : C × C) :
    (component E f g χ (.product p q) X).hom ≫ prod.snd =
      E.functor.map prod.snd ≫ (component E f g χ q X).hom := by
  simp [component,Category.assoc]

omit [FinitaryExtensive D] in
theorem productComparison_identity (A B : D) :
    prodComparison (𝟭 D) A B = 𝟙 (A ⨯ B) := by
  change prod.lift (prod.fst : A ⨯ B ⟶ A) prod.snd = 𝟙 _
  apply prod.hom_ext <;> simp

omit [Regular D] in
theorem coproductComparison_identity (A B : D) :
    coprodComparison (𝟭 D) A B = 𝟙 (A ⨿ B) := by
  change coprod.desc (coprod.inl : A ⟶ A ⨿ B) coprod.inr = 𝟙 _
  apply coprod.hom_ext <;> simp

omit [FinitaryExtensive D] in
theorem terminalComparison_identity : terminalComparison (𝟭 D) = 𝟙 (⊤_ D) :=
  terminalIsTerminal.hom_ext _ _

/-- The polynomial comparison for the identity equivalence is the
identity, by finite product and coproduct uniqueness at every node. -/
theorem component_refl (p : SyntaxPolynomial D) (A : D × D) :
    (component ((CategoryTheory.Equivalence.refl : D ≌ D)) id id (fun X => Iso.refl X) p A).hom = 𝟙 _ := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient X => rfl
  | unit => exact terminalComparison_identity
  | product p q hp hq =>
      simp [component,hp,hq,productComparison_identity]
      rfl
  | sum p q hp hq =>
      simp [component,hp,hq,coproductComparison_identity]
      rfl

theorem jointIso_refl (p q : SyntaxPolynomial D) :
    jointIso (CategoryTheory.Equivalence.refl : D ≌ D) id id (fun X => Iso.refl X) p q = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact Prod.ext (component_refl p A) (component_refl q A)

end SyntaxPolynomialTransport

namespace SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
local notation "K₀" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
  (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
local notation "K₁" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

omit [Regular D] [FinitaryExtensive D] in
theorem sourceLanguageEquality : K₀ = SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V σ d).mapCoefficients E.inverse.obj)
    ((SyntaxPolynomial.formulaExpression V π d).mapCoefficients E.inverse.obj) := by
  simp only [mapCoefficients_termExpression,mapCoefficients_formulaExpression]

theorem targetLanguageEquality : SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V σ d).mapCoefficients id)
    ((SyntaxPolynomial.formulaExpression V π d).mapCoefficients id) = K₁ := by
  simp only [mapCoefficients_termExpression,mapCoefficients_formulaExpression,id_eq]

/-- The existing polynomial comparison, normalized by explicit functor
equality isomorphisms. Every coefficient uses its actual counit. -/
def languageJointIso : K₀ ⋙ (E.prod E).functor ≅ (E.prod E).functor ⋙ K₁ :=
  eqToIso (congrArg (fun F => F ⋙ (E.prod E).functor) (sourceLanguageEquality E V σ π d)) ≪≫
    SyntaxPolynomialTransport.jointIso E E.inverse.obj id (fun X => E.counitIso.app X)
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) ≪≫
    eqToIso (congrArg (fun G => (E.prod E).functor ⋙ G) (targetLanguageEquality V σ π d))

theorem languageJointIso_refl (A : D × D) :
    (languageJointIso (CategoryTheory.Equivalence.refl : D ≌ D) V σ π d).hom.app A = 𝟙 _ := by
  have hi : languageJointIso (CategoryTheory.Equivalence.refl : D ≌ D) V σ π d = Iso.refl _ := by
    unfold languageJointIso
    erw [SyntaxPolynomialTransport.jointIso_refl]
    apply Iso.ext
    simp only [Iso.trans_hom,eqToIso.hom,Iso.refl_hom]
    erw [Category.id_comp,eqToHom_trans]
    rfl
  rw [hi]
  rfl

variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)

def mappedSyntaxAlgebra : Endofunctor.Algebra K₁ :=
  AlgebraTransport.mappedAlgebra (E.prod E) (languageJointIso E V σ π d) S₀.algebra

def mappedSyntaxInitial : IsInitial (mappedSyntaxAlgebra E V σ π d S₀) :=
  AlgebraTransport.initial (E.prod E) (languageJointIso E V σ π d) S₀.algebra S₀.initial

/-- In the identity case the normalized mapped algebra has the same
carriers and constructors, through an isomorphism with identity carriers. -/
def languageIdentityIso (S : CategoricalSyntax V σ π d) :
    mappedSyntaxAlgebra ((CategoryTheory.Equivalence.refl : D ≌ D)) V σ π d S ≅ S.algebra := by
  refine Endofunctor.Algebra.isoMk (Iso.refl S.algebra.a) ?_
  have hi := ((languageJointIso ((CategoryTheory.Equivalence.refl : D ≌ D)) V σ π d).app S.algebra.a).hom_inv_id
  change (languageJointIso (CategoryTheory.Equivalence.refl : D ≌ D) V σ π d).hom.app S.algebra.a ≫
    ((languageJointIso (CategoryTheory.Equivalence.refl : D ≌ D) V σ π d).app S.algebra.a).inv = 𝟙 _ at hi
  rw [languageJointIso_refl,Category.id_comp] at hi
  change (K₁).map (𝟙 S.algebra.a) ≫ S.algebra.str =
    (((languageJointIso ((CategoryTheory.Equivalence.refl : D ≌ D)) V σ π d).app S.algebra.a).inv ≫ S.algebra.str) ≫ 𝟙 _
  rw [hi,(K₁).map_id]
  simp

/-- The comparison is obtained from the two proved universal
properties; constructor compatibility is part of this algebra isomorphism. -/
def syntaxAlgebraIso (S₁ : CategoricalSyntax V σ π d) :
    mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra :=
  (mappedSyntaxInitial E V σ π d S₀).uniqueUpToIso S₁.initial

variable {S₁ : CategoricalSyntax V σ π d}
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def syntaxCarrierIso :
    (E.prod E).functor.obj S₀.algebra.a ≅ S₁.algebra.a :=
  (Endofunctor.Algebra.forget K₁).mapIso c

def syntaxTermIso : E.functor.obj S₀.algebra.a.1 ≅ S₁.algebra.a.1 :=
  (CategoryTheory.Prod.fst D D).mapIso (syntaxCarrierIso E V σ π d S₀ c)

def syntaxFormulaIso : E.functor.obj S₀.algebra.a.2 ≅ S₁.algebra.a.2 :=
  (CategoryTheory.Prod.snd D D).mapIso (syntaxCarrierIso E V σ π d S₀ c)

/-- The whole ordinary constructor square follows from the actual
algebra isomorphism, before taking any free-variable or substitution fold. -/
theorem language_structure_comparison :
    (E.prod E).functor.map S₀.algebra.str ≫ c.hom.f =
      (languageJointIso E V σ π d).hom.app S₀.algebra.a ≫ (K₁).map c.hom.f ≫ S₁.algebra.str := by
  rw [c.hom.h]
  change _ = ((languageJointIso E V σ π d).app S₀.algebra.a).hom ≫
    (((languageJointIso E V σ π d).app S₀.algebra.a).inv ≫
      (E.prod E).functor.map S₀.algebra.str) ≫ c.hom.f
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

end SyntaxOperationsTransport
end CategoricalEssentialIncompleteness.V46
