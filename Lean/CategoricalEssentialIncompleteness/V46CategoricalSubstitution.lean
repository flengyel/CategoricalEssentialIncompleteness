/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables
public import CategoricalEssentialIncompleteness.V46CategoricalListLawsParameters

/-! # Named-variable substitution by an algebra in the parameter slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

namespace SyntaxPolynomial

@[simp, reassoc] theorem parameterComparison_inl (P : D) (X : D × D)
    (p q : SyntaxPolynomial D) :
    coprod.inl ≫ parameterComparison P X (.sum p q) =
      parameterComparison P X p ≫ (constantFamilyFunctor P).map coprod.inl := by
  simp [parameterComparison, constantCoproductComparison]

@[simp, reassoc] theorem parameterComparison_inr (P : D) (X : D × D)
    (p q : SyntaxPolynomial D) :
    coprod.inr ≫ parameterComparison P X (.sum p q) =
      parameterComparison P X q ≫ (constantFamilyFunctor P).map coprod.inr := by
  simp [parameterComparison, constantCoproductComparison]

/-- The polynomial comparison respects every pair of morphisms of the
two varying sorts; the coefficient and parameter objects remain fixed. -/
theorem parameterComparison_natural (P : D) {X Y : D × D} (f : X ⟶ Y)
    (p : SyntaxPolynomial D) :
    (p.withParameters P).eval.map
        ((constantFamilyFunctor P).map f.1, (constantFamilyFunctor P).map f.2) ≫
      parameterComparison P Y p =
      parameterComparison P X p ≫ (constantFamilyFunctor P).map (p.eval.map f) := by
  induction p with
  | term => simp [withParameters, eval, parameterComparison]
  | formula => simp [withParameters, eval, parameterComparison]
  | coefficient A => simp [withParameters, eval, parameterComparison, constantFamilyFunctor]
  | unit => simp [withParameters, eval, parameterComparison, constantFamilyFunctor]
  | product p q hp hq =>
    change prod.map _ _ ≫ (prod.map _ _ ≫ _) =
      (prod.map _ _ ≫ _) ≫ (constantFamilyFunctor P).map (prod.map _ _)
    rw [← Category.assoc, prod.map_map, hp, hq, ← prod.map_map, Category.assoc,
      constantProductComparison_natural, ← Category.assoc]
  | sum p q hp hq =>
    change coprod.map _ _ ≫ (coprod.map _ _ ≫ _) =
      (coprod.map _ _ ≫ _) ≫ (constantFamilyFunctor P).map (coprod.map _ _)
    rw [← Category.assoc, coprod.map_map, hp, hq, ← coprod.map_map, Category.assoc,
      constantCoproductComparison_natural, ← Category.assoc]

end SyntaxPolynomial

namespace SumFibers

/-- The two pullbacks of an arrow into a coproduct exhibit its source
as a coproduct. -/
def isColimit {X A B : D} (f : X ⟶ A ⨿ B) :
    IsColimit (BinaryCofan.mk (pullback.fst f coprod.inl) (pullback.fst f coprod.inr)) := by
  have h := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod A B))
    (BinaryCofan.mk (pullback.fst f coprod.inl) (pullback.fst f coprod.inr))
  exact ((h (pullback.snd f coprod.inl) (pullback.snd f coprod.inr) f
    pullback.condition.symm pullback.condition.symm).mpr
      ⟨IsPullback.of_hasPullback f coprod.inl, IsPullback.of_hasPullback f coprod.inr⟩).some

def coverIso {X A B : D} (f : X ⟶ A ⨿ B) :
    pullback f coprod.inl ⨿ pullback f coprod.inr ≅ X where
  hom := coprod.desc (pullback.fst f coprod.inl) (pullback.fst f coprod.inr)
  inv := BinaryCofan.IsColimit.desc (isColimit f) coprod.inl coprod.inr
  hom_inv_id := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc]
      simpa using BinaryCofan.IsColimit.inl_desc (isColimit f) coprod.inl coprod.inr
    · simp only [coprod.inr_desc_assoc]
      simpa using BinaryCofan.IsColimit.inr_desc (isColimit f) coprod.inl coprod.inr
  inv_hom_id := by
    apply BinaryCofan.IsColimit.hom_ext (isColimit f)
    · rw [← Category.assoc, BinaryCofan.IsColimit.inl_desc]
      simp
    · rw [← Category.assoc, BinaryCofan.IsColimit.inr_desc]
      simp

/-- The success and failure pullbacks are complementary subobjects. -/
theorem complementary {X A B : D} (f : X ⟶ A ⨿ B) :
    IsCompl (Subobject.mk (pullback.fst f coprod.inl))
      (Subobject.mk (pullback.fst f coprod.inr)) := by
  let φ := (coverIso f).hom
  have : IsIso φ := inferInstance
  have hi : imageSubobject φ = ⊤ :=
    (PresentationLemmas.image_eq_top_iff_regularEpi φ).mpr inferInstance
  have hm : Subobject.mk (pullback.fst f coprod.inl) ⊓
      Subobject.mk (pullback.fst f coprod.inr) = ⊥ :=
    (PresentationLemmas.mono_copair_iff _ _).mp (inferInstance : Mono φ)
  rw [show φ = coprod.desc (pullback.fst f coprod.inl)
    (pullback.fst f coprod.inr) from rfl, PresentationLemmas.image_copair,
    imageSubobject_mono, imageSubobject_mono] at hi
  exact IsCompl.of_eq hm hi

/-- Case analysis on an arbitrary coproduct-valued morphism, using
its two source fibers rather than global elements. -/
def caseOf {X A B Y : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y) : X ⟶ Y :=
  BinaryCofan.IsColimit.desc (isColimit f) g₀ g₁

omit [Regular D] in
@[simp, reassoc] theorem inl_caseOf {X A B Y : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y) :
    pullback.fst f coprod.inl ≫ caseOf f g₀ g₁ = g₀ :=
  BinaryCofan.IsColimit.inl_desc (isColimit f) _ _

omit [Regular D] in
@[simp, reassoc] theorem inr_caseOf {X A B Y : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y) :
    pullback.fst f coprod.inr ≫ caseOf f g₀ g₁ = g₁ :=
  BinaryCofan.IsColimit.inr_desc (isColimit f) _ _

omit [Regular D] in
theorem comp_caseOf_inl {X A B Y Z : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y)
    (k : Z ⟶ X) (a : Z ⟶ A) (hk : k ≫ f = a ≫ coprod.inl) :
    k ≫ caseOf f g₀ g₁ = pullback.lift k a hk ≫ g₀ := by
  calc
    _ = (pullback.lift k a hk ≫ pullback.fst f coprod.inl) ≫ caseOf f g₀ g₁ := by
      rw [pullback.lift_fst]
    _ = _ := by rw [Category.assoc, inl_caseOf]

omit [Regular D] in
theorem comp_caseOf_inr {X A B Y Z : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y)
    (k : Z ⟶ X) (b : Z ⟶ B) (hk : k ≫ f = b ≫ coprod.inr) :
    k ≫ caseOf f g₀ g₁ = pullback.lift k b hk ≫ g₁ := by
  calc
    _ = (pullback.lift k b hk ≫ pullback.fst f coprod.inr) ≫ caseOf f g₀ g₁ := by
      rw [pullback.lift_fst]
    _ = _ := by rw [Category.assoc, inr_caseOf]

end SumFibers

namespace OptionSyntax

abbrev obj (Y : D) : D := (⊤_ D) ⨿ Y

def fail {X Y : D} : X ⟶ obj Y := terminal.from X ≫ coprod.inl

def map {Y Z : D} (f : Y ⟶ Z) : obj Y ⟶ obj Z := coprod.map (𝟙 _) f

/-- A binary operation fails if either operand fails and otherwise
applies the given constructor. -/
def binary {Y Z : D} (h : Y ⨯ Y ⟶ Z) : obj Y ⨯ obj Y ⟶ obj Z :=
  SumFibers.caseOf (prod.fst : obj Y ⨯ obj Y ⟶ obj Y)
    fail
    (SumFibers.caseOf
      (pullback.fst (prod.fst : obj Y ⨯ obj Y ⟶ obj Y) coprod.inr ≫ prod.snd)
      fail
      (prod.lift
        (pullback.fst _ coprod.inr ≫ pullback.snd
          (prod.fst : obj Y ⨯ obj Y ⟶ obj Y) coprod.inr)
        (pullback.snd _ coprod.inr) ≫ h ≫ coprod.inr))

/-- Lifting a constructor with one coefficient and one recursive formula. -/
def coefficient {V Y Z : D} (h : V ⨯ Y ⟶ Z) : V ⨯ obj Y ⟶ obj Z :=
  SumFibers.caseOf (prod.snd : V ⨯ obj Y ⟶ obj Y) fail
    (prod.lift (pullback.fst _ coprod.inr ≫ prod.fst)
      (pullback.snd _ coprod.inr) ≫ h ≫ coprod.inr)

end OptionSyntax

namespace CategoricalSyntax

variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

def variableConstructor : V ⟶ S.algebra.a.1 := coprod.inl ≫ S.algebra.str.1

def functionConstructors :
    (SyntaxPolynomial.constructors σ d).eval.obj S.algebra.a ⟶ S.algebra.a.1 :=
  coprod.inr ≫ S.algebra.str.1

def equalityConstructor : S.algebra.a.1 ⨯ S.algebra.a.1 ⟶ S.algebra.a.2 :=
  coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ S.algebra.str.2

def relationConstructors :
    (SyntaxPolynomial.constructors π d).eval.obj S.algebra.a ⟶ S.algebra.a.2 :=
  coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ S.algebra.str.2

def implicationConstructor : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  coprod.inr ≫ coprod.inl ≫ S.algebra.str.2

def quantifierConstructor : V ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  coprod.inr ≫ S.algebra.str.2

def substitutionParameters : D := V ⨯ S.algebra.a.1

def substitutionCarriers : D × D :=
  (S.algebra.a.1 ⨯ S.algebra.a.1, S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2)

def originalProjection : S.substitutionCarriers ⟶ S.algebra.a := (prod.fst, prod.fst)

def termResultProjection : S.substitutionCarriers ⟶ S.algebra.a := (prod.snd, prod.fst)

/-- Variable substitution retains the named variable in the original
component and tests it against the variable parameter. -/
def variableSubstitutionPair : S.substitutionParameters ⨯ V ⟶ S.algebra.a.1 ⨯ S.algebra.a.1 :=
  prod.lift (prod.snd ≫ S.variableConstructor)
    (Two.branch (prod.lift prod.snd (prod.fst ≫ prod.fst) ≫ S.decidableVariables.test)
      (prod.snd ≫ S.variableConstructor) (prod.fst ≫ prod.snd))

def functionSubstitutionPair :
    (SyntaxPolynomial.constructors σ d).eval.obj S.substitutionCarriers ⟶
      S.algebra.a.1 ⨯ S.algebra.a.1 :=
  prod.lift ((SyntaxPolynomial.constructors σ d).eval.map S.originalProjection ≫
    S.functionConstructors)
    ((SyntaxPolynomial.constructors σ d).eval.map S.termResultProjection ≫
      S.functionConstructors)

def equalitySubstitutionPair :
    (SyntaxPolynomial.power .term 2).eval.obj S.substitutionCarriers ⟶
      S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 :=
  prod.lift ((SyntaxPolynomial.power .term 2).eval.map S.originalProjection ≫
    S.equalityConstructor)
    ((SyntaxPolynomial.power .term 2).eval.map S.termResultProjection ≫
      S.equalityConstructor ≫ coprod.inr)

def relationSubstitutionPair :
    (SyntaxPolynomial.constructors π d).eval.obj S.substitutionCarriers ⟶
      S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 :=
  prod.lift ((SyntaxPolynomial.constructors π d).eval.map S.originalProjection ≫
    S.relationConstructors)
    ((SyntaxPolynomial.constructors π d).eval.map S.termResultProjection ≫
      S.relationConstructors ≫ coprod.inr)

def negationSubstitutionPair : S.substitutionCarriers.2 ⟶
    S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 :=
  prod.lift (prod.fst ≫ S.negationConstructor)
    (prod.snd ≫ OptionSyntax.map S.negationConstructor)

def implicationSubstitutionPair :
    (SyntaxPolynomial.power .formula 2).eval.obj S.substitutionCarriers ⟶
      S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 :=
  prod.lift (prod.map prod.fst prod.fst ≫ S.implicationConstructor)
    (prod.map prod.snd prod.snd ≫ OptionSyntax.binary S.implicationConstructor)

def quantifierOriginal :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ S.algebra.a.2 :=
  prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst) ≫ S.quantifierConstructor

def quantifierEquality :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ Two D :=
  prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst) ≫ S.decidableVariables.test

def captureAllowed :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ Two D :=
  Two.binary Bool.or
    (Two.unary Bool.not
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.snd ≫ prod.snd ≫ prod.fst ≫ S.formulaOccurrences) ≫
          S.lists.membership S.decidableVariables))
    (Two.unary Bool.not
      (prod.lift (prod.snd ≫ prod.fst)
        (prod.fst ≫ prod.snd ≫ S.termOccurrences) ≫
          S.lists.membership S.decidableVariables))

/-- The equal-name branch returns the original quantified body even
when the recursive substitution result fails. -/
def quantifierSubstitutionResult :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶
      OptionSyntax.obj S.algebra.a.2 :=
  Two.branch S.quantifierEquality
    (Two.branch S.captureAllowed OptionSyntax.fail
      (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd) ≫
        OptionSyntax.coefficient S.quantifierConstructor))
    (S.quantifierOriginal ≫ coprod.inr)

def quantifierSubstitutionPair :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶
      S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 :=
  prod.lift S.quantifierOriginal S.quantifierSubstitutionResult

theorem quantifierSubstitution_equal_branch :
    Two.fiberι S.quantifierEquality true ≫ S.quantifierSubstitutionResult =
      Two.fiberι S.quantifierEquality true ≫ S.quantifierOriginal ≫ coprod.inr := by
  exact Two.fiberι_branch _ _ _ true

theorem quantifierSubstitution_distinct_allowed {X : D}
    (k : X ⟶ S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2))
    (he : k ≫ S.quantifierEquality = Two.constant X false)
    (hc : k ≫ S.captureAllowed = Two.constant X true) :
    k ≫ S.quantifierSubstitutionResult =
      k ≫ prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd) ≫
        OptionSyntax.coefficient S.quantifierConstructor := by
  unfold quantifierSubstitutionResult
  rw [Two.comp_branch _ _ _ k false he]
  exact Two.comp_branch _ _ _ k true hc

theorem quantifierSubstitution_distinct_capture {X : D}
    (k : X ⟶ S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2))
    (he : k ≫ S.quantifierEquality = Two.constant X false)
    (hc : k ≫ S.captureAllowed = Two.constant X false) :
    k ≫ S.quantifierSubstitutionResult = OptionSyntax.fail := by
  unfold quantifierSubstitutionResult
  rw [Two.comp_branch _ _ _ k false he]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Two.comp_branch _ _ _ k false hc]
  simp [OptionSyntax.fail]

def substitutionAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
    ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)) where
  a := (constantFamily S.substitutionParameters S.substitutionCarriers.1,
    constantFamily S.substitutionParameters S.substitutionCarriers.2)
  str :=
    (coprod.desc (parameterHom S.variableSubstitutionPair)
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
        (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.functionSubstitutionPair),
      coprod.desc
        (coprod.desc
          (coprod.desc
            (coprod.desc
              (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
                (SyntaxPolynomial.power .term 2) ≫
                  (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair)
              (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
                (SyntaxPolynomial.constructors π d) ≫
                  (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair))
            ((constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair))
          (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
            (SyntaxPolynomial.power .formula 2) ≫
              (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair))
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (.product (.coefficient V) .formula) ≫ parameterHom S.quantifierSubstitutionPair))

def substitutionFold := S.foldWithParameters S.substitutionParameters S.substitutionAlgebra

theorem variableSubstitution_original :
    parameterHom S.variableSubstitutionPair ≫
        (constantFamilyFunctor S.substitutionParameters).map prod.fst =
      (constantFamilyFunctor S.substitutionParameters).map S.variableConstructor := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;>
    simp [parameterHom, variableSubstitutionPair, constantFamilyFunctor]

theorem quantifierSubstitution_original :
    parameterHom S.quantifierSubstitutionPair ≫
        (constantFamilyFunctor S.substitutionParameters).map prod.fst =
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.map (𝟙 V) prod.fst ≫ S.quantifierConstructor) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp only [parameterHom, constantFamilyFunctor, Over.comp_left,
      Over.homMk_left, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rfl
  · simp only [parameterHom, quantifierSubstitutionPair, quantifierOriginal,
      constantFamilyFunctor, Over.comp_left, Over.homMk_left, Category.assoc,
      prod.lift_fst, prod.lift_snd_assoc, prod.map_snd]
    change (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst) :
      S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ V ⨯ S.algebra.a.2) ≫
        S.quantifierConstructor = prod.snd ≫ prod.map (𝟙 V) prod.fst ≫ S.quantifierConstructor
    have hp : prod.lift (prod.snd ≫ prod.fst)
      (prod.snd ≫ prod.snd ≫ prod.fst) =
      (prod.snd : S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ _) ≫
        prod.map (𝟙 V) prod.fst := by
      apply prod.hom_ext <;> simp <;> rfl
    exact (congrArg (fun f => f ≫ S.quantifierConstructor) hp).trans (Category.assoc _ _ _)

/-- Forgetting the computed result is a morphism from the substitution
algebra to the original syntax algebra pulled back to the parameter slice. -/
def substitutionOriginalHom : S.substitutionAlgebra ⟶
    SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters where
  f := ((constantFamilyFunctor S.substitutionParameters).map prod.fst,
    (constantFamilyFunctor S.substitutionParameters).map prod.fst)
  h := by
    apply Prod.ext
    · change ((SyntaxPolynomial.termExpression V σ d).withParameters
          S.substitutionParameters).eval.map
          ((constantFamilyFunctor S.substitutionParameters).map prod.fst,
            (constantFamilyFunctor S.substitutionParameters).map prod.fst) ≫
          (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a
            (SyntaxPolynomial.termExpression V σ d) ≫
              (constantFamilyFunctor S.substitutionParameters).map S.algebra.str.1) =
          S.substitutionAlgebra.str.1 ≫
            (constantFamilyFunctor S.substitutionParameters).map prod.fst
      have hn := SyntaxPolynomial.parameterComparison_natural S.substitutionParameters
        S.originalProjection (SyntaxPolynomial.termExpression V σ d)
      dsimp only [originalProjection] at hn
      dsimp only [substitutionAlgebra]
      rw [← Category.assoc, hn]
      apply coprod.hom_ext
      · simpa [SyntaxPolynomial.termExpression, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, substitutionAlgebra, SyntaxPolynomial.algebraWithParameters,
          SyntaxPolynomial.parameterComparison, constantCoproductComparison,
          originalProjection, variableConstructor, ← Functor.map_comp_assoc,
          ← Functor.map_comp, Category.assoc] using
            S.variableSubstitution_original.symm
      · simp [SyntaxPolynomial.termExpression, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor,
          SyntaxPolynomial.parameterComparison_inr_assoc,
          originalProjection, functionSubstitutionPair, functionConstructors,
          ← Functor.map_comp, Category.assoc]
    · change ((SyntaxPolynomial.formulaExpression V π d).withParameters
          S.substitutionParameters).eval.map
          ((constantFamilyFunctor S.substitutionParameters).map prod.fst,
            (constantFamilyFunctor S.substitutionParameters).map prod.fst) ≫
          (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a
            (SyntaxPolynomial.formulaExpression V π d) ≫
              (constantFamilyFunctor S.substitutionParameters).map S.algebra.str.2) =
          S.substitutionAlgebra.str.2 ≫
            (constantFamilyFunctor S.substitutionParameters).map prod.fst
      have hn := SyntaxPolynomial.parameterComparison_natural S.substitutionParameters
        S.originalProjection (SyntaxPolynomial.formulaExpression V π d)
      dsimp only [originalProjection] at hn
      dsimp only [substitutionAlgebra]
      rw [← Category.assoc, hn]
      repeat' apply coprod.hom_ext
      all_goals
        simp [SyntaxPolynomial.formulaExpression, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          SyntaxPolynomial.parameterComparison_inl_assoc,
          SyntaxPolynomial.parameterComparison_inr_assoc, originalProjection,
          equalitySubstitutionPair, relationSubstitutionPair, negationSubstitutionPair,
          implicationSubstitutionPair, equalityConstructor, relationConstructors,
          negationConstructor, negationInjection, implicationConstructor,
          S.quantifierSubstitution_original, ← Functor.map_comp, Category.assoc]
      all_goals simp [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.power,
        SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, quantifierConstructor] <;> rfl

/-- The original components of the fold are identities on the two
parameterized syntax objects. -/
theorem substitutionFold_original :
    S.substitutionFold ≫ S.substitutionOriginalHom.f =
      𝟙 (constantFamily S.substitutionParameters S.algebra.a.1,
        constantFamily S.substitutionParameters S.algebra.a.2) := by
  let A := SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters
  let f : A ⟶ S.substitutionAlgebra := (S.stable S.substitutionParameters).to _
  have h : f ≫ S.substitutionOriginalHom = 𝟙 A :=
    (S.stable S.substitutionParameters).hom_ext _ _
  exact congrArg Endofunctor.Algebra.Hom.f h

theorem substitutionFold_commutes :
    (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map
        S.substitutionFold ≫ S.substitutionAlgebra.str =
      (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str ≫
          S.substitutionFold :=
  S.foldWithParameters_commutes _ _

theorem substitutionFold_unique
    (f : (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters S.algebra.a.2) ⟶ S.substitutionAlgebra.a)
    (hf : (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map
        f ≫ S.substitutionAlgebra.str =
      (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str ≫ f) :
    f = S.substitutionFold :=
  S.foldWithParameters_unique _ _ f hf

def termSubstitution : S.algebra.a.1 ⨯ S.substitutionParameters ⟶ S.algebra.a.1 :=
  (prod.braiding _ _).hom ≫ S.substitutionFold.1.left ≫ prod.snd ≫ prod.snd

def formulaSubstitutionOption :
    S.algebra.a.2 ⨯ S.substitutionParameters ⟶ OptionSyntax.obj S.algebra.a.2 :=
  (prod.braiding _ _).hom ≫ S.substitutionFold.2.left ≫ prod.snd ≫ prod.snd

theorem termSubstitution_original :
    (prod.braiding S.algebra.a.1 S.substitutionParameters).hom ≫
      S.substitutionFold.1.left ≫ prod.snd ≫ prod.fst = prod.fst := by
  have h : S.substitutionFold.1 ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.fst : S.algebra.a.1 ⨯ S.algebra.a.1 ⟶ S.algebra.a.1) =
      𝟙 (constantFamily S.substitutionParameters S.algebra.a.1) :=
    congrArg Prod.fst S.substitutionFold_original
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simp only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd, Over.id_left, Category.id_comp] at hh
  simpa only [Category.assoc, prod.braiding_hom, prod.lift_snd] using
    congrArg (fun k => (prod.braiding S.algebra.a.1 S.substitutionParameters).hom ≫ k) hh

theorem formulaSubstitution_original :
    (prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫
      S.substitutionFold.2.left ≫ prod.snd ≫ prod.fst = prod.fst := by
  have h : S.substitutionFold.2 ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.fst : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ S.algebra.a.2) =
      𝟙 (constantFamily S.substitutionParameters S.algebra.a.2) :=
    congrArg Prod.snd S.substitutionFold_original
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simp only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd, Over.id_left, Category.id_comp] at hh
  simpa only [Category.assoc, prod.braiding_hom, prod.lift_snd] using
    congrArg (fun k => (prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫ k) hh

def admissibleSubstitution : D := pullback S.formulaSubstitutionOption coprod.inr

def admissibleInclusion : S.admissibleSubstitution ⟶ S.algebra.a.2 ⨯ S.substitutionParameters :=
  pullback.fst _ _

def formulaSubstitution : S.admissibleSubstitution ⟶ S.algebra.a.2 := pullback.snd _ _

instance admissibleInclusion_mono : Mono S.admissibleInclusion := by
  dsimp [admissibleInclusion, admissibleSubstitution]
  infer_instance

theorem formulaSubstitution_square :
    S.admissibleInclusion ≫ S.formulaSubstitutionOption =
      S.formulaSubstitution ≫ coprod.inr := pullback.condition

theorem formulaSubstitution_isPullback :
    IsPullback S.admissibleInclusion S.formulaSubstitution
      S.formulaSubstitutionOption coprod.inr :=
  IsPullback.of_hasPullback _ _

theorem admissibility_complemented :
    IsCompl (Subobject.mk S.admissibleInclusion)
      (Subobject.mk (pullback.fst S.formulaSubstitutionOption coprod.inl)) :=
  (SumFibers.complementary S.formulaSubstitutionOption).symm

end CategoricalSyntax

end CategoricalEssentialIncompleteness.V46
