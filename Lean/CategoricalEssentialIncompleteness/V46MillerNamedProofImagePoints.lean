/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageData

/-! # Literal named points of the actual uniform logical operations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
namespace Points
section Generic
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P:=P)

private theorem point_natural {X Y : Total.TotalCategory P} (f : X ⟶ Y) (x : (U).obj X) :
    Total.underlyingPoint ((U).map f x)=Total.underlyingPoint x ≫ f := by
  have h := ConcreteCategory.congr_hom ((Total.underlyingHomComparison (P:=P)).hom.naturality f) x
  exact h

private theorem point_value {X : Total.TotalCategory P} (x : (U).obj X) :
    (U).map (Total.underlyingPoint x) ⟨0,rfl⟩=x := by
  apply Subtype.ext
  exact Part.mem_unique (Total.totalFunction_mem (Total.underlyingPoint x) ⟨0,rfl⟩)
    (Part.eq_some_iff.mp (Total.underlyingPoint_value x 0 rfl))

def pairPoint {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) : (U).obj (X ⨯ Y) :=
  (U).map (prod.lift (Total.underlyingPoint x) (Total.underlyingPoint y)) ⟨0,rfl⟩

theorem pairPoint_fst {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.fst : X ⨯ Y ⟶ X) (pairPoint x y)=x := by
  rw [pairPoint,← CategoryTheory.Functor.map_comp_apply,prod.lift_fst,point_value]

theorem pairPoint_snd {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.snd : X ⨯ Y ⟶ Y) (pairPoint x y)=y := by
  rw [pairPoint,← CategoryTheory.Functor.map_comp_apply,prod.lift_snd,point_value]

theorem product_ext {X Y : Total.TotalCategory P} {p q : (U).obj (X ⨯ Y)}
    (hf : (U).map prod.fst p=(U).map prod.fst q)
    (hs : (U).map prod.snd p=(U).map prod.snd q) : p=q := by
  apply (Total.pointHomEquiv (X ⨯ Y)).injective
  apply prod.hom_ext
  · change Total.underlyingPoint p ≫ (prod.fst : X ⨯ Y ⟶ X) =
      Total.underlyingPoint q ≫ (prod.fst : X ⨯ Y ⟶ X)
    rw [← point_natural,← point_natural,hf]
  · change Total.underlyingPoint p ≫ (prod.snd : X ⨯ Y ⟶ Y) =
      Total.underlyingPoint q ≫ (prod.snd : X ⨯ Y ⟶ Y)
    rw [← point_natural,← point_natural,hs]

theorem lift_point {A B C : Total.TotalCategory P} (f : A ⟶ B) (g : A ⟶ C) (a : (U).obj A) :
    (U).map (prod.lift f g) a=pairPoint ((U).map f a) ((U).map g a) := by
  apply product_ext
  · rw [← CategoryTheory.Functor.map_comp_apply,prod.lift_fst,pairPoint_fst]
  · rw [← CategoryTheory.Functor.map_comp_apply,prod.lift_snd,pairPoint_snd]

private theorem point_comp {X Y Z : Total.TotalCategory P}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : (U).obj X) :
    (U).map (f ≫ g) x = (U).map g ((U).map f x) :=
  CategoryTheory.Functor.map_comp_apply (U) f g x

theorem pullback_point_exists {A B C : Total.TotalCategory P} (f : A ⟶ C) (g : B ⟶ C)
    (a : (U).obj A) (b : (U).obj B) (h : (U).map f a=(U).map g b) :
    ∃ z : (U).obj (pullback f g), (U).map (pullback.fst f g) z=a ∧
      (U).map (pullback.snd f g) z=b :=
  Types.exists_of_isPullback ((IsPullback.of_hasPullback f g).map (U)) a b h

end Generic

variable (P : Uniform.Family)
local notation "U" => Total.underlying (P := P)
local notation "F" => Syntax.predicateFunctor P
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

theorem mapped_pair {A B : PredicateCategory 𝗣𝗔} {X Y : Total.TotalCategory P}
    (i : (F).obj A ≅ X) (j : (F).obj B ≅ Y)
    (a : PredicateInterpretation.Obj ℕ A) (b : PredicateInterpretation.Obj ℕ B) :
    (U).map (NamedSyntaxComparison.Options.productIso (F) i j).hom
      (sourcePoint P (A ⨯ B) (SyntacticLists.pairPoint 𝗣𝗔 ℕ a b))=
      pairPoint ((U).map i.hom (sourcePoint P A a)) ((U).map j.hom (sourcePoint P B b)) := by
  apply product_ext
  · rw [← CategoryTheory.Functor.map_comp_apply,NamedSyntaxComparison.Options.productIso_fst,
      CategoryTheory.Functor.map_comp_apply,map_sourcePoint,SyntacticLists.pairPoint_fst,pairPoint_fst]
  · rw [← CategoryTheory.Functor.map_comp_apply,NamedSyntaxComparison.Options.productIso_snd,
      CategoryTheory.Functor.map_comp_apply,map_sourcePoint,SyntacticLists.pairPoint_snd,pairPoint_snd]

private theorem operation_point {A B : PredicateCategory 𝗣𝗔} {X Y : Total.TotalCategory P}
    (i : (F).obj A ≅ X) (j : (F).obj B ≅ Y) (a : A ⟶ B) (g : X ⟶ Y)
    (h : (F).map a ≫ j.hom=i.hom ≫ g) (q : PredicateInterpretation.Obj ℕ A) :
    (U).map g ((U).map i.hom (sourcePoint P A q))=
      (U).map j.hom (sourcePoint P B ((N).map a q)) := by
  have hh := congrArg (fun f => (U).map f (sourcePoint P A q)) h
  simp only [CategoryTheory.Functor.map_comp_apply,map_sourcePoint] at hh
  exact hh.symm

variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "tChart" => Iso.symm (NamedSyntaxComparison.termIso P (V) σ π d)
local notation "fChart" => Iso.symm (NamedSyntaxComparison.formulaIso P (V) σ π d)

def namePoint (x : ℕ) : (U).obj ((F).obj (V)) :=
  sourcePoint P (V) (SyntacticNamedHilbert.namePoint x)

theorem implication_point (φ ψ : Fm) :
    (U).map (S).implicationConstructor (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))=
      formulaPoint P σ π d (.imp φ ψ) := by
  have h := operation_point P (NamedSyntaxComparison.Options.productIso (F) (fChart) (fChart)) (fChart)
    (S₀).implicationConstructor (S).implicationConstructor
    (NamedSyntaxComparison.implication_constructor P (V) σ π d)
    (SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.formulaPoint σ π d φ)
      (SyntacticNamedHilbert.formulaPoint σ π d ψ))
  have hm := mapped_pair P (fChart) (fChart)
    (SyntacticNamedHilbert.formulaPoint σ π d φ)
    (SyntacticNamedHilbert.formulaPoint σ π d ψ)
  have hn := congrArg
    (fun q => (U).map (fChart).hom (sourcePoint P (S₀).algebra.a.2 q))
    (SyntacticNamedHilbert.implication_point σ π d φ ψ)
  exact (congrArg ((U).map (S).implicationConstructor) hm.symm).trans (h.trans hn)

theorem equality_point (u v : Tm) :
    (U).map (S).equalityConstructor (pairPoint (termPoint P σ π d u) (termPoint P σ π d v))=
      formulaPoint P σ π d (.equal u v) := by
  have h := operation_point P (NamedSyntaxComparison.Options.productIso (F) (tChart) (tChart)) (fChart)
    (S₀).equalityConstructor (S).equalityConstructor
    (NamedSyntaxComparison.equality_constructor P (V) σ π d)
    (SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.termPoint σ π d u)
      (SyntacticNamedHilbert.termPoint σ π d v))
  have hm := mapped_pair P (tChart) (tChart)
    (SyntacticNamedHilbert.termPoint σ π d u)
    (SyntacticNamedHilbert.termPoint σ π d v)
  have hn := congrArg
    (fun q => (U).map (fChart).hom (sourcePoint P (S₀).algebra.a.2 q))
    (SyntacticNamedHilbert.equality_point σ π d u v)
  exact (congrArg ((U).map (S).equalityConstructor) hm.symm).trans (h.trans hn)

theorem quantifier_point (x : ℕ) (φ : Fm) :
    (U).map (S).quantifierConstructor (pairPoint (namePoint P x) (formulaPoint P σ π d φ))=
      formulaPoint P σ π d (.all x φ) := by
  have h := operation_point P (NamedSyntaxComparison.Options.productIso (F) (Iso.refl _) (fChart)) (fChart)
    (S₀).quantifierConstructor (S).quantifierConstructor
    (NamedSyntaxComparison.quantifier_constructor P (V) σ π d)
    (SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.namePoint x)
      (SyntacticNamedHilbert.formulaPoint σ π d φ))
  have hm := mapped_pair P (Iso.refl ((F).obj (V))) (fChart)
    (SyntacticNamedHilbert.namePoint x) (SyntacticNamedHilbert.formulaPoint σ π d φ)
  have hm' : (U).map (NamedSyntaxComparison.Options.productIso (F)
      (Iso.refl ((F).obj (V))) (fChart)).hom
      (sourcePoint P _ (SyntacticLists.pairPoint 𝗣𝗔 ℕ (SyntacticNamedHilbert.namePoint x)
        (SyntacticNamedHilbert.formulaPoint σ π d φ))) =
      pairPoint (namePoint P x) (formulaPoint P σ π d φ) := by
    simpa only [Iso.refl_hom, Iso.symm_hom, CategoryTheory.Functor.map_id_apply,
      namePoint, formulaPoint, sourceFormulaPoint] using hm
  have hn := congrArg
    (fun q => (U).map (fChart).hom (sourcePoint P (S₀).algebra.a.2 q))
    (SyntacticNamedHilbert.quantifier_point σ π d x φ)
  exact (congrArg ((U).map (S).quantifierConstructor) hm'.symm).trans (h.trans hn)

theorem implication_at {A : Total.TotalCategory P} (f g : A ⟶ (S).algebra.a.2) (a : (U).obj A)
    (φ ψ : Fm) (hf : (U).map f a = formulaPoint P σ π d φ)
    (hg : (U).map g a = formulaPoint P σ π d ψ) :
    (U).map (prod.lift f g ≫ (S).implicationConstructor) a = formulaPoint P σ π d (.imp φ ψ) := by
  calc
    _ = (U).map (S).implicationConstructor ((U).map (prod.lift f g) a) :=
      (U).map_comp_apply _ _ a
    _ = (U).map (S).implicationConstructor
        (pairPoint ((U).map f a) ((U).map g a)) :=
      congrArg ((U).map (S).implicationConstructor) (lift_point f g a)
    _ = (U).map (S).implicationConstructor
        (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) :=
      congrArg ((U).map (S).implicationConstructor)
        (congrArg₂ (pairPoint) hf hg)
    _ = _ := implication_point P σ π d φ ψ

theorem negation_at {A : Total.TotalCategory P} (f : A ⟶ (S).algebra.a.2) (a : (U).obj A)
    (φ : Fm) (hf : (U).map f a = formulaPoint P σ π d φ) :
    (U).map (f ≫ (S).negationConstructor) a = formulaPoint P σ π d (.neg φ) := by
  calc
    _ = (U).map (S).negationConstructor ((U).map f a) :=
      point_comp f (S).negationConstructor a
    _ = (U).map (S).negationConstructor (formulaPoint P σ π d φ) :=
      congrArg ((U).map (S).negationConstructor) hf
    _ = _ := formulaPoint_negation P σ π d φ

theorem equality_at {A : Total.TotalCategory P} (f g : A ⟶ (S).algebra.a.1) (a : (U).obj A)
    (u t : Tm) (hf : (U).map f a = termPoint P σ π d u)
    (hg : (U).map g a = termPoint P σ π d t) :
    (U).map (prod.lift f g ≫ (S).equalityConstructor) a = formulaPoint P σ π d (.equal u t) := by
  exact ((U).map_comp_apply _ _ a).trans
    ((congrArg ((U).map (S).equalityConstructor) (lift_point f g a)).trans
      ((congrArg ((U).map (S).equalityConstructor)
        (congrArg₂ (pairPoint) hf hg)).trans (equality_point P σ π d u t)))

theorem quantifier_at {A : Total.TotalCategory P}
    (f : A ⟶ (F).obj (V)) (g : A ⟶ (S).algebra.a.2) (a : (U).obj A)
    (x : ℕ) (φ : Fm) (hf : (U).map f a = namePoint P x)
    (hg : (U).map g a = formulaPoint P σ π d φ) :
    (U).map (prod.lift f g ≫ (S).quantifierConstructor) a = formulaPoint P σ π d (.all x φ) := by
  exact ((U).map_comp_apply _ _ a).trans
    ((congrArg ((U).map (S).quantifierConstructor) (lift_point f g a)).trans
      ((congrArg ((U).map (S).quantifierConstructor)
        (congrArg₂ (pairPoint) hf hg)).trans (quantifier_point P σ π d x φ)))


def substitutionPoint (x : ℕ) (φ : Fm) (t : Tm) : (U).obj ((S).algebra.a.2 ⨯ (S).substitutionParameters) :=
  pairPoint (formulaPoint P σ π d φ) (pairPoint (namePoint P x) (termPoint P σ π d t))


end Points
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
