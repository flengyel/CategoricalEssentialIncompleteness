/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxComparison
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Identical-word charts for PA-described uniform syntax

The charts preserve scalar words, including stored binder names and
ordered child records. The input chart uses the proved polynomial
finite-geometry comparison; no initiality property of the predicate
functor is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family)

def identityIso (X Y : Total.TotalCategory P) (h : ∀ n,n∈X.obj.support ↔ n∈Y.obj.support) : X ≅ Y where
  hom := ⟨Total.totalFromFunction id Computable.id (fun n hn => (h n).mp hn),
    Total.totalFromFunction_total _ _ _⟩
  inv := ⟨Total.totalFromFunction id Computable.id (fun n hn => (h n).mpr hn),
    Total.totalFromFunction_total _ _ _⟩
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hf : Total.val (Total.totalFromFunction id Computable.id (fun n hn => (h n).mp hn)) n=
        Part.some n := Part.eq_some_iff.mpr ((Total.mem_totalFromFunction _ _ _ n n).mpr ⟨hn,rfl⟩)
    change Total.val ((Total.totalFromFunction id Computable.id (fun n hn => (h n).mp hn)) ≫
      (Total.totalFromFunction id Computable.id (fun n hn => (h n).mpr hn))) n = Total.val (𝟙 X.obj) n
    rw [Total.val_comp,hf,Part.bind_some]
    exact (Part.eq_some_iff.mpr ((Total.mem_totalFromFunction _ _ _ n n).mpr ⟨(h n).mp hn,rfl⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hf : Total.val (Total.totalFromFunction id Computable.id (fun n hn => (h n).mpr hn)) n=
        Part.some n := Part.eq_some_iff.mpr ((Total.mem_totalFromFunction _ _ _ n n).mpr ⟨hn,rfl⟩)
    change Total.val ((Total.totalFromFunction id Computable.id (fun n hn => (h n).mpr hn)) ≫
      (Total.totalFromFunction id Computable.id (fun n hn => (h n).mp hn))) n = Total.val (𝟙 Y.obj) n
    rw [Total.val_comp,hf,Part.bind_some]
    exact (Part.eq_some_iff.mpr ((Total.mem_totalFromFunction _ _ _ n n).mpr ⟨(h n).mpr hn,rfl⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm

theorem identityIso_graph (X Y : Total.TotalCategory P) (h : ∀ n,n∈X.obj.support ↔ n∈Y.obj.support) (n m : ℕ) :
    m∈Total.val (identityIso P X Y h).hom.hom n ↔ n∈X.obj.support ∧ m=n :=
  Total.mem_totalFromFunction id Computable.id (fun n hn => (h n).mp hn) n m

theorem identityIso_inverse_graph (X Y : Total.TotalCategory P) (h : ∀ n,n∈X.obj.support ↔ n∈Y.obj.support) (n m : ℕ) :
    m∈Total.val (identityIso P X Y h).inv.hom n ↔ n∈Y.obj.support ∧ m=n :=
  Total.mem_totalFromFunction id Computable.id (fun n hn => (h n).mpr hn) n m

def wordIso (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) :
    Syntax.Raw.wordObject formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b) ≅
      (Syntax.predicateFunctor P).obj (SyntacticSyntax.Postfix.plainCarrier formula a b) :=
  identityIso P _ _ (fun word => by
    rw [Syntax.predicateFunctor_object]
    exact Syntax.Raw.uniformWords_mapped a b formula word)

def storedWordIso (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) :
    Syntax.Raw.wordObject formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b) ≅
      (Syntax.predicateFunctor P).obj (SyntacticSyntax.Postfix.carrier formula a b) :=
  identityIso P _ _ (fun word => by
    rw [Syntax.predicateFunctor_object]
    exact (Syntax.Raw.uniformWords_mapped a b formula word).trans
      (SyntacticSyntax.Postfix.carrier_plain_model formula a b word).symm)

theorem wordIso_graph (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) (word output : ℕ) :
    output∈Total.val (wordIso P a b formula).hom.hom word ↔
      word∈(Syntax.Raw.uniformWords formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b)).support ∧
        output=word :=
  identityIso_graph P _ _ (fun word => by
    rw [Syntax.predicateFunctor_object]
    exact Syntax.Raw.uniformWords_mapped a b formula word) word output

theorem storedWordIso_graph (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) (word output : ℕ) :
    output∈Total.val (storedWordIso P a b formula).hom.hom word ↔
      word∈(Syntax.Raw.uniformWords formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b)).support ∧
        output=word :=
  identityIso_graph P _ _ (fun word => by
    rw [Syntax.predicateFunctor_object]
    exact (Syntax.Raw.uniformWords_mapped a b formula word).trans
      (SyntacticSyntax.Postfix.carrier_plain_model formula a b word).symm) word output

/-- Literal raw inputs, including ordered children and original tags, are compared with
the image of the source chosen polynomial. -/
def inputIso (X Y : PredicateCategory 𝗣𝗔) (X' Y' : Total.TotalCategory P)
    (iX : X' ≅ (Syntax.predicateFunctor P).obj X)
    (iY : Y' ≅ (Syntax.predicateFunctor P).obj Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P p) ≅
      (Syntax.predicateFunctor P).obj (p.eval.obj (X,Y)) :=
  Syntax.Raw.baseComparison X' Y' (Syntax.Polynomial.mapped P p) ≪≫
    (Syntax.Polynomial.mapped P p).eval.mapIso
      { hom := (iX.hom,iY.hom)
        inv := (iX.inv,iY.inv)
        hom_inv_id := Prod.ext iX.hom_inv_id iY.hom_inv_id
        inv_hom_id := Prod.ext iX.inv_hom_id iY.inv_hom_id } ≪≫
      (Syntax.Polynomial.component P p (X,Y)).symm

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
