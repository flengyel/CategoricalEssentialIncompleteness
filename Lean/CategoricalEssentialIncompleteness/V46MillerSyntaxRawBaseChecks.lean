/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawBase


/-! # Statement checks in `V46MillerSyntaxRawBaseChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks

variable {P : Uniform.Family} (A B : Total.TotalCategory P)

example (p : SyntaxPolynomial (Total.TotalCategory P)) :
    (⟨carrier A.obj B.obj p⟩ : Total.TotalCategory P) ≅ p.eval.obj (A,B) := baseComparison A B p

example (C : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (baseComparison A B (.coefficient C)).inv.hom n ↔ n∈C.obj.support ∧ m=n :=
  baseComparison_coefficient_graph A B C n m

example (n : ℕ) (hn : n∈(⊤_ (Total.TotalCategory P)).obj.support) :
    Total.val (baseUnitIso (P := P)).inv.hom n=Part.some 0 := baseUnitIso_inverse_value n hn

example (C D : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (taggedSumIso C D).hom.hom n ↔
      n∈(taggedSum C.obj D.obj).support ∧ m=2*(Nat.unpair n).1+(Nat.unpair n).2 :=
  taggedSumIso_hom_graph C D n m

example (C D : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (taggedSumIso C D).inv.hom n ↔
      n∈(Total.coproduct C.obj D.obj).support ∧ m=Nat.pair (n/2) (n%2) :=
  taggedSumIso_inv_graph C D n m

example (C D : Total.TotalCategory P) :
    taggedInl C D ≫ (taggedSumIso C D).hom=Total.totalInl C D := taggedInl_chart C D

example (C D : Total.TotalCategory P) :
    taggedInr C D ≫ (taggedSumIso C D).hom=Total.totalInr C D := taggedInr_chart C D

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).hom ≫ prod.fst=
      Total.totalFst (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B a).hom :=
  baseComparison_product_fst A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).hom ≫ prod.snd=
      Total.totalSnd (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B b).hom :=
  baseComparison_product_snd A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    taggedInl (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B (.sum a b)).hom=
      (baseComparison A B a).hom ≫ coprod.inl := baseComparison_sum_inl A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    taggedInr (baseObject A B a) (baseObject A B b) ≫ (baseComparison A B (.sum a b)).hom=
      (baseComparison A B b).hom ≫ coprod.inr := baseComparison_sum_inr A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).inv ≫ Total.totalFst (baseObject A B a) (baseObject A B b)=
      prod.fst ≫ (baseComparison A B a).inv := baseComparison_product_inv_fst A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison A B (.product a b)).inv ≫ Total.totalSnd (baseObject A B a) (baseObject A B b)=
      prod.snd ≫ (baseComparison A B b).inv := baseComparison_product_inv_snd A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    coprod.inl ≫ (baseComparison A B (.sum a b)).inv=
      (baseComparison A B a).inv ≫ taggedInl (baseObject A B a) (baseObject A B b) :=
  baseComparison_sum_inv_inl A B a b

example (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    coprod.inr ≫ (baseComparison A B (.sum a b)).inv=
      (baseComparison A B b).inv ≫ taggedInr (baseObject A B a) (baseObject A B b) :=
  baseComparison_sum_inv_inr A B a b

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
