/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordCarrier
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInduction
public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionPowers

/-! # Actual finite-power coordinates of uniform derivation words

The raw tuple uses the parser's left-associated ordered pairing. Only
the finite structural charts are computed here; no extension of an
arbitrary uniformly represented operation is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation SyntacticSyntax
variable {P : Uniform.Family}
local notation "U" => (Total.underlying (P := P))

def powerProjection (X Y : Total.TotalCategory P) : (n : ℕ) → (k : Fin n) →
    ((SyntaxPolynomial.power (D := Total.TotalCategory P) .term n).eval.obj (X,Y) ⟶ X)
  | 0,k => k.elim0
  | 1,_ => 𝟙 X
  | n+2,k => Fin.lastCases prod.snd
      (fun j => prod.fst ≫ powerProjection X Y (n+1) j) k

theorem powerProjection_natural {X Y X' Y' : Total.TotalCategory P}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (k : Fin n) :
    (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n).eval.map ((f,g) : (X,Y) ⟶ (X',Y')) ≫
      powerProjection X' Y' n k=powerProjection X Y n k ≫ f := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    cases n with
    | zero => simp [SyntaxPolynomial.power,SyntaxPolynomial.eval,powerProjection]
    | succ n =>
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [powerProjection,Fin.lastCases_last]
        exact prod.map_snd _ _
      · simp only [powerProjection,Fin.lastCases_castSucc]
        change prod.map _ f ≫ (prod.fst ≫ powerProjection X' Y' (n+1) j)=_
        simp only [prod.map_fst_assoc,Category.assoc,ih]
        rfl

def finiteChild (X : Total.TotalCategory P) (n : ℕ) (k : Fin n) : finitePower X n ⟶ X :=
  (PolynomialComparison.powerIso X n).hom ≫ powerProjection X (⊤_ (Total.TotalCategory P)) n k

@[reassoc] theorem finiteChild_natural {X Y : Total.TotalCategory P} (f : X ⟶ Y) (n : ℕ) (k : Fin n) :
    finitePowerMap f n ≫ finiteChild Y n k=finiteChild X n k ≫ f := by
  rw [finiteChild,← Category.assoc,PolynomialComparison.powerIso_natural,
    Category.assoc,powerProjection_natural,← Category.assoc]
  rfl

def tupleChild : (n : ℕ) → Fin n → ℕ → ℕ
  | 0,k,_ => k.elim0
  | 1,_,u => u
  | n+2,k,u => Fin.lastCases (Nat.unpair u).2
      (fun j => tupleChild (n+1) j (Nat.unpair u).1) k

theorem rawProduct_fst (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (u : (U).obj (Syntax.Raw.baseObject X Y (.product a b))) :
    (U).map prod.fst ((U).map (Syntax.Raw.baseComparison X Y (.product a b)).hom u)=
      (U).map (Syntax.Raw.baseComparison X Y a).hom
        ⟨(Nat.unpair u.val).1,u.property.1⟩ := by
  have hp := (Total.totalFunction_eq_iff
    (Total.totalFst (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) u
      ⟨(Nat.unpair u.val).1,u.property.1⟩).mpr
    ((Total.mem_partialFst (Syntax.Raw.carrier X.obj Y.obj a) (Syntax.Raw.carrier X.obj Y.obj b)
      u.val (Nat.unpair u.val).1).mpr ⟨u.property,rfl⟩)
  have hh := congrArg (fun f : Syntax.Raw.baseObject X Y (.product a b) ⟶ a.eval.obj (X,Y) =>
    (U).map f u) (Syntax.Raw.baseComparison_product_fst X Y a b)
  erw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply] at hh
  exact hh.trans (congrArg ((U).map (Syntax.Raw.baseComparison X Y a).hom) hp)

theorem rawProduct_snd (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (u : (U).obj (Syntax.Raw.baseObject X Y (.product a b))) :
    (U).map prod.snd ((U).map (Syntax.Raw.baseComparison X Y (.product a b)).hom u)=
      (U).map (Syntax.Raw.baseComparison X Y b).hom
        ⟨(Nat.unpair u.val).2,u.property.2⟩ := by
  have hp := (Total.totalFunction_eq_iff
    (Total.totalSnd (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) u
      ⟨(Nat.unpair u.val).2,u.property.2⟩).mpr
    ((Total.mem_partialSnd (Syntax.Raw.carrier X.obj Y.obj a) (Syntax.Raw.carrier X.obj Y.obj b)
      u.val (Nat.unpair u.val).2).mpr ⟨u.property,rfl⟩)
  have hh := congrArg (fun f : Syntax.Raw.baseObject X Y (.product a b) ⟶ b.eval.obj (X,Y) =>
    (U).map f u) (Syntax.Raw.baseComparison_product_snd X Y a b)
  erw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply] at hh
  exact hh.trans (congrArg ((U).map (Syntax.Raw.baseComparison X Y b).hom) hp)

/-- Every interpreted finite projection reads the indicated original
child word, not a selected pullback witness or a common parent formula. -/
theorem powerProjection_value (X Y : Total.TotalCategory P) (n : ℕ) (k : Fin n)
    (u : (U).obj (Syntax.Raw.baseObject X Y (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n))) :
    ((U).map (powerProjection X Y n k)
      ((U).map (Syntax.Raw.baseComparison X Y (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)).hom u)).val=
      tupleChild n k u.val := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    cases n with
    | zero =>
      simp only [powerProjection,tupleChild,SyntaxPolynomial.power,Syntax.Raw.baseComparison,
        Iso.refl_hom]
      change ((U).map (𝟙 X) ((U).map (𝟙 X) u)).val=u.val
      erw [CategoryTheory.Functor.map_id]
      rfl
    | succ n =>
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [powerProjection,tupleChild,Fin.lastCases_last,SyntaxPolynomial.power]
        erw [rawProduct_snd X Y (SyntaxPolynomial.power (D := Total.TotalCategory P) .term (n+1)) .term]
        change ((U).map (𝟙 X) ⟨(Nat.unpair u.val).2,u.property.2⟩).val=(Nat.unpair u.val).2
        rw [CategoryTheory.Functor.map_id]
        rfl
      · simp only [powerProjection,tupleChild,Fin.lastCases_castSucc,CategoryTheory.Functor.map_comp_apply,
          SyntaxPolynomial.power]
        erw [rawProduct_fst X Y (SyntaxPolynomial.power (D := Total.TotalCategory P) .term (n+1)) .term]
        exact ih j ⟨(Nat.unpair u.val).1,u.property.1⟩

def rawPowerIso (X : Total.TotalCategory P) (n : ℕ) :
    finitePower X n ≅ Syntax.Raw.baseObject X (⊤_ (Total.TotalCategory P)) (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n) :=
  PolynomialComparison.powerIso X n ≪≫
    (Syntax.Raw.baseComparison X (⊤_ (Total.TotalCategory P)) (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)).symm

theorem finiteChild_value (X : Total.TotalCategory P) (n : ℕ) (k : Fin n)
    (z : (U).obj (finitePower X n)) :
    ((U).map (finiteChild X n k) z).val=
      tupleChild n k ((U).map (rawPowerIso X n).hom z).val := by
  let u := (U).map (rawPowerIso X n).hom z
  have he : (U).map (Syntax.Raw.baseComparison X (⊤_ (Total.TotalCategory P))
      (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)).hom u=
        (U).map (PolynomialComparison.powerIso X n).hom z := by
    have hh : (rawPowerIso X n).hom≫(Syntax.Raw.baseComparison X
        (⊤_ (Total.TotalCategory P)) (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)).hom=
        (PolynomialComparison.powerIso X n).hom := by
      simp only [rawPowerIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    have hv := congrArg (fun f : finitePower X n ⟶
      (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n).eval.obj
        (X,⊤_ (Total.TotalCategory P)) => (U).map f z) hh
    erw [CategoryTheory.Functor.map_comp_apply] at hv
    exact hv
  rw [finiteChild,CategoryTheory.Functor.map_comp_apply,← he]
  exact powerProjection_value X (⊤_ (Total.TotalCategory P)) n k u

theorem tupleChild_smaller (X Y : Total.TotalCategory P) (n : ℕ) (k : Fin n) (bound u : ℕ)
    (hu : u∈(Syntax.Raw.carrier X.obj Y.obj (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)).support)
    (hs : Coding.ChildSize (Syntax.Raw.skeleton (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n)) bound u) :
    FFL.FirstOrder.Arithmetic.len (tupleChild n k u)<bound := by
  induction n generalizing u with
  | zero => exact k.elim0
  | succ n ih =>
    cases n with
    | zero => simpa only [tupleChild,SyntaxPolynomial.power,Syntax.Raw.skeleton,
        SyntaxPolynomial.mapCoefficients,Coding.ChildSize] using hs
    | succ n =>
      have hsize : Coding.ChildSize
          (Syntax.Raw.skeleton (SyntaxPolynomial.power (D := Total.TotalCategory P) .term (n+1))) bound (Nat.unpair u).1 ∧
            FFL.FirstOrder.Arithmetic.len (Nat.unpair u).2<bound := by
        simpa only [SyntaxPolynomial.power,Syntax.Raw.skeleton,SyntaxPolynomial.mapCoefficients,
          Coding.ChildSize,FiniteSigmaOne.nat_pi₁_eq,SyntacticSyntax.NatVectors.nat_pi₂_eq] using hs
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa only [tupleChild,Fin.lastCases_last] using hsize.2
      · simpa only [tupleChild,Fin.lastCases_castSucc] using ih j (Nat.unpair u).1 hu.1 hsize.1

def ruleTag : (n : ℕ) → Fin (n+1) → ℕ → ℕ
  | 0,_,u => u
  | n+1,i,u => Fin.lastCases (Nat.pair u 1) (fun j => Nat.pair (ruleTag n j u) 0) i

theorem ruleTag_childSize (labels : ℕ → Total.TotalCategory P) (n : ℕ) (i : Fin (n+1))
    (bound label tuple : ℕ)
    (hs : Coding.ChildSize (Syntax.Raw.skeleton (SyntaxPolynomial.constructors labels n))
      bound (ruleTag n i (Nat.pair label tuple))) :
    Coding.ChildSize (Syntax.Raw.skeleton (SyntaxPolynomial.power (D := Total.TotalCategory P) .term i.val)) bound tuple := by
  induction n with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    trivial
  | succ n ih =>
    revert hs
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hs
      simpa [ruleTag,Fin.lastCases_last,Fin.val_last,SyntaxPolynomial.constructors,
        Syntax.Raw.skeleton,SyntaxPolynomial.mapCoefficients,Coding.ChildSize,
        FiniteSigmaOne.nat_pi₁_eq,SyntacticSyntax.NatVectors.nat_pi₂_eq,Nat.unpair_pair] using hs
    · intro hs
      apply ih j
      simpa [ruleTag,Fin.lastCases_castSucc,Fin.val_castSucc,SyntaxPolynomial.constructors,
        Syntax.Raw.skeleton,SyntaxPolynomial.mapCoefficients,Coding.ChildSize,
        FiniteSigmaOne.nat_pi₁_eq,SyntacticSyntax.NatVectors.nat_pi₂_eq,Nat.unpair_pair] using hs

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
