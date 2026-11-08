/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstantsCodes

/-! # The actual constant-polynomial chart in every parameter slice

Both arrows are constructed from the ordinary recursive code maps. Their
source/target guards, parameter equations and inverse equations are proved
on the original carriers, including when the parameter carrier is empty.
No constant-family code comparison is supplied as a hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family}

def constantLiftCode (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ) : ℕ :=
  Nat.pair (Nat.unpair n).1 (constantLift p (Nat.unpair n).1 (Nat.unpair n).2)

def constantUnliftCode (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ) : ℕ :=
  Nat.pair (Nat.unpair n).1 (constantUnlift p (Nat.unpair n).2)

theorem constantLiftCode_primrec (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec (constantLiftCode p) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    ((constantLift_primrec p).comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

theorem constantUnliftCode_primrec (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec (constantUnliftCode p) :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    ((constantUnlift_primrec p).comp (Primrec.snd.comp Primrec.unpair))

theorem constantLiftCode_parameter (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ) :
    (Nat.unpair (constantLiftCode p n)).1=(Nat.unpair n).1 := by
  simp only [constantLiftCode,Nat.unpair_pair]

theorem constantUnliftCode_parameter (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ) :
    (Nat.unpair (constantUnliftCode p n)).1=(Nat.unpair n).1 := by
  simp only [constantUnliftCode,Nat.unpair_pair]

theorem constantUnliftCode_liftCode (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ) :
    constantUnliftCode p (constantLiftCode p n)=n := by
  simp only [constantUnliftCode,constantLiftCode,Nat.unpair_pair,constantUnlift_lift,Nat.pair_unpair]

variable (R A B : Total.TotalCategory P) (X Y : Over R)

def constantCoefficient (p : SyntaxPolynomial (Total.TotalCategory P)) : Total.TotalCategory P := ⟨carrier A.obj B.obj p⟩

def constantSource (p : SyntaxPolynomial (Total.TotalCategory P)) : Over R :=
  object R X Y (.coefficient (constantCoefficient A B p))

def constantTarget (p : SyntaxPolynomial (Total.TotalCategory P)) : Over R :=
  object R (constantObject R A) (constantObject R B) p

theorem constantLiftCode_supported (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn:n∈(constantSource R A B X Y p).left.obj.support) :
    constantLiftCode p n∈(constantTarget R A B p).left.obj.support := by
  change (Nat.unpair n).1∈R.obj.support ∧ (Nat.unpair n).2∈(carrier A.obj B.obj p).support at hn
  change fiber R (constantObject R A) (constantObject R B) p (Nat.unpair (constantLiftCode p n))
  simpa only [constantLiftCode,Nat.unpair_pair] using constantLift_supported R A B p hn.1 hn.2

theorem constantUnliftCode_supported (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn:n∈(constantTarget R A B p).left.obj.support) :
    constantUnliftCode p n∈(constantSource R A B X Y p).left.obj.support := by
  have hs := constantUnlift_supported R A B p
    (r:=(Nat.unpair n).1) (u:=(Nat.unpair n).2) hn
  change (Nat.unpair (constantUnliftCode p n)).1∈R.obj.support ∧
    (Nat.unpair (constantUnliftCode p n)).2∈(carrier A.obj B.obj p).support
  simpa only [constantUnliftCode,Nat.unpair_pair] using hs

theorem constantLiftCode_unliftCode (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn:n∈(constantTarget R A B p).left.obj.support) :
    constantLiftCode p (constantUnliftCode p n)=n := by
  have h := constantLift_unlift R A B p
    (r:=(Nat.unpair n).1) (u:=(Nat.unpair n).2) hn
  simp only [constantLiftCode,constantUnliftCode,Nat.unpair_pair,h,Nat.pair_unpair]

/-- The uniform structural map crosses two actual raw presentations. Its
proper-support and parameter laws have already been proved above. -/
def constantForward (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantSource R A B X Y p ⟶ constantTarget R A B p := by
  let f : (constantSource R A B X Y p).left ⟶ (constantTarget R A B p).left :=
    ⟨Total.totalFromFunction (constantLiftCode p) (constantLiftCode_primrec p).to_comp
      (constantLiftCode_supported R A B X Y p),Total.totalFromFunction_total _ _ _⟩
  refine Over.homMk f ?_
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hfn : Total.val f.hom n=Part.some (constantLiftCode p n) :=
    Part.eq_some_iff.mpr ((Total.mem_totalFromFunction (constantLiftCode p) (constantLiftCode_primrec p).to_comp
      (constantLiftCode_supported R A B X Y p) n _).mpr ⟨hn,rfl⟩)
  have hout : Total.val (constantTarget R A B p).hom.hom (constantLiftCode p n)=
      Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph R (constantObject R A) (constantObject R B) p _ _).mpr
      ⟨constantLiftCode_supported R A B X Y p n hn,(constantLiftCode_parameter p n).symm⟩)
  have hin : Total.val (constantSource R A B X Y p).hom.hom n=Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph R X Y (.coefficient (constantCoefficient A B p)) n _).mpr
      ⟨hn,rfl⟩)
  change Total.val (f.hom ≫ (constantTarget R A B p).hom.hom) n =
    Total.val (constantSource R A B X Y p).hom.hom n
  rw [Total.val_comp,hfn,Part.bind_some,hout,hin]

def constantBackward (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantTarget R A B p ⟶ constantSource R A B X Y p := by
  let f : (constantTarget R A B p).left ⟶ (constantSource R A B X Y p).left :=
    ⟨Total.totalFromFunction (constantUnliftCode p) (constantUnliftCode_primrec p).to_comp
      (constantUnliftCode_supported R A B X Y p),Total.totalFromFunction_total _ _ _⟩
  refine Over.homMk f ?_
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hfn : Total.val f.hom n=Part.some (constantUnliftCode p n) :=
    Part.eq_some_iff.mpr ((Total.mem_totalFromFunction (constantUnliftCode p) (constantUnliftCode_primrec p).to_comp
      (constantUnliftCode_supported R A B X Y p) n _).mpr ⟨hn,rfl⟩)
  have hout : Total.val (constantSource R A B X Y p).hom.hom (constantUnliftCode p n)=
      Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph R X Y (.coefficient (constantCoefficient A B p)) _ _).mpr
      ⟨constantUnliftCode_supported R A B X Y p n hn,(constantUnliftCode_parameter p n).symm⟩)
  have hin : Total.val (constantTarget R A B p).hom.hom n=Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph R (constantObject R A) (constantObject R B) p n _).mpr ⟨hn,rfl⟩)
  change Total.val (f.hom ≫ (constantSource R A B X Y p).hom.hom) n =
    Total.val (constantTarget R A B p).hom.hom n
  rw [Total.val_comp,hfn,Part.bind_some,hout,hin]

theorem constantForward_graph (p : SyntaxPolynomial (Total.TotalCategory P)) (n m : ℕ) :
    m∈Total.val (constantForward R A B X Y p).left.hom n ↔
      ((Nat.unpair n).1∈R.obj.support ∧ (Nat.unpair n).2∈(carrier A.obj B.obj p).support) ∧
      m=constantLiftCode p n := Total.mem_totalFromFunction (constantLiftCode p) (constantLiftCode_primrec p).to_comp
        (constantLiftCode_supported R A B X Y p) n m

theorem constantBackward_graph (p : SyntaxPolynomial (Total.TotalCategory P)) (n m : ℕ) :
    m∈Total.val (constantBackward R A B X Y p).left.hom n ↔
      fiber R (constantObject R A) (constantObject R B) p (Nat.unpair n) ∧
      m=constantUnliftCode p n := Total.mem_totalFromFunction (constantUnliftCode p) (constantUnliftCode_primrec p).to_comp
        (constantUnliftCode_supported R A B X Y p) n m

theorem constantForward_value (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn:n∈(constantSource R A B X Y p).left.obj.support) :
    Total.val (constantForward R A B X Y p).left.hom n=Part.some (constantLiftCode p n) :=
  Part.eq_some_iff.mpr ((constantForward_graph R A B X Y p n _).mpr ⟨hn,rfl⟩)

theorem constantBackward_value (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn:n∈(constantTarget R A B p).left.obj.support) :
    Total.val (constantBackward R A B X Y p).left.hom n=Part.some (constantUnliftCode p n) :=
  Part.eq_some_iff.mpr ((constantBackward_graph R A B X Y p n _).mpr ⟨hn,rfl⟩)

def constantRawIso (p : SyntaxPolynomial (Total.TotalCategory P)) :
    object R X Y (.coefficient (⟨carrier A.obj B.obj p⟩:Total.TotalCategory P)) ≅
      object R (constantObject R A) (constantObject R B) p where
  hom := constantForward R A B X Y p
  inv := constantBackward R A B X Y p
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    change Total.val ((constantForward R A B X Y p).left.hom ≫
      (constantBackward R A B X Y p).left.hom) n =
      Total.supportIdentity (constantSource R A B X Y p).left.obj.support n
    rw [Total.val_comp,constantForward_value R A B X Y p n hn,Part.bind_some,
      constantBackward_value R A B X Y p _ (constantLiftCode_supported R A B X Y p n hn),
      constantUnliftCode_liftCode]
    exact (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    change Total.val ((constantBackward R A B X Y p).left.hom ≫
      (constantForward R A B X Y p).left.hom) n =
      Total.supportIdentity (constantTarget R A B p).left.obj.support n
    rw [Total.val_comp,constantBackward_value R A B X Y p n hn,Part.bind_some,
      constantForward_value R A B X Y p _ (constantUnliftCode_supported R A B X Y p n hn),
      constantLiftCode_unliftCode R A B p n hn]
    exact (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm

theorem constantRawIso_hom_graph (p : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m∈Total.val (constantRawIso R A B X Y p).hom.left.hom (Nat.pair r u) ↔
      (r∈R.obj.support ∧ u∈(carrier A.obj B.obj p).support) ∧
      m=Nat.pair r (constantLift p r u) := by
  change m∈Total.val (constantForward R A B X Y p).left.hom (Nat.pair r u) ↔ _
  simpa only [constantLiftCode,Nat.unpair_pair] using constantForward_graph R A B X Y p (Nat.pair r u) m

theorem constantRawIso_inv_graph (p : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m∈Total.val (constantRawIso R A B X Y p).inv.left.hom (Nat.pair r u) ↔
      fiber R (constantObject R A) (constantObject R B) p (r,u) ∧
      m=Nat.pair r (constantUnlift p u) := by
  change m∈Total.val (constantBackward R A B X Y p).left.hom (Nat.pair r u) ↔ _
  simpa only [constantUnliftCode,Nat.unpair_pair] using constantBackward_graph R A B X Y p (Nat.pair r u) m

theorem constantRawIso_parameter (p : SyntaxPolynomial (Total.TotalCategory P)) :
    (constantRawIso R A B X Y p).hom.left ≫ (constantTarget R A B p).hom=
      (constantSource R A B X Y p).hom := (constantRawIso R A B X Y p).hom.w

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
