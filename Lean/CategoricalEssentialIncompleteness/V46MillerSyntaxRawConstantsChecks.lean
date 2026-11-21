/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstants


/-! # The constant-polynomial chart in every parameter slice -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P:Uniform.Family} (R A B:Total.TotalCategory P) (X Y:Over R)

example (p:SyntaxPolynomial (Total.TotalCategory P)) :
    Raw.object R X Y (.coefficient (⟨Raw.carrier A.obj B.obj p⟩:Total.TotalCategory P)) ≅
      Raw.object R (Over.mk (Total.totalFst R A)) (Over.mk (Total.totalFst R B)) p :=
  Raw.constantRawIso R A B X Y p

example (p:SyntaxPolynomial (Total.TotalCategory P)) (r u m:ℕ) :
    m∈Total.val (Raw.constantRawIso R A B X Y p).hom.left.hom (Nat.pair r u) ↔
      (r∈R.obj.support ∧ u∈(Raw.carrier A.obj B.obj p).support) ∧
      m=Nat.pair r (Raw.constantLift p r u) := Raw.constantRawIso_hom_graph R A B X Y p r u m

example (p:SyntaxPolynomial (Total.TotalCategory P)) (r u m:ℕ) :
    m∈Total.val (Raw.constantRawIso R A B X Y p).inv.left.hom (Nat.pair r u) ↔
      Raw.fiber R (Over.mk (Total.totalFst R A)) (Over.mk (Total.totalFst R B)) p (r,u) ∧
      m=Nat.pair r (Raw.constantUnlift p u) := Raw.constantRawIso_inv_graph R A B X Y p r u m

example (p:SyntaxPolynomial (Total.TotalCategory P)) :
    (Raw.constantRawIso R A B X Y p).hom.left ≫
      Raw.projection R (Over.mk (Total.totalFst R A)) (Over.mk (Total.totalFst R B)) p=
      Raw.projection R X Y (.coefficient (⟨Raw.carrier A.obj B.obj p⟩:Total.TotalCategory P)) :=
  Raw.constantRawIso_parameter R A B X Y p

/-- A constant term really acquires the leaf's own stored parameter. -/
example (r u:ℕ) (hr:r∈R.obj.support) (hu:u∈A.obj.support) :
    Total.val (Raw.constantRawIso R A B X Y .term).hom.left.hom (Nat.pair r u)=
      Part.some (Nat.pair r (Nat.pair r u)) :=
  Part.eq_some_iff.mpr ((Raw.constantRawIso_hom_graph R A B X Y .term r u _).mpr ⟨⟨hr,hu⟩,rfl⟩)

/-- A coefficient label retains its whole literal payload. -/
example (C:Total.TotalCategory P) (r u:ℕ) (hr:r∈R.obj.support) (hu:u∈C.obj.support) :
    Total.val (Raw.constantRawIso R A B X Y (.coefficient C)).hom.left.hom (Nat.pair r u)=
      Part.some (Nat.pair r u) :=
  Part.eq_some_iff.mpr ((Raw.constantRawIso_hom_graph R A B X Y (.coefficient C) r u _).mpr
    ⟨⟨hr,hu⟩,rfl⟩)

example (p:SyntaxPolynomial (Total.TotalCategory P)) : Primrec (Raw.constantLiftCode p) :=
  Raw.constantLiftCode_primrec p
example (p:SyntaxPolynomial (Total.TotalCategory P)) : Primrec (Raw.constantUnliftCode p) :=
  Raw.constantUnliftCode_primrec p
