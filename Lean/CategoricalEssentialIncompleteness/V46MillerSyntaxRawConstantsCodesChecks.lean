/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstantsCodes


/-! # Explicit recursive constant-family polynomial codes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P:Uniform.Family} (R A B:Total.TotalCategory P)

example (p:SyntaxPolynomial (Total.TotalCategory P)) : Primrec₂ (Raw.constantLift p) := Raw.constantLift_primrec p
example (p:SyntaxPolynomial (Total.TotalCategory P)) : Primrec (Raw.constantUnlift p) := Raw.constantUnlift_primrec p

example (p:SyntaxPolynomial (Total.TotalCategory P)) (r u:ℕ) :
    Raw.constantUnlift p (Raw.constantLift p r u)=u := Raw.constantUnlift_lift p r u

example (p:SyntaxPolynomial (Total.TotalCategory P)) (r u:ℕ) :
    Raw.fiber R (Over.mk (Total.totalFst R A)) (Over.mk (Total.totalFst R B)) p
      (r,Raw.constantLift p r u) ↔ r∈R.obj.support ∧ u∈(Raw.carrier A.obj B.obj p).support :=
  Raw.constant_fiber_iff R A B p r u

example (p:SyntaxPolynomial (Total.TotalCategory P)) (r u:ℕ)
    (h:Raw.fiber R (Over.mk (Total.totalFst R A)) (Over.mk (Total.totalFst R B)) p (r,u)) :
    Raw.constantLift p r (Raw.constantUnlift p u)=u := Raw.constantLift_unlift R A B p h

example (a b:SyntaxPolynomial (Total.TotalCategory P)) (r u v:ℕ) :
    Raw.constantLift (.product a b) r (Nat.pair u v)=
      Nat.pair (Raw.constantLift a r u) (Raw.constantLift b r v) := Raw.constantLift_product a b r u v

example (a b:SyntaxPolynomial (Total.TotalCategory P)) (r u:ℕ) :
    Raw.constantLift (.sum a b) r (Nat.pair u 0)=Nat.pair (Raw.constantLift a r u) 0 :=
  Raw.constantLift_inl a b r u

example (a b:SyntaxPolynomial (Total.TotalCategory P)) (r u:ℕ) :
    Raw.constantLift (.sum a b) r (Nat.pair u 1)=Nat.pair (Raw.constantLift b r u) 1 :=
  Raw.constantLift_inr a b r u

example (C:Total.TotalCategory P) (r u:ℕ) : Raw.constantLift (.coefficient C) r u=u := rfl
example (r u:ℕ) : Raw.constantLift (P:=P) .unit r u=u := rfl
