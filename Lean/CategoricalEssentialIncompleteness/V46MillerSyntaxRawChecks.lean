import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw

noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
open CategoricalEssentialIncompleteness.V46
variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)

example (p : SyntaxPolynomial (Total.TotalCategory P)) :
    Uniform.Enumerable P (Raw.fiber R X Y p) := Raw.fiber_enumerable R X Y p

example (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h : Raw.fiber R X Y p (r,u)) : r ∈ R.obj.support := Raw.fiber_parameter R X Y p h

example (p : SyntaxPolynomial (Total.TotalCategory P)) {r u : ℕ}
    (h : Raw.fiber R X Y p (r,u)) : u ∈ (Raw.carrier X.left.obj Y.left.obj p).support :=
  Raw.fiber_carrier R X Y p h

example (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v m : ℕ) :
    m ∈ Total.val (Raw.productFst R X Y a b).left.hom (Nat.pair r (Nat.pair u v)) ↔
      Raw.fiber R X Y a (r,u) ∧ Raw.fiber R X Y b (r,v) ∧ m=Nat.pair r u :=
  Raw.productFst_graph R X Y a b r u v m

example (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u v m : ℕ) :
    m ∈ Total.val (Raw.productSnd R X Y a b).left.hom (Nat.pair r (Nat.pair u v)) ↔
      Raw.fiber R X Y a (r,u) ∧ Raw.fiber R X Y b (r,v) ∧ m=Nat.pair r v :=
  Raw.productSnd_graph R X Y a b r u v m

example (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m ∈ Total.val (Raw.sumInl R X Y a b).left.hom (Nat.pair r u) ↔
      Raw.fiber R X Y a (r,u) ∧ m=Nat.pair r (Nat.pair u 0) :=
  Raw.sumInl_graph R X Y a b r u m

example (a b : SyntaxPolynomial (Total.TotalCategory P)) (r u m : ℕ) :
    m ∈ Total.val (Raw.sumInr R X Y a b).left.hom (Nat.pair r u) ↔
      Raw.fiber R X Y b (r,u) ∧ m=Nat.pair r (Nat.pair u 1) :=
  Raw.sumInr_graph R X Y a b r u m

example (p : SyntaxPolynomial (Total.TotalCategory P)) (r u : ℕ) :
    r ∈ Total.val (Raw.projection R X Y p).hom (Nat.pair r u) ↔ Raw.fiber R X Y p (r,u) := by
  simpa only [Nat.unpair_pair,and_true] using Raw.projection_graph R X Y p (Nat.pair r u) r
