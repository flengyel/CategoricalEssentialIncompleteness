import CategoricalEssentialIncompleteness.V46MillerSyntaxRawActionGraphs
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformParameterAlgebra
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformRelationUnique

/-! # The actual polynomial action on parameterized literal words

The chart inserts the external parameter at recursive leaves. The relation
on the resulting output tuple is the actual morphism graph on each child,
with coefficient labels and ordered tags retained. This comparison derives
from the proved action graphs and does not assume a constructor equation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P} {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable {X Y : Over R}
variable (f : uniformWordFamily R false p q ⟶ X)
  (g : uniformWordFamily R true p q ⟶ Y)

def candidateRelation : Relations.Relation
  | false,r,word,value => value∈Total.val f.left.hom (Nat.pair r word)
  | true,r,word,value => value∈Total.val g.left.hom (Nat.pair r word)

theorem liftedAction_graph (Q : SyntaxPolynomial (Total.TotalCategory P)) (r u v : ℕ)
    (hr : r∈R.obj.support)
    (hu : u∈(carrier (uniformWords false p q) (uniformWords true p q) Q).support) :
    ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y f g Q r (constantLift Q r u) v ↔
      Relations.map (fun r => r∈R.obj.support) (candidateRelation f g) (erased Q) r u v := by
  induction Q generalizing u v with
  | term =>
    change u∈(uniformWords false p q).support at hu
    change (r∈Total.val (uniformWordFamily R false p q).hom.hom (Nat.pair r u) ∧
      v∈Total.val f.left.hom (Nat.pair r u)) ↔ v∈Total.val f.left.hom (Nat.pair r u)
    apply and_iff_right
    apply (Total.mem_partialFst _ _ _ _).mpr
    exact ⟨by
      change (Nat.unpair (Nat.pair r u)).1∈R.obj.support ∧
        (Nat.unpair (Nat.pair r u)).2∈(uniformWords false p q).support
      simpa only [Nat.unpair_pair] using And.intro hr hu,by simp⟩
  | formula =>
    change u∈(uniformWords true p q).support at hu
    change (r∈Total.val (uniformWordFamily R true p q).hom.hom (Nat.pair r u) ∧
      v∈Total.val g.left.hom (Nat.pair r u)) ↔ v∈Total.val g.left.hom (Nat.pair r u)
    apply and_iff_right
    apply (Total.mem_partialFst _ _ _ _).mpr
    exact ⟨by
      change (Nat.unpair (Nat.pair r u)).1∈R.obj.support ∧
        (Nat.unpair (Nat.pair r u)).2∈(uniformWords true p q).support
      simpa only [Nat.unpair_pair] using And.intro hr hu,by simp⟩
  | coefficient C =>
    change (r∈R.obj.support ∧ u∈C.obj.support ∧ v=u) ↔
      (r∈R.obj.support ∧ topCarrier.val.Evalb (M := ℕ) ![u] ∧ v=u)
    exact ⟨fun h => ⟨h.1,by simp [topCarrier],h.2.2⟩,
      fun h => ⟨h.1,hu,h.2.2⟩⟩
  | unit =>
    have hu0 : u=0 := hu
    change (r∈R.obj.support ∧ u=0 ∧ v=u) ↔ (r∈R.obj.support ∧ u=0 ∧ v=0)
    rw [hu0]
  | product a b ia ib =>
    change (ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      X Y f g a r (Nat.unpair (constantLift (.product a b) r u)).1 (Nat.unpair v).1 ∧
      ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        X Y f g b r (Nat.unpair (constantLift (.product a b) r u)).2 (Nat.unpair v).2) ↔
      (Relations.map (fun r => r∈R.obj.support) (candidateRelation f g) (erased a) r (π₁ u) (π₁ v) ∧
        Relations.map (fun r => r∈R.obj.support) (candidateRelation f g) (erased b) r (π₂ u) (π₂ v))
    simp only [constantLift,Nat.unpair_pair,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]
    exact and_congr (ia (Nat.unpair u).1 (Nat.unpair v).1 hu.1)
      (ib (Nat.unpair u).2 (Nat.unpair v).2 hu.2)
  | sum a b ia ib =>
    change (((Nat.unpair (constantLift (.sum a b) r u)).2=0 ∧ (Nat.unpair v).2=0 ∧
      ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        X Y f g a r (Nat.unpair (constantLift (.sum a b) r u)).1 (Nat.unpair v).1) ∨
      ((Nat.unpair (constantLift (.sum a b) r u)).2=1 ∧ (Nat.unpair v).2=1 ∧
        ActionGraph R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
          X Y f g b r (Nat.unpair (constantLift (.sum a b) r u)).1 (Nat.unpair v).1)) ↔
      ((π₂ u=0 ∧ π₂ v=0 ∧ Relations.map (fun r => r∈R.obj.support)
        (candidateRelation f g) (erased a) r (π₁ u) (π₁ v)) ∨
       (π₂ u=1 ∧ π₂ v=1 ∧ Relations.map (fun r => r∈R.obj.support)
        (candidateRelation f g) (erased b) r (π₁ u) (π₁ v)))
    simp only [FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]
    rcases hu with ⟨hu0,ha⟩ | ⟨hu1,hb⟩
    · simp only [constantLift,ite_eq_left hu0,Nat.unpair_pair]
      simpa [hu0] using and_congr_right (fun _ => ia (Nat.unpair u).1 (Nat.unpair v).1 ha)
    · have hu0 : (Nat.unpair u).2≠0 := by
        have ht : (Nat.unpair u).2=1 := hu1
        omega
      simp only [constantLift,ite_eq_right hu0,Nat.unpair_pair]
      simpa [hu1] using and_congr_right (fun _ => ib (Nat.unpair u).1 (Nat.unpair v).1 hb)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
