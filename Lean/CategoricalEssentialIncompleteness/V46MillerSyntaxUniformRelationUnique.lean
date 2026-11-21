/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInduction
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRelationUnique

/-! # Constructor uniqueness for every uniform coefficient signature

Coefficient guards may be forgotten only in comparing two output tuples: both actions
preserve each coefficient value. Word/input guards remain in the root laws and
structural induction. The categorical application still derives these laws for every
algebra morphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

theorem children_erased (H : Bool → ℕ → Prop) (Q : SyntaxPolynomial (Total.TotalCategory P)) (u : ℕ) :
    WordInduction.ChildHolds H (erased Q) u ↔ UniformChildren H Q u := by
  induction Q generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product c d ic id =>
      change (WordInduction.ChildHolds H (erased c) (π₁ u) ∧
        WordInduction.ChildHolds H (erased d) (π₂ u)) ↔
        UniformChildren H c (Nat.unpair u).1 ∧ UniformChildren H d (Nat.unpair u).2
      rw [FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,ic,id]
  | sum c d ic id =>
      change (if π₂ u=0 then WordInduction.ChildHolds H (erased c) (π₁ u)
        else WordInduction.ChildHolds H (erased d) (π₁ u)) ↔
        (if (Nat.unpair u).2=0 then UniformChildren H c (Nat.unpair u).1
          else UniformChildren H d (Nat.unpair u).1)
      rw [FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]
      by_cases h : (Nat.unpair u).2=0
      · simpa only [ite_eq_left h] using ic (Nat.unpair u).1
      · simpa only [ite_eq_right h] using id (Nat.unpair u).1

/-- The guarded constructor equation for a candidate relation. -/
def UniformRootLaw (p q : SyntaxPolynomial (Total.TotalCategory P)) (Q : ℕ → Prop)
    (op R : Relations.Relation) : Prop :=
  ∀ (formula : Bool) (r u value : ℕ),
    u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support →
    R formula r (constructor formula (skeleton (if formula then q else p)) u) value →
      ∃ v,Relations.map Q R (erased (if formula then q else p)) r u v ∧ op formula r v value

theorem uniform_relation_unique (p q : SyntaxPolynomial (Total.TotalCategory P)) (Q : ℕ → Prop)
    (op R S : Relations.Relation)
    (hOp : ∀ formula r u x y,op formula r u x → op formula r u y → x=y)
    (hR : UniformRootLaw p q Q op R) (hS : UniformRootLaw p q Q op S) :
    ∀ formula word,word ∈ (uniformWords formula p q).support →
      ∀ r x y,R formula r word x → S formula r word y → x=y := by
  apply uniform_word_induction p q
    (fun formula word => ∀ r x y,R formula r word x → S formula r word y → x=y)
  intro formula u hu hc r x y hx hy
  obtain ⟨v,hv,hox⟩ := hR formula r u x hu hx
  obtain ⟨w,hw,hoy⟩ := hS formula r u y hu hy
  have hchildren : WordInduction.ChildHolds
      (fun formula word => ∀ r x y,R formula r word x → S formula r word y → x=y)
      (erased (if formula then q else p)) u := (children_erased _ _ _).mpr hc
  have he := Relations.map_compare Q R S (erased (if formula then q else p)) r u v w hchildren hv hw
  subst w
  exact hOp formula r v x y hox hoy

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
