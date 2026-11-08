import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformConstructors
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformRelationUnique

/-! # The actual uniform evaluator's root law and comparison of candidate graphs

The root law is derived from the constructed fold, including the actual
coefficient guards. A categorical candidate still has to obtain its root
law from its algebra-morphism equation; no such equation is assumed in a
printed initiality theorem here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : CategoryTheory.Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

def foldRelation : Relations.Relation := fun formula r word value =>
  value ∈ Total.val (uniformFold hT hF formula).left.hom (Nat.pair r word)

def operationRelation : Relations.Relation := fun formula r input value =>
  value ∈ (if formula then operation hF else operation hT) (r,input)

theorem mapValues_erased (Q : SyntaxPolynomial (Total.TotalCategory P)) {r u v : ℕ}
    (h : UniformMapValues hT hF Q r u v) :
    Relations.map (fun r => r ∈ R.obj.support) (foldRelation hT hF) (erased Q) r u v := by
  induction Q generalizing u v with
  | term =>
    exact (uniformFold_graph hT hF false r u v).mpr h
  | formula =>
    exact (uniformFold_graph hT hF true r u v).mpr h
  | coefficient C =>
    exact ⟨h.1,by simp [topCarrier],h.2.2⟩
  | unit => exact h
  | product a b ia ib =>
    simpa only [erased,skeleton,SyntaxPolynomial.mapCoefficients,Relations.map,
      FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using And.intro (ia h.1) (ib h.2)
  | sum a b ia ib =>
    rcases h with ⟨hu,hv,hm⟩ | ⟨hu,hv,hm⟩
    · simpa only [erased,skeleton,SyntaxPolynomial.mapCoefficients,Relations.map,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
        (Or.inl ⟨hu,hv,ia hm⟩ :
          ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧
            Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF) (erased a)
              r (Nat.unpair u).1 (Nat.unpair v).1) ∨
          ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧
            Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF) (erased b)
              r (Nat.unpair u).1 (Nat.unpair v).1))
    · simpa only [erased,skeleton,SyntaxPolynomial.mapCoefficients,Relations.map,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
        (Or.inr ⟨hu,hv,ib hm⟩ :
          ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧
            Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF) (erased a)
              r (Nat.unpair u).1 (Nat.unpair v).1) ∨
          ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧
            Relations.map (fun r => r∈R.obj.support) (foldRelation hT hF) (erased b)
              r (Nat.unpair u).1 (Nat.unpair v).1))

theorem foldRelation_rootLaw : UniformRootLaw p q (fun r => r∈R.obj.support)
    (operationRelation hT hF) (foldRelation hT hF) := by
  intro formula r u value hu hv
  have hr := ((uniformFold_graph hT hF formula r _ value).mp hv).1
  obtain ⟨v,hm,hop⟩ := (uniformFold_constructor hT hF formula r u value hr hu).mp hv
  exact ⟨v,mapValues_erased hT hF _ hm,hop⟩

theorem operationRelation_functional (formula : Bool) (r u x y : ℕ)
    (hx : operationRelation hT hF formula r u x)
    (hy : operationRelation hT hF formula r u y) : x=y := by
  cases formula
  · exact operation_functional hT hx hy
  · exact operation_functional hF hx hy

theorem candidate_fold_value (S : Relations.Relation)
    (hS : UniformRootLaw p q (fun r => r∈R.obj.support) (operationRelation hT hF) S)
    (formula : Bool) (word : ℕ) (hw : word∈(uniformWords formula p q).support)
    (r x y : ℕ) (hx : S formula r word x) (hy : foldRelation hT hF formula r word y) : x=y :=
  uniform_relation_unique p q _ (operationRelation hT hF) S (foldRelation hT hF)
    (operationRelation_functional hT hF) hS (foldRelation_rootLaw hT hF)
    formula word hw r x y hx hy

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
