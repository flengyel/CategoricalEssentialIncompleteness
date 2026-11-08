import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformDecomposition
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize

/-! # Arbitrary-property induction with all uniform coefficient objects

The induction predicate is external and unrestricted. Only the structural
size function is read through the old arithmetic parser; all actual word
and coefficient membership conditions remain uniform positive predicates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def UniformChildren (H : Bool → ℕ → Prop) : SyntaxPolynomial (Total.TotalCategory P) → ℕ → Prop
  | .term,u => H false u
  | .formula,u => H true u
  | .coefficient _,_ => True
  | .unit,_ => True
  | .product a b,u => UniformChildren H a (Nat.unpair u).1 ∧ UniformChildren H b (Nat.unpair u).2
  | .sum a b,u => if (Nat.unpair u).2=0 then UniformChildren H a (Nat.unpair u).1
      else UniformChildren H b (Nat.unpair u).1

theorem uniformChildren_of_smaller (p q Q : SyntaxPolynomial (Total.TotalCategory P))
    (H : Bool → ℕ → Prop) (n : ℕ) {u : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support)
    (hs : ChildSize (skeleton Q) n u)
    (h : ∀ (formula : Bool) (word : ℕ),len word<n →
      word ∈ (uniformWords formula p q).support → H formula word) : UniformChildren H Q u := by
  induction Q generalizing u with
  | term => exact h false u (by simpa [skeleton,SyntaxPolynomial.mapCoefficients,ChildSize] using hs) hu
  | formula => exact h true u (by simpa [skeleton,SyntaxPolynomial.mapCoefficients,ChildSize] using hs) hu
  | coefficient _ => trivial
  | unit => trivial
  | product c d ic id =>
      have hc : ChildSize (skeleton c) n (Nat.unpair u).1 ∧
          ChildSize (skeleton d) n (Nat.unpair u).2 := by
        simpa only [skeleton,SyntaxPolynomial.mapCoefficients,ChildSize,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hs
      exact ⟨ic hu.1 hc.1,id hu.2 hc.2⟩
  | sum c d ic id =>
      rcases hu with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · have hc : ChildSize (skeleton c) n (Nat.unpair u).1 := by
          simpa [skeleton,SyntaxPolynomial.mapCoefficients,ChildSize,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hk] using hs
        simpa only [UniformChildren,ite_eq_left hk] using ic hv hc
      · have hc : ChildSize (skeleton d) n (Nat.unpair u).1 := by
          simpa [skeleton,SyntaxPolynomial.mapCoefficients,ChildSize,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hk] using hs
        have hk0 : (Nat.unpair u).2≠0 := by omega
        simpa only [UniformChildren,ite_eq_right hk0] using id hv hc

theorem uniform_word_induction (p q : SyntaxPolynomial (Total.TotalCategory P)) (H : Bool → ℕ → Prop)
    (root : ∀ (formula : Bool) (u : ℕ),
      u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support →
      UniformChildren H (if formula then q else p) u →
        H formula (constructor formula (skeleton (if formula then q else p)) u)) :
    ∀ formula word,word ∈ (uniformWords formula p q).support → H formula word := by
  have aux : ∀ n : ℕ,∀ formula word,len word=n →
      word ∈ (uniformWords formula p q).support → H formula word := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro formula word hn hw
        obtain ⟨u,hu,he⟩ := uniformWords_decomposition p q formula hw
        subst word
        apply root formula u hu
        apply uniformChildren_of_smaller p q (if formula then q else p) H n hu
        · rw [← hn]
          exact (childSizeGraph_eval _ _ _).mp
            (children_smaller formula (skeleton (if formula then q else p)) u)
        · intro sort child hlt hc
          exact ih (len child) hlt sort child rfl hc
  intro formula word hw
  exact aux (len word) formula word rfl hw

theorem uniform_constructor_injective (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool)
    {u v : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support)
    (hv : v ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support)
    (he : constructor formula (skeleton (if formula then q else p)) u=
      constructor formula (skeleton (if formula then q else p)) v) : u=v := by
  have hu' := rawInput_erased p q (if formula then q else p) hu
  have hv' := rawInput_erased p q (if formula then q else p) hv
  have he' : constructor formula (erased (if formula then q else p)) u=
      constructor formula (erased (if formula then q else p)) v := by
    simpa only [erased_constructor] using he
  exact Postfix.constructor_injective formula (erased p) (erased q)
    (erased (if formula then q else p)) u v hu' hv' he'

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
