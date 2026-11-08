import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformRelationUnique
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) (Q : ℕ → Prop)
    (op R S : Relations.Relation)
    (hOp : ∀ formula r u x y,op formula r u x → op formula r u y → x=y)
    (hR : UniformRootLaw p q Q op R) (hS : UniformRootLaw p q Q op S) :
    ∀ formula word,word ∈ (uniformWords formula p q).support →
      ∀ r x y,R formula r word x → S formula r word y → x=y :=
  uniform_relation_unique p q Q op R S hOp hR hS
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
