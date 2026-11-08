import CategoricalEssentialIncompleteness.V46MillerSyntaxRelationUnique
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Relations.Checks
example (a b : RawPolynomial) (Q : ℕ → Prop) (op R S : Relation)
    (hOp : ∀ formula p u x y,op formula p u x → op formula p u y → x=y)
    (hR : RootLaw a b Q op R) (hS : RootLaw a b Q op S) :
    ∀ formula word,(Postfix.plainCarrier formula a b).val.Evalb (M := ℕ) ![word] →
      ∀ p x y,R formula p word x → S formula p word y → x=y :=
  plain_word_relation_unique a b Q op R S hOp hR hS
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Relations.Checks
