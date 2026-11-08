import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportMembership
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedSyntaxComparison.ListTransport
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (S : DecidableVariables V)
example :
    (Syntax.predicateFunctor P).map ((SyntacticLists.stableListAlgebra 𝗣𝗔 V).membership S) ≫
      (Derivation.booleanIso (Syntax.predicateFunctor P)).hom=
    prodComparison (Syntax.predicateFunctor P) V (SyntacticLists.stableListAlgebra 𝗣𝗔 V).algebra.carrier ≫
      (NamedSyntaxComparison.mappedListStable P V).membership (Derivation.mappedEquality (Syntax.predicateFunctor P) S) :=
  map_membership P V S
example :
    (mappedList (Over.post (Syntax.predicateFunctor P)) (constantFamily V V)
      (constantFamily ((Syntax.predicateFunctor P).obj V) ((Syntax.predicateFunctor P).obj V))
      (coefficientComparison (Syntax.predicateFunctor P) V V ((Syntax.predicateFunctor P).obj V) (Iso.refl _))
      (StableListAlgebra.membershipAlgebra S)).asAlgebra ≅
      (StableListAlgebra.membershipAlgebra (Derivation.mappedEquality (Syntax.predicateFunctor P) S)).asAlgebra :=
  mappedMembershipAlgebraIso P V S
