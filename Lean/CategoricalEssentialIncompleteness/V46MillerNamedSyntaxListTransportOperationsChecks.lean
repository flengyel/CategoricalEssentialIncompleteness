import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportOperations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedSyntaxComparison.ListTransport
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔)
local notation "F" => Syntax.predicateFunctor P
local notation "L" => SyntacticLists.stableListAlgebra 𝗣𝗔 V
local notation "R" => NamedSyntaxComparison.mappedListStable P V
example (U : PredicateCategory 𝗣𝗔) :
    (actualParametersIso P V U).hom.f=(familyComparison (F) U (L).algebra.carrier).hom :=
  actualParametersIso_hom P V U
example : (F).map (L).singleton=(R).singleton := map_singleton P V
example : (F).map (L).append=prodComparison (F) (L).algebra.carrier (L).algebra.carrier ≫ (R).append :=
  map_append P V
example : (F).map (L).algebra.cons=prodComparison (F) V (L).algebra.carrier ≫ (R).algebra.cons :=
  map_cons P V
