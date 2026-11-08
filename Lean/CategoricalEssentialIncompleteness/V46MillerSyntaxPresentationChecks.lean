import CategoricalEssentialIncompleteness.V46MillerSyntaxPresentation
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable (P : Uniform.Family)

example {X Y : LocalConnectedness.EnumerableCarriers.Total} (f : X ⟶ Y) :
    Total.val (ordinaryMap P f).hom = LocalConnectedness.EnumerableCarriers.val f.hom := ordinaryMap_value P f
example : PredicateCategory 𝗣𝗔 ⥤ Total.TotalCategory P := predicateFunctor P
example : predicateFunctor P ⋙ Total.underlying ≅
    PredicateInterpretation.functor 𝗣𝗔 ℕ := standardComparison P
example (C : PredicateCategory 𝗣𝗔) :
    (predicateFunctor P).obj C = (⟨predicateObject P C⟩ : Total.TotalCategory P) := predicateFunctor_object P C
example {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D) (x y : ℕ) :
    y ∈ Total.val ((predicateFunctor P).map f).hom x ↔
      ∃ a : PredicateInterpretation.Obj ℕ C,a.val=x ∧
        ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map f a).val=y := predicateFunctor_graph P f x y
example (formula : Bool) (p q : SyntacticSyntax.RawPolynomial) :
    (words P formula p q).support =
      {w : ℕ | (SyntacticSyntax.Postfix.plainCarrier formula p q).val.Evalb (M := ℕ) ![w]} := words_support P formula p q
end CategoricalEssentialIncompleteness.V46.Miller.Syntax
