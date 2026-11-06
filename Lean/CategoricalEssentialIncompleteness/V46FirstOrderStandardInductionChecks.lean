import CategoricalEssentialIncompleteness.V46FirstOrderStandardInduction

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.FirstOrderStandardInductionChecks
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable {V Fm L Sent A : PredicateCategory 𝗣𝗔}
variable (logical : L ⟶ Fm) (sentence : Sent ⟶ Fm) (axioms : A ⟶ Sent)
variable (all : V ⨯ Fm ⟶ Fm) (imp : Fm ⨯ Fm ⟶ Fm)
example (P : Obj 𝗣𝗔 ℕ Fm → Prop)
    (hl : ∀ l : Obj 𝗣𝗔 ℕ L, P ((F 𝗣𝗔 ℕ).map logical l))
    (ha : ∀ a : Obj 𝗣𝗔 ℕ A, P ((F 𝗣𝗔 ℕ).map (axioms ≫ sentence) a))
    (hg : ∀ z : Obj 𝗣𝗔 ℕ (V ⨯ Fm),
      P ((F 𝗣𝗔 ℕ).map (prod.snd : V ⨯ Fm ⟶ Fm) z) → P ((F 𝗣𝗔 ℕ).map all z))
    (hm : ∀ z : Obj 𝗣𝗔 ℕ (Fm ⨯ Fm),
      P ((F 𝗣𝗔 ℕ).map (prod.fst : Fm ⨯ Fm ⟶ Fm) z) →
      P ((F 𝗣𝗔 ℕ).map imp z) → P ((F 𝗣𝗔 ℕ).map (prod.snd : Fm ⨯ Fm ⟶ Fm) z)) :
    ∀ d : Obj 𝗣𝗔 ℕ (derivationAlgebra 𝗣𝗔 (firstOrderRules logical sentence axioms all imp)).a.left,
      P ((F 𝗣𝗔 ℕ).map (derivationAlgebra 𝗣𝗔
        (firstOrderRules logical sentence axioms all imp)).a.hom d) :=
  firstOrder_conclusion_induction 𝗣𝗔 logical sentence axioms all imp P hl ha hg hm
end CategoricalEssentialIncompleteness.V46.FirstOrderStandardInductionChecks
