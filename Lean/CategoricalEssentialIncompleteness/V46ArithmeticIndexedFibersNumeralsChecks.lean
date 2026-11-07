import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersNumerals
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (e : ℕ) : (⊤_ (TotalSplit 𝗣𝗔)) ⨿ complement e ≅ ArithmeticIndexedAxioms.parameter :=
  numeralSplitIso e
example (e : ℕ) : coprod.inl ≫ (numeralSplitIso e).hom = numeral e := numeralSplitIso_inl e
example (e : ℕ) : coprod.inr ≫ (numeralSplitIso e).hom = complementInclusion e := numeralSplitIso_inr e
example (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    Over (ArithmeticIndexedAxioms.parameter ⨯ X) ≌ Over X × Over (complement e ⨯ X) :=
  sliceEquivalence e X
example (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    fiberMap e X = prod.lift (terminal.from X ≫ numeral e) (𝟙 X) := fiberMap_primitive e X
example (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    complementMap e X = prod.map (complementInclusion e) (𝟙 X) := complementMap_primitive e X
example (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    (sliceEquivalence e X).functor =
      (Over.pullback (fiberMap e X)).prod' (Over.pullback (complementMap e X)) := rfl

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
