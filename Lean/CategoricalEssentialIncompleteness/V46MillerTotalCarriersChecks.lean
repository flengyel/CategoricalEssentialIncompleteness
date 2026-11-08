import CategoricalEssentialIncompleteness.V46MillerTotalCarriers
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example (X : Carrier P) : (partialObject X).base = Uniform.N P := rfl
example (X : Carrier P) : (partialObject X).domain = Uniform.setIdem (Uniform.N P) X.support X.enumerable := rfl
example : Category (Carrier P) := inferInstance
example : RestrictionCategory (Carrier P) := inferInstance
example : Ranges (Carrier P) := inferInstance
example : Splits (Carrier P) := inferInstance
example {X Y : Carrier P} (f : X ⟶ Y) :
    ∃ e : ℕ,∀ p ∈ P.oracles,∀ x y,y ∈ val f x ↔ y ∈ OracleProgram.numberedEval e p x := val_represented f
example {X Y : Carrier P} (f : X ⟶ Y) : isTotal f ↔ ∀ x ∈ X.support,(val f x).Dom := total_iff f
example {X Y : Carrier P} (f : X ⟶ Y) (x y : ℕ) (h : y ∈ val f x) : x ∈ X.support ∧ y ∈ Y.support :=
  ⟨val_source f x y h,val_target f x y h⟩
example {X Y : Carrier P} (f : X ⟶ Y) : support (Ranges.range f) = {y | ∃ x,y ∈ val f x} := support_range f
example {X : Carrier P} (a : Idem X) : into a ≫ outof a = 𝟙 (subcarrier a) := into_outof a
example {X : Carrier P} (a : Idem X) : outof a ≫ into a = a.hom := outof_into a
end CategoricalEssentialIncompleteness.V46.Miller.Total
