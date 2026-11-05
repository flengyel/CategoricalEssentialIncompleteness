import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentCore

/-! The invariant is an actual family equation on original/result carriers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.substitutionAlgebra.a ⟶
    (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters (OptionSyntax.obj S.algebra.a.2)) := S.absenceMask

example {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) (hm : m ≫ S.absenceMask = m ≫ S.absenceResult) :
    S.termPairGood A.1.hom (m.1.left ≫ prod.snd) ∧
      S.formulaPairGood A.2.hom (m.2.left ≫ prod.snd) := S.absence_recursive_good m hm
