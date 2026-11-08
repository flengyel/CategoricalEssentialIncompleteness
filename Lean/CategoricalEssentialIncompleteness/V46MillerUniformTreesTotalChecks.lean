import CategoricalEssentialIncompleteness.V46MillerUniformTreesTotal
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
variable {P : Uniform.Family}
variable (step : Input → Part ℕ) (initial steps : ℕ → ℕ)
variable (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
variable (hi : Computable initial) (hn : Computable steps)
variable (X Y : Total.Carrier P) (I : ℕ → ℕ → ℕ → Prop)
variable (hz : ∀ x ∈ X.support,I x 0 (initial x))
variable (ht : ∀ x ∈ X.support,∀ i < steps x,∀ v,I x i v →
  ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w)
variable (hout : ∀ x ∈ X.support,∀ y,I x (steps x) y → y ∈ Y.support)

example : (⟨X⟩ : Total.TotalCategory P) ⟶ ⟨Y⟩ := totalFold step initial steps hs hi hn X Y I hz ht hout
example : isTotal (foldArrow step initial steps hs hi hn X Y I hz ht hout) :=
  foldArrow_total step initial steps hs hi hn X Y I hz ht hout
example (x y : ℕ) :
    y ∈ Total.val (totalFold step initial steps hs hi hn X Y I hz ht hout).hom x ↔
      x ∈ X.support ∧ ∃ states,Record step initial x (steps x) states ∧ states.getD (steps x) 0 = y :=
  totalFold_graph step initial steps hs hi hn X Y I hz ht hout x y
end CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
