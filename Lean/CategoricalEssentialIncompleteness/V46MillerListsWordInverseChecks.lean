import CategoricalEssentialIncompleteness.V46MillerListsWordInverse
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (V : Total.Carrier P)
example : Lists.object V ≅ Syntax.Raw.wordObject false (Lists.polynomial (⟨V⟩ : Total.TotalCategory P)) .unit := Lists.wordIso V
example (R : Total.TotalCategory P) :
    constantFamily R (Lists.object V) ≅
      constantFamily R (Syntax.Raw.wordObject false (Lists.polynomial (⟨V⟩ : Total.TotalCategory P)) .unit) :=
  Lists.wordIsoWithParameters V R
example (word value : ℕ)
    (hw : word ∈ (Syntax.Raw.uniformWords false (Lists.polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).support)
    (hv : value ∈ Lists.CodeInverse.decode word) : value ∈ (Lists.carrier V).support ∧ Lists.wordOfCode V value=word :=
  Lists.decode_supported V word value hw hv
