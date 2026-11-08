import CategoricalEssentialIncompleteness.V46MillerListsDecoder
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller
example : Partrec Lists.CodeInverse.decode := Lists.CodeInverse.decode_partrec
example {P : Uniform.Family} (V : Total.Carrier P) (n : ℕ) :
    n ∈ Lists.CodeInverse.decode (Lists.wordOfCode V n) := Lists.CodeInverse.decode_wordOfCode V n
