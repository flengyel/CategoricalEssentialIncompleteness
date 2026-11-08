import CategoricalEssentialIncompleteness.V46MillerListsWordCodes
noncomputable section
open FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (V : Total.Carrier P)
example : Primrec (Lists.wordOfCode V) := Lists.wordOfCode_primrec V
example (v rest : ℕ) :
    Lists.wordOfCode V (adjoin v rest)=Lists.consWord V v (Lists.wordOfCode V rest) :=
  Lists.wordOfCode_adjoin V v rest
example (n word : ℕ) : word ∈ Total.val (Lists.wordMap V).hom n ↔
    n ∈ (Lists.carrier V).support ∧ word=Lists.wordOfCode V n := Lists.wordMap_graph V n word
