import CategoricalEssentialIncompleteness.V46SyntacticSyntaxWords

/-! Postfix word operations at arbitrary PA-model lengths. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Words
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (a b c : M) : append (append a b) c = append a (append b c) := append_assoc a b c
example (a b : M) : len (append a b) = len a + len b := len_append a b
example (a b i : M) (hi : i < len a) : nth (append a b) i = nth a i := nth_append_left a b i hi
example (a b i : M) : nth (append a b) (len a + i) = nth b i := nth_append_right a b i
example (a : M) : a = 0 ∨ ∃ b x : M, a = concat b x := nil_or_snoc a
example (a b x y : M) (h : concat a x = concat b y) : a = b ∧ x = y := snoc_injective a b x y h
