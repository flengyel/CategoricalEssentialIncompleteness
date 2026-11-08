import CategoricalEssentialIncompleteness.V46MillerBinaryCore
noncomputable section
open Set
namespace CategoricalEssentialIncompleteness.V46.Miller.Checks
example (p : ℕ → Fin 2) (n : ℕ) :
    (rho p n : ℝ) = ∑' j, (p (Nat.pair n j) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ := rho_value p n
example : Continuous (rho : (ℕ → Fin 2) → (ℕ → Set.Icc (0 : ℝ) 1)) := rho_continuous
example : Function.Surjective (rho : (ℕ → Fin 2) → (ℕ → Set.Icc (0 : ℝ) 1)) := rho_surjective
example (z : ℕ → Set.Icc (0 : ℝ) 1) :
    ({p : ℕ → Fin 2 | rho p = z}).Nonempty := representations_nonempty z
example (z : ℕ → Set.Icc (0 : ℝ) 1) :
    IsCompact ({p : ℕ → Fin 2 | rho p = z}) := representations_isCompact z
example (s : List (Fin 2)) : IsOpen ({p : ℕ → Fin 2 | bitPrefix p s.length = s}) := cylinder_isOpen s
example (s : List (Fin 2)) : IsCompact ({p : ℕ → Fin 2 | bitPrefix p s.length = s}) := cylinder_isCompact s
example (s : List (Fin 2)) : ∃ p : ℕ → Fin 2, bitPrefix p s.length = s := cylinder_nonempty s
end CategoricalEssentialIncompleteness.V46.Miller.Checks
