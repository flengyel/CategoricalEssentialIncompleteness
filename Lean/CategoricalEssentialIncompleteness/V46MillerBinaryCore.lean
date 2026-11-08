import Mathlib.Analysis.Real.OfDigits
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.List.OfFn

/-! # Binary representations and their compact fibers for the Miller construction -/

noncomputable section
open scoped BigOperators
open Set

namespace CategoricalEssentialIncompleteness.V46.Miller

abbrev Bits := ℕ → Fin 2
abbrev Word := List (Fin 2)
abbrev Point := ℕ → Set.Icc (0 : ℝ) 1

def bitPrefix (p : Bits) (n : ℕ) : Word := List.ofFn (fun i : Fin n => p i)

def cylinder (s : Word) : Set Bits := {p | bitPrefix p s.length = s}

@[simp] theorem prefix_length (p : Bits) (n : ℕ) : (bitPrefix p n).length = n := by
  simp [bitPrefix]

@[simp] theorem prefix_getElem (p : Bits) (n i : ℕ) (hi : i < (bitPrefix p n).length) :
    (bitPrefix p n)[i] = p i := by
  simp [bitPrefix]

theorem prefix_take (p : Bits) (n k : ℕ) :
    (bitPrefix p n).take k = bitPrefix p (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_take, prefix_getElem]

def extend (s : Word) : Bits := fun i => s[i]?.getD 0

@[simp] theorem prefix_extend (s : Word) : bitPrefix (extend s) s.length = s := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [bitPrefix, extend]

theorem cylinder_nonempty (s : Word) : (cylinder s).Nonempty :=
  ⟨extend s, prefix_extend s⟩

@[simp] theorem mem_cylinder_prefix (p : Bits) (n : ℕ) : p ∈ cylinder (bitPrefix p n) := by
  simp [cylinder]

theorem mem_cylinder_iff (p : Bits) (s : Word) :
    p ∈ cylinder s ↔ ∀ i (hi : i < s.length), p i = s[i] := by
  constructor
  · intro h i hi
    change bitPrefix p s.length = s at h
    have hh := congrArg (fun l : Word => l[i]?) h
    simpa [bitPrefix, hi] using hh
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simpa only [prefix_getElem] using h i hj

theorem cylinder_eq_iInter (s : Word) :
    cylinder s = ⋂ i : Fin s.length, {p : Bits | p i = s.get i} := by
  ext p
  simp only [mem_cylinder_iff, Set.mem_iInter]
  exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i,hi⟩⟩

theorem cylinder_isOpen (s : Word) : IsOpen (cylinder s) := by
  rw [cylinder_eq_iInter]
  apply isOpen_iInter_of_finite
  intro i
  exact IsOpen.preimage (f := fun p : Bits => p (i : ℕ))
    (continuous_apply (i : ℕ)) (isOpen_discrete ({s.get i} : Set (Fin 2)))

theorem cylinder_isClosed (s : Word) : IsClosed (cylinder s) := by
  rw [cylinder_eq_iInter]
  exact isClosed_iInter (fun i => isClosed_eq (continuous_apply (i : ℕ)) continuous_const)

theorem cylinder_isCompact (s : Word) : IsCompact (cylinder s) :=
  (cylinder_isClosed s).isCompact

/-- The printed binary expansion, with the fixed recursive pairing `Nat.pair`. -/
def rho (p : Bits) : Point := fun n =>
  ⟨Real.ofDigits (fun j => p (Nat.pair n j)),
    Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

@[simp] theorem rho_value (p : Bits) (n : ℕ) :
    (rho p n : ℝ) = ∑' j, (p (Nat.pair n j) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ := rfl

theorem rho_continuous : Continuous rho := by
  apply continuous_pi
  intro n
  exact Continuous.subtype_mk (Real.continuous_ofDigits.comp
    (continuous_pi (fun j => continuous_apply (Nat.pair n j)))) _

theorem rho_surjective : Function.Surjective rho := by
  intro z
  have h : ∀ n, ∃ d : Bits, Real.ofDigits d = (z n : ℝ) := by
    intro n
    obtain ⟨d, _, hd⟩ := Real.ofDigits_SurjOn (b := 2) (by decide) (z n).property
    exact ⟨d, hd⟩
  choose d hd using h
  refine ⟨fun k => d (Nat.unpair k).1 (Nat.unpair k).2, ?_⟩
  funext n
  apply Subtype.ext
  change Real.ofDigits (fun j => d (Nat.unpair (Nat.pair n j)).1
    (Nat.unpair (Nat.pair n j)).2) = (z n : ℝ)
  simpa only [Nat.unpair_pair] using hd n

def representations (z : Point) : Set Bits := {p | rho p = z}

theorem representations_nonempty (z : Point) : (representations z).Nonempty :=
  rho_surjective z

theorem representations_isClosed (z : Point) : IsClosed (representations z) :=
  isClosed_eq rho_continuous continuous_const

theorem representations_isCompact (z : Point) : IsCompact (representations z) :=
  (representations_isClosed z).isCompact

end CategoricalEssentialIncompleteness.V46.Miller
