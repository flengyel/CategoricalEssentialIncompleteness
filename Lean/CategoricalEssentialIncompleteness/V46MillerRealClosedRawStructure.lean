import CategoricalEssentialIncompleteness.V46MillerRealClosedAxioms
import CategoricalEssentialIncompleteness.V46NamedFiniteSemantics
import Mathlib.Tactic.FinCases

/-! # The actual sixteen field matrices in an arbitrary named structure

This interpretation has only the total functions and relations of the
fixed bounded language. No algebraic or order structure is an input.
Every law below is extracted from one of the original literal matrices.
-/
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u

structure Interpretation (K : Type u) where
  functions : (n : Fin (bound+1)) → FunctionSymbols n.val → (Fin n.val → K) → K
  relations : (n : Fin (bound+1)) → RelationSymbols n.val → (Fin n.val → K) → Prop

variable {K : Type u}

def zeroValue (M : Interpretation K) : K := M.functions ⟨0,by decide⟩ zeroSymbol Fin.elim0
def oneValue (M : Interpretation K) : K := M.functions ⟨0,by decide⟩ oneSymbol Fin.elim0
def constantValue (M : Interpretation K) (n : ℕ) : K :=
  M.functions ⟨0,by decide⟩ (constantSymbol n) Fin.elim0
def negValue (M : Interpretation K) (x : K) : K := M.functions ⟨1,by decide⟩ negSymbol ![x]
def addValue (M : Interpretation K) (x y : K) : K := M.functions ⟨2,by decide⟩ addSymbol ![x,y]
def mulValue (M : Interpretation K) (x y : K) : K := M.functions ⟨2,by decide⟩ mulSymbol ![x,y]
def ltValue (M : Interpretation K) (x y : K) : Prop := M.relations ⟨2,by decide⟩ ltSymbol ![x,y]
def value (M : Interpretation K) (t : Term) (ρ : ℕ → K) : K := t.evaluate M.functions ρ
def Holds (M : Interpretation K) (φ : Formula) (ρ : ℕ → K) : Prop := φ.Holds M.functions M.relations ρ

/-- A total nullary interpretation supplies the standard nonempty domain. -/
theorem interpretation_nonempty (M : Interpretation K) : Nonempty K := ⟨zeroValue M⟩

def MatricesValid (M : Interpretation K) : Prop := ∀ φ∈finiteMatrices,∀ ρ : ℕ → K,Holds M φ ρ

@[simp] theorem value_var (M : Interpretation K) (i : ℕ) (ρ : ℕ → K) : value M (var i) ρ=ρ i := rfl
@[simp] theorem value_zero (M : Interpretation K) (ρ : ℕ → K) : value M zero ρ=zeroValue M := by
  apply congrArg (M.functions ⟨0,by decide⟩ zeroSymbol)
  funext i
  exact Fin.elim0 i
@[simp] theorem value_one (M : Interpretation K) (ρ : ℕ → K) : value M one ρ=oneValue M := by
  apply congrArg (M.functions ⟨0,by decide⟩ oneSymbol)
  funext i
  exact Fin.elim0 i
@[simp] theorem value_c (M : Interpretation K) (n : ℕ) (ρ : ℕ → K) : value M (c n) ρ=constantValue M n := by
  apply congrArg (M.functions ⟨0,by decide⟩ (constantSymbol n))
  funext i
  exact Fin.elim0 i
@[simp] theorem value_neg (M : Interpretation K) (t : Term) (ρ : ℕ → K) :
    value M (neg t) ρ=negValue M (value M t ρ) := by
  apply congrArg (M.functions ⟨1,by decide⟩ negSymbol)
  funext i
  fin_cases i
  rfl
@[simp] theorem value_add (M : Interpretation K) (s t : Term) (ρ : ℕ → K) :
    value M (add s t) ρ=addValue M (value M s ρ) (value M t ρ) := by
  apply congrArg (M.functions ⟨2,by decide⟩ addSymbol)
  funext i
  fin_cases i <;> rfl
@[simp] theorem value_mul (M : Interpretation K) (s t : Term) (ρ : ℕ → K) :
    value M (mul s t) ρ=mulValue M (value M s ρ) (value M t ρ) := by
  apply congrArg (M.functions ⟨2,by decide⟩ mulSymbol)
  funext i
  fin_cases i <;> rfl
@[simp] theorem holds_equal (M : Interpretation K) (s t : Term) (ρ : ℕ → K) :
    Holds M (.equal s t) ρ ↔ value M s ρ=value M t ρ := Iff.rfl
@[simp] theorem holds_lt (M : Interpretation K) (s t : Term) (ρ : ℕ → K) :
    Holds M (lt s t) ρ ↔ ltValue M (value M s ρ) (value M t ρ) := by
  apply Iff.of_eq
  apply congrArg (M.relations ⟨2,by decide⟩ ltSymbol)
  funext i
  fin_cases i <;> rfl
@[simp] theorem holds_neg (M : Interpretation K) (φ : Formula) (ρ : ℕ → K) :
    Holds M (negation φ) ρ ↔ ¬Holds M φ ρ := Iff.rfl
@[simp] theorem holds_imp (M : Interpretation K) (φ ψ : Formula) (ρ : ℕ → K) :
    Holds M (imp φ ψ) ρ ↔ (Holds M φ ρ → Holds M ψ ρ) := Iff.rfl
@[simp] theorem holds_all (M : Interpretation K) (i : ℕ) (φ : Formula) (ρ : ℕ → K) :
    Holds M (all i φ) ρ ↔ ∀ x,Holds M φ (Function.update ρ i x) := Iff.rfl
@[simp] theorem holds_and (M : Interpretation K) (φ ψ : Formula) (ρ : ℕ → K) :
    Holds M (conjunction φ ψ) ρ ↔ Holds M φ ρ ∧ Holds M ψ ρ := by
  simp only [conjunction,holds_neg,holds_imp]
  tauto
@[simp] theorem holds_or (M : Interpretation K) (φ ψ : Formula) (ρ : ℕ → K) :
    Holds M (disjunction φ ψ) ρ ↔ Holds M φ ρ ∨ Holds M ψ ρ := by
  simp only [disjunction,holds_neg,holds_imp]
  tauto
@[simp] theorem holds_exists (M : Interpretation K) (i : ℕ) (φ : Formula) (ρ : ℕ → K) :
    Holds M (existential i φ) ρ ↔ ∃ x,Holds M φ (Function.update ρ i x) := by
  classical
  simp [existential]

theorem close_elim (M : Interpretation K) (names : List ℕ) (φ : Formula) (ρ : ℕ → K)
    (h : Holds M (close names φ) ρ) : Holds M φ ρ := by
  induction names generalizing ρ with
  | nil => exact h
  | cons name names ih =>
      change ∀ x,Holds M (close names φ) (Function.update ρ name x) at h
      simpa only [Function.update_eq_self] using ih _ (h (ρ name))

private def assignment (x y z : K) (i : ℕ) : K := if i=0 then x else if i=1 then y else z

/-- These are consequences of the printed matrices, not additional
hypotheses on the final model comparison. -/
structure MatrixConsequences (M : Interpretation K) : Prop where
  add_assoc : ∀ x y z,addValue M (addValue M x y) z=addValue M x (addValue M y z)
  add_comm : ∀ x y,addValue M x y=addValue M y x
  add_zero : ∀ x,addValue M x (zeroValue M)=x
  add_neg : ∀ x,addValue M x (negValue M x)=zeroValue M
  mul_assoc : ∀ x y z,mulValue M (mulValue M x y) z=mulValue M x (mulValue M y z)
  mul_comm : ∀ x y,mulValue M x y=mulValue M y x
  mul_one : ∀ x,mulValue M x (oneValue M)=x
  distrib : ∀ x y z,mulValue M x (addValue M y z)=addValue M (mulValue M x y) (mulValue M x z)
  zero_ne_one : zeroValue M≠oneValue M
  inverse_exists : ∀ x,x≠zeroValue M → ∃ y,mulValue M x y=oneValue M
  irrefl : ∀ x,¬ltValue M x x
  trans : ∀ x y z,ltValue M x y ∧ ltValue M y z → ltValue M x z
  trichotomy : ∀ x y,ltValue M x y ∨ x=y ∨ ltValue M y x
  add_lt_right : ∀ x y z,ltValue M x y → ltValue M (addValue M x z) (addValue M y z)
  mul_pos : ∀ x y,ltValue M (zeroValue M) x ∧ ltValue M (zeroValue M) y →
    ltValue M (zeroValue M) (mulValue M x y)
  zero_lt_one : ltValue M (zeroValue M) (oneValue M)

/-- All sixteen fields are extracted from their actual literal matrix. -/
theorem matrix_consequences (M : Interpretation K) (hM : MatricesValid M) : MatrixConsequences M where
  add_assoc := by
    intro x y z
    have h : Holds M (.equal (add (add (var 0) (var 1)) (var 2)) (add (var 0) (add (var 1) (var 2)))) (assignment (x) (y) (z)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  add_comm := by
    intro x y
    have h : Holds M (.equal (add (var 0) (var 1)) (add (var 1) (var 0))) (assignment (x) (y) (y)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  add_zero := by
    intro x
    have h : Holds M (.equal (add (var 0) zero) (var 0)) (assignment (x) (x) (x)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  add_neg := by
    intro x
    have h : Holds M (.equal (add (var 0) (neg (var 0))) zero) (assignment (x) (x) (x)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  mul_assoc := by
    intro x y z
    have h : Holds M (.equal (mul (mul (var 0) (var 1)) (var 2)) (mul (var 0) (mul (var 1) (var 2)))) (assignment (x) (y) (z)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  mul_comm := by
    intro x y
    have h : Holds M (.equal (mul (var 0) (var 1)) (mul (var 1) (var 0))) (assignment (x) (y) (y)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  mul_one := by
    intro x
    have h : Holds M (.equal (mul (var 0) one) (var 0)) (assignment (x) (x) (x)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  distrib := by
    intro x y z
    have h : Holds M (.equal (mul (var 0) (add (var 1) (var 2))) (add (mul (var 0) (var 1)) (mul (var 0) (var 2)))) (assignment (x) (y) (z)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  zero_ne_one := by
    have h : Holds M (negation (.equal zero one)) (assignment (zeroValue M) (zeroValue M) (zeroValue M)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  inverse_exists := by
    intro x
    have h : Holds M (imp (negation (.equal (var 0) zero)) (existential 1 (.equal (mul (var 0) (var 1)) one))) (assignment (x) (x) (x)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  irrefl := by
    intro x
    have h : Holds M (negation (lt (var 0) (var 0))) (assignment (x) (x) (x)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  trans := by
    intro x y z
    have h : Holds M (imp (conjunction (lt (var 0) (var 1)) (lt (var 1) (var 2))) (lt (var 0) (var 2))) (assignment (x) (y) (z)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  trichotomy := by
    intro x y
    have h : Holds M (disjunction (lt (var 0) (var 1)) (disjunction (.equal (var 0) (var 1)) (lt (var 1) (var 0)))) (assignment (x) (y) (y)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  add_lt_right := by
    intro x y z
    have h : Holds M (imp (lt (var 0) (var 1)) (lt (add (var 0) (var 2)) (add (var 1) (var 2)))) (assignment (x) (y) (z)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  mul_pos := by
    intro x y
    have h : Holds M (imp (conjunction (lt zero (var 0)) (lt zero (var 1))) (lt zero (mul (var 0) (var 1)))) (assignment (x) (y) (y)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h
  zero_lt_one := by
    have h : Holds M (lt zero one) (assignment (zeroValue M) (zeroValue M) (zeroValue M)) :=
      hM _ (by simp [finiteMatrices]) _
    simpa [assignment] using h

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
