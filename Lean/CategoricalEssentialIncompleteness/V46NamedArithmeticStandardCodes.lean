import CategoricalEssentialIncompleteness.V46NamedArithmeticSignature
import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables

/-! Positive Sigma-one graph instances commute with standard numeral
parameters in every PA model. This is a comparison of arithmetic code
values; it does not identify old bound-variable syntax with named syntax. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticStandardCodes
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem sigmaOne_natCast {k : ℕ} (φ : 𝚺₁.Semisentence k) (v : Fin k → ℕ)
    (h : φ.val.Evalb v) : φ.val.Evalb (M := M) (Nat.cast ∘ v) := by
  simpa [numeral_eq_natCast] using bold_sigma_one_completeness' (M := M) (by simp) h

private theorem castVector_one (n : ℕ) :
    (Nat.cast ∘ (![n] : Fin 1 → ℕ) : Fin 1 → M) = ![(n : M)] := by
  funext i
  fin_cases i
  rfl

private theorem castVector_two (a b : ℕ) :
    (Nat.cast ∘ (![a,b] : Fin 2 → ℕ) : Fin 2 → M) = ![(a : M),(b : M)] := by
  funext i
  fin_cases i <;> rfl

private theorem castVector_three (a b c : ℕ) :
    (Nat.cast ∘ (![a,b,c] : Fin 3 → ℕ) : Fin 3 → M) = ![(a : M),(b : M),(c : M)] := by
  funext i
  fin_cases i <;> rfl

theorem carrier_natCast (C : Carrier) (n : ℕ) (hn : C.val.Evalb ![n]) :
    C.val.Evalb (M := M) ![(n : M)] := by
  have h := sigmaOne_natCast (M := M) C ![n] hn
  rw [castVector_one] at h
  exact h

theorem pair_natCast (a b : ℕ) : ((Arithmetic.pair a b : ℕ) : M) = Arithmetic.pair (a : M) (b : M) := by
  have hN : pairDef.val.Evalb (M := ℕ) ![Arithmetic.pair a b,a,b] := by simp
  have hM : pairDef.val.Evalb (M := M) (Nat.cast ∘ ![Arithmetic.pair a b,a,b]) :=
    sigmaOne_natCast (M := M) (pairDef.ofZero 𝚺₁) ![Arithmetic.pair a b,a,b] hN
  rw [castVector_three] at hM
  simpa using hM

theorem adjoin_natCast (a b : ℕ) : ((adjoin a b : ℕ) : M) = adjoin (a : M) (b : M) := by
  have hN : adjoinDef.val.Evalb (M := ℕ) ![adjoin a b,a,b] := by simp
  have hM : adjoinDef.val.Evalb (M := M) (Nat.cast ∘ ![adjoin a b,a,b]) :=
    sigmaOne_natCast (M := M) (adjoinDef.ofZero 𝚺₁) ![adjoin a b,a,b] hN
  rw [castVector_three] at hM
  simpa using hM

theorem constructor_natCast (formula : Bool) (q : RawPolynomial) (u : ℕ) :
    ((constructor formula q u : ℕ) : M) = constructor formula q (u : M) := by
  have hN := (constructorGraph_eval formula q (constructor formula q u : ℕ) u).mpr rfl
  have hM := sigmaOne_natCast (M := M) (constructorGraph formula q) ![constructor formula q u,u] hN
  rw [castVector_two] at hM
  exact (constructorGraph_eval formula q _ _).mp hM

theorem freeVariables_natCast (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (word : ℕ) :
    ((ConcreteNamedSubstitution.freeVariables V σ π d word : ℕ) : M) =
      ConcreteNamedSubstitution.freeVariables V σ π d (word : M) := by
  have hN := (ConcreteNamedSubstitution.freeVariablesGraph_eval V σ π d
    (ConcreteNamedSubstitution.freeVariables V σ π d word : ℕ) word).mpr rfl
  have hM := sigmaOne_natCast (M := M) (ConcreteNamedSubstitution.freeVariablesGraph V σ π d)
    ![ConcreteNamedSubstitution.freeVariables V σ π d word,word] hN
  rw [castVector_two] at hM
  exact (ConcreteNamedSubstitution.freeVariablesGraph_eval V σ π d _ _).mp hM

theorem member_pack_natCast (name : M) (l : List ℕ) :
    ConcreteNamedSubstitution.member name ((SyntacticSyntax.NatVectors.pack l : ℕ) : M) = 1 ↔
      ∃ y ∈ l,(y : M) = name := by
  classical
  induction l with
  | nil => simp [SyntacticSyntax.NatVectors.pack_nil]
  | cons y ys ih =>
    rw [NamedPostfixEncoding.pack_adjoin,adjoin_natCast,ConcreteNamedSubstitution.member_adjoin]
    by_cases hy : (y : M) = name
    · simp [hy]
    · simp [hy,ih]

end CategoricalEssentialIncompleteness.V46.NamedArithmeticStandardCodes
