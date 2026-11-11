/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeSigmaOneWitness

/-!
# Literal internal instances of the extraction seed

All substitutions here are operations on internal syntax, not semantic
equivalences. The matrix valuation is `(y',y,u)`. Its conclusion is the
existing `eqValue y y'`, with the original equality syntax unchanged.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeSubstitution

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem quote_all {n : ℕ} (phi : ArithmeticSemisentence (n + 1)) :
    (⌜∀¹ phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      ∀¹ (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ (n + 1)) := by
  simp [Sentence.typed_quote_def]

private theorem quote_rew {n m : ℕ} (phi : ArithmeticSemisentence n)
    (w : Fin n → ArithmeticSemiterm Empty m) :
    (⌜(Rew.subst w) ▹ phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ m) =
      (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n).subst (fun i => ⌜w i⌝) := by
  simp [Sentence.typed_quote_def, Rewriting.emb_subst_eq_subst_emb,
    Semiterm.empty_typed_quote_def]

/-- The single numerical template parameter used by the executable core. -/
noncomputable def extractionBodyCode (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ℕ :=
  Encodable.encode (extractionBodyU M h k)

noncomputable def matrixAfterU (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  (⌜extractionMatrix M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1, typedNumeral u]

noncomputable def matrixAfterY (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (⌜extractionMatrix M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
    ![Bootstrapping.Semiterm.bvar 0, typedNumeral y, typedNumeral u]

private theorem numeral_encode_quote {n : ℕ} (phi : ArithmeticSemisentence n) :
    (ORingStructure.numeral (Encodable.encode phi) : V) = (⌜phi⌝ : V) := by
  rw [numeral_eq_natCast_app, Sentence.quote_eq_encode]

private theorem quote_all_value {n : ℕ} (phi : ArithmeticSemisentence (n + 1)) :
    (⌜∀¹ phi⌝ : V) = ^∀ (⌜phi⌝ : V) := by
  simpa only [← Sentence.quote_eq, Bootstrapping.Semiformula.val_all] using
    congrArg Bootstrapping.Semiformula.val (quote_all (V := V) phi)

theorem seedBody_quote (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (ORingStructure.numeral (extractionBodyCode M h k) : V) =
      (⌜extractionBodyU M h k⌝ : V) :=
  numeral_encode_quote (extractionBodyU M h k)

theorem seed_quote (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (⌜extractionSeed M h k⌝ : V) = ^∀ (⌜extractionBodyU M h k⌝ : V) :=
  quote_all_value (extractionBodyU M h k)

theorem subst1Value_typedNumeral (phi : Bootstrapping.Semiformula V ℒₒᵣ 1) (u : V) :
    subst1Value (Arithmetic.numeral u) phi.val =
      (phi.subst (toNumVec (k := 0) ![u])).val := by
  rw [subst1Value_eq_substs1 (by simp) phi.isSemiformula_one]
  rfl

private theorem forall3_first (phi : ArithmeticSemisentence 3) (u : V) :
    subst1Value (Arithmetic.numeral u) (⌜∀¹ ∀¹ phi⌝ : V) =
      ^∀ (^∀ ((⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
        ![Bootstrapping.Semiterm.bvar (0 : Fin 2), Bootstrapping.Semiterm.bvar 1,
          typedNumeral u]).val) := by
  rw [show (⌜∀¹ ∀¹ phi⌝ : V) =
    (⌜∀¹ ∀¹ phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [quote_all, Bootstrapping.Semiformula.substs_all,
    Bootstrapping.Semiformula.val_all]
  congr 3
  apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 3 2 =>
    (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst w)
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

theorem first_specialization (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u : V) :
    subst1Value (Arithmetic.numeral u) (⌜extractionBodyU M h k⌝ : V) =
      ^∀ (^∀ (matrixAfterU M h k u).val) := by
  exact forall3_first (extractionMatrix M h k) u

private theorem partial3_second (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (u y : V) :
    subst1Value (Arithmetic.numeral y)
      (^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 2), Bootstrapping.Semiterm.bvar 1,
        typedNumeral u]).val) =
      ^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1),
        typedNumeral y, typedNumeral u]).val := by
  let a : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
    phi.subst ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1, typedNumeral u]
  rw [show (^∀ a.val : V) = (∀¹ a : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 1
  dsimp only [a]
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

theorem second_specialization (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y : V) :
    subst1Value (Arithmetic.numeral y) (^∀ (matrixAfterU M h k u).val) =
      ^∀ (matrixAfterY M h k u y).val :=
  partial3_second (⌜extractionMatrix M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3) u y

private theorem partial3_third (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (u y r : V) :
    subst1Value (Arithmetic.numeral r)
      (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral y, typedNumeral u]).val =
      (phi.subst (toNumVec (k := 0) ![r, y, u])).val := by
  rw [subst1Value_typedNumeral, Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

-- Apply the typed-to-untyped substitution equation before instantiating
-- the arithmetic formula, to avoid expanding its entire quotation.
private theorem partial3_third_value (phi : ArithmeticSemisentence 3) (u y r : V) :
    subst1Value (Arithmetic.numeral r)
      ((⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
        ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral y, typedNumeral u]).val =
      instanceValue phi ![r, y, u] :=
  (partial3_third (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3) u y r).trans
    (toNumVec_instance phi ![r, y, u])

theorem third_specialization (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y r : V) :
    subst1Value (Arithmetic.numeral r) (matrixAfterY M h k u y).val =
      instanceValue (extractionMatrix M h k) ![r, y, u] := by
  exact partial3_third_value (extractionMatrix M h k) u y r

theorem instanceValue_imp {n : ℕ} (phi psi : ArithmeticSemisentence n) (v : Fin n → V) :
    instanceValue (phi 🡒 psi) v = imp ℒₒᵣ (instanceValue phi v) (instanceValue psi v) := by
  have hquote : (⌜phi 🡒 psi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) 🡒 ⌜psi⌝ := by
    simp [Sentence.typed_quote_def]
  rw [← toNumVec_instance, hquote, Bootstrapping.Semiformula.substs_imp]
  rfl

theorem instanceValue_rew {n m : ℕ} (phi : ArithmeticSemisentence n)
    (w : Fin n → ArithmeticSemiterm Empty m) (v : Fin m → V) :
    instanceValue ((Rew.subst w) ▹ phi) v =
      ((⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n).subst
        (fun i => (⌜w i⌝ : Bootstrapping.Semiterm V ℒₒᵣ m).subst
          (toNumVec (k := 0) v))).val := by
  rw [← toNumVec_instance, quote_rew, Bootstrapping.Semiformula.substs_substs]
  rfl

private theorem matrixFor_instance (F : ArithmeticSentence) (M : ArithmeticSemisentence 1)
    (H K E : ArithmeticSemisentence 2) (u y r : V) :
    instanceValue (extractionMatrixFor F M H K E) ![r, y, u] =
      imp ℒₒᵣ (⌜F⌝ : V) (imp ℒₒᵣ (instanceValue M ![u])
        (imp ℒₒᵣ (instanceValue H ![u, y])
          (imp ℒₒᵣ (instanceValue K ![u, r]) (instanceValue E ![y, r])))) := by
  simp only [extractionMatrixFor, instanceValue_imp, instanceValue_rew]
  simp [instanceValue, substNumerals, toNumVec,
    Bootstrapping.Semiformula.subst_nil_eq_self, SemitermVec.val,
    Matrix.vecHead, Matrix.vecTail]
  rfl

/-- Literal identity with the four MP premises and the existing equality code. -/
theorem matrix_instance (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y r : V) :
    instanceValue (extractionMatrix M h k) ![r, y, u] =
      imp ℒₒᵣ (⌜familyEq M h k⌝ : V)
        (imp ℒₒᵣ (instanceValue M.val ![u])
          (imp ℒₒᵣ (instanceValue (outputGraph h).val ![u, y])
            (imp ℒₒᵣ (instanceValue (outputGraph k).val ![u, r]) (eqValue y r)))) :=
  matrixFor_instance (familyEq M h k) M.val (outputGraph h).val (outputGraph k).val
    equalityFormula u y r

end FailureOfComposition.NativeFamilyExtraction
