/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeMembershipFormulas

/-!
# Literal instances of the assembly schemas

Pointwise specialization runs in the order `e,u,d`, and closure specialization
in the order `e,d`. These identities use the actual internal numeral and
substitution operations, including nonstandard numerals. They identify syntax
codes, not just semantically equivalent formulas.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeSubstitution

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem quote_all {n : ℕ} (phi : ArithmeticSemisentence (n + 1)) :
    (⌜∀¹ phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      ∀¹ (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ (n + 1)) := by
  simp [Sentence.typed_quote_def]

private theorem numeral_encode_quote {n : ℕ} (phi : ArithmeticSemisentence n) :
    (ORingStructure.numeral (Encodable.encode phi) : V) = (⌜phi⌝ : V) := by
  rw [numeral_eq_natCast_app, Sentence.quote_eq_encode]

private theorem quote_all_value {n : ℕ} (phi : ArithmeticSemisentence (n + 1)) :
    (⌜∀¹ phi⌝ : V) = ^∀ (⌜phi⌝ : V) := by
  simpa only [← Sentence.quote_eq, Bootstrapping.Semiformula.val_all] using
    congrArg Bootstrapping.Semiformula.val (quote_all (V := V) phi)

noncomputable def pointwiseBodyCode (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ℕ := Encodable.encode (pointwiseBodyE S M h k)

noncomputable def closureBodyCode (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ℕ := Encodable.encode (closureBodyE S M h k)

noncomputable def pointwiseAfterE (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
  (⌜pointwiseMatrix S M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1, typedNumeral e]

noncomputable def pointwiseAfterU (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (⌜pointwiseMatrix S M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
    ![Bootstrapping.Semiterm.bvar 0, typedNumeral u, typedNumeral e]

noncomputable def closureAfterE (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (⌜closureMatrix S M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Bootstrapping.Semiterm.bvar 0, typedNumeral e]

theorem pointwiseBody_quote (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (ORingStructure.numeral (pointwiseBodyCode S M h k) : V) =
      (⌜pointwiseBodyE S M h k⌝ : V) := numeral_encode_quote _

theorem closureBody_quote (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (ORingStructure.numeral (closureBodyCode S M h k) : V) =
      (⌜closureBodyE S M h k⌝ : V) := numeral_encode_quote _

theorem pointwiseSchema_quote (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (⌜pointwiseSchema S M h k⌝ : V) = ^∀ (⌜pointwiseBodyE S M h k⌝ : V) :=
  quote_all_value _

theorem closureSchema_quote (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    (⌜closureSchema S M h k⌝ : V) = ^∀ (⌜closureBodyE S M h k⌝ : V) :=
  quote_all_value _

private theorem forall3_first (phi : ArithmeticSemisentence 3) (e : V) :
    subst1Value (Arithmetic.numeral e) (⌜∀¹ ∀¹ phi⌝ : V) =
      ^∀ (^∀ ((⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst
        ![Bootstrapping.Semiterm.bvar (0 : Fin 2), Bootstrapping.Semiterm.bvar 1,
          typedNumeral e]).val) := by
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

private theorem partial3_second (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (e u : V) :
    subst1Value (Arithmetic.numeral u)
      (^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 2), Bootstrapping.Semiterm.bvar 1,
        typedNumeral e]).val) =
      ^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1),
        typedNumeral u, typedNumeral e]).val := by
  let a : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
    phi.subst ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1, typedNumeral e]
  rw [show (^∀ a.val : V) = (∀¹ a : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 1
  dsimp only [a]
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

private theorem partial3_third (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (e u d : V) :
    subst1Value (Arithmetic.numeral d)
      (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral u, typedNumeral e]).val =
      (phi.subst (toNumVec (k := 0) ![d, u, e])).val := by
  rw [subst1Value_typedNumeral, Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

private theorem forall2_first (phi : ArithmeticSemisentence 2) (e : V) :
    subst1Value (Arithmetic.numeral e) (⌜∀¹ phi⌝ : V) =
      ^∀ ((⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral e]).val := by
  rw [show (⌜∀¹ phi⌝ : V) =
    (⌜∀¹ phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [quote_all, Bootstrapping.Semiformula.substs_all,
    Bootstrapping.Semiformula.val_all]
  congr 2
  apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 2 1 =>
    (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst w)
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

private theorem partial2_second (phi : Bootstrapping.Semiformula V ℒₒᵣ 2) (e d : V) :
    subst1Value (Arithmetic.numeral d)
      (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral e]).val =
      (phi.subst (toNumVec (k := 0) ![d, e])).val := by
  rw [subst1Value_typedNumeral, Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

theorem pointwise_first (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) :
    subst1Value (Arithmetic.numeral e) (⌜pointwiseBodyE S M h k⌝ : V) =
      ^∀ (^∀ (pointwiseAfterE S M h k e).val) := forall3_first _ e

theorem pointwise_second (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u : V) :
    subst1Value (Arithmetic.numeral u) (^∀ (pointwiseAfterE S M h k e).val) =
      ^∀ (pointwiseAfterU S M h k e u).val := partial3_second _ e u

theorem pointwise_third (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u d : V) :
    subst1Value (Arithmetic.numeral d) (pointwiseAfterU S M h k e u).val =
      instanceValue (pointwiseMatrix S M h k) ![d, u, e] := partial3_third _ e u d

theorem closure_first (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) :
    subst1Value (Arithmetic.numeral e) (⌜closureBodyE S M h k⌝ : V) =
      ^∀ (closureAfterE S M h k e).val := forall2_first _ e

theorem closure_second (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e d : V) :
    subst1Value (Arithmetic.numeral d) (closureAfterE S M h k e).val =
      instanceValue (closureMatrix S M h k) ![d, e] := partial2_second _ e d

private theorem pointwiseFor_instance (A : ArithmeticSemisentence 1) (T : ArithmeticSentence)
    (M : ArithmeticSemisentence 1) (B D : ArithmeticSemisentence 2) (e u d : V) :
    instanceValue (pointwiseMatrixFor A T M B D) ![d, u, e] =
      imp ℒₒᵣ (instanceValue A ![e]) (imp ℒₒᵣ (⌜T⌝ : V)
        (imp ℒₒᵣ (instanceValue M ![u])
          (imp ℒₒᵣ (instanceValue B ![u, d]) (instanceValue D ![u, d])))) := by
  simp only [pointwiseMatrixFor, instanceValue_imp, instanceValue_rew]
  simp [instanceValue, substNumerals, toNumVec,
    Bootstrapping.Semiformula.subst_nil_eq_self, SemitermVec.val,
    Matrix.vecHead, Matrix.vecTail]
  rfl

private theorem closureFor_instance (A : ArithmeticSemisentence 1) (T : ArithmeticSentence)
    (C : ArithmeticSemisentence 1) (e d : V) :
    instanceValue (closureMatrixFor A T C) ![d, e] =
      imp ℒₒᵣ (instanceValue A ![e]) (imp ℒₒᵣ (⌜T⌝ : V) (instanceValue C ![d])) := by
  simp only [closureMatrixFor, instanceValue_imp, instanceValue_rew]
  simp [instanceValue, substNumerals, toNumVec,
    Bootstrapping.Semiformula.subst_nil_eq_self, SemitermVec.val,
    Matrix.vecHead, Matrix.vecTail]
  rfl

theorem pointwise_matrix_instance (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u d : V) :
    instanceValue (pointwiseMatrix S M h k) ![d, u, e] =
      imp ℒₒᵣ (instanceValue (familyAcceptance S M h k).val ![e])
        (imp ℒₒᵣ (⌜totality M k⌝ : V) (imp ℒₒᵣ (instanceValue M.val ![u])
          (imp ℒₒᵣ (instanceValue (membershipFormula S h).val ![u, d])
            (instanceValue (membershipFormula S k).val ![u, d])))) :=
  pointwiseFor_instance _ _ _ _ _ e u d

theorem closure_matrix_instance (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e d : V) :
    instanceValue (closureMatrix S M h k) ![d, e] =
      imp ℒₒᵣ (instanceValue (familyAcceptance S M h k).val ![e])
        (imp ℒₒᵣ (⌜totality M k⌝ : V) (instanceValue (transferClosure S M h k) ![d])) :=
  closureFor_instance _ _ _ e d

theorem acceptanceInstance_literal (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) :
    unaryInstanceValue (⌜(familyAcceptance S M h k).val⌝ : V) e =
      instanceValue (familyAcceptance S M h k).val ![e] := unaryInstance_literal _ e

theorem membershipInstance_literal (S : ArithmeticTheory) [S.Δ₁] (h : ℕ) (u d : V) :
    binaryInstanceValue (⌜(membershipFormula S h).val⌝ : V) u d =
      instanceValue (membershipFormula S h).val ![u, d] := binaryInstance_literal _ u d

theorem closureInstance_literal (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (d : V) :
    unaryInstanceValue (⌜transferClosure S M h k⌝ : V) d =
      instanceValue (transferClosure S M h k) ![d] := unaryInstance_literal _ d

theorem acceptance_toNumVec (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) :
    ((Bootstrapping.Semiformula.subst (toNumVec (k := 0) ![e])
      (⌜(familyAcceptance S M h k).val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)).val) =
      instanceValue (familyAcceptance S M h k).val ![e] := toNumVec_instance _ _

theorem membership_toNumVec (S : ArithmeticTheory) [S.Δ₁] (h : ℕ) (u d : V) :
    ((Bootstrapping.Semiformula.subst (toNumVec (k := 0) ![u, d])
      (⌜(membershipFormula S h).val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2)).val) =
      instanceValue (membershipFormula S h).val ![u, d] := toNumVec_instance _ _

theorem closure_toNumVec (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (d : V) :
    ((Bootstrapping.Semiformula.subst (toNumVec (k := 0) ![d])
      (⌜transferClosure S M h k⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)).val) =
      instanceValue (transferClosure S M h k) ![d] := toNumVec_instance _ _

end FailureOfComposition.NativeMembershipAssembly
