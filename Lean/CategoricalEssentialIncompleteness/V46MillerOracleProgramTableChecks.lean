/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable


/-! # Compiling an ordinary coherent table search into one oracle program -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.OracleProgram
open CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

example : Computable ofTableCode := ofTableCode_computable
example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (hM : MonotoneValues F)
    (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTable F hF) p n ↔ ∃ k,
      y ∈ F ((bitPrefix p k).map Fin.val,n) := ofTable_graph F hF hM p n y
example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (hM : MonotoneValues F)
    (p : Bits) (n : ℕ) :
    (eval (ofTable F hF) p n).Dom ↔ ∃ k,
      (F ((bitPrefix p k).map Fin.val,n)).Dom := ofTable_domain F hF hM p n
example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (hM : MonotoneValues F) :
    ∃ e : Nat.Partrec.Code, ∀ p : Bits, ∀ n y : ℕ,
      y ∈ eval e p n ↔ ∃ k, y ∈ F ((bitPrefix p k).map Fin.val,n) :=
  ⟨ofTable F hF,ofTable_graph F hF hM⟩

example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (hM : MonotoneValues F) :
    ∃ d : ℕ, ∀ p : Bits, ∀ n y : ℕ,
      y ∈ numberedEval d p n ↔ ∃ k, y ∈ F ((bitPrefix p k).map Fin.val,n) :=
  exists_uniform_index F hF hM

example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (p : Bits) (n y : ℕ) :
    y ∈ eval (ofTable F hF) p n → ∃ k, y ∈ F ((bitPrefix p k).map Fin.val,n) :=
  ofTable_sound F hF p n y
example (F : List ℕ × ℕ → Part ℕ) (hF : Partrec F) (p : Bits) (n : ℕ)
    (hcoh : ∀ i j a b, a ∈ F ((bitPrefix p i).map Fin.val,n) →
      b ∈ F ((bitPrefix p j).map Fin.val,n) → a=b) (y : ℕ) :
    y ∈ eval (ofTable F hF) p n ↔ ∃ k, y ∈ F ((bitPrefix p k).map Fin.val,n) :=
  ofTable_graph_at F hF p n hcoh y
