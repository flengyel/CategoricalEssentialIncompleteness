/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofValidity

/-! # Recursive relabeling of finite proofs -/

@[expose] public section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

theorem Formula.mapAtoms_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable (Formula.mapAtoms f) := by
  have h := Formula.decode_computable.comp ((Formula.sigma_computable hf).comp Formula.encode_computable)
  exact h.of_eq (fun p => by rw [sigma_encode,Formula.decode_encode])

namespace ProofTree

theorem positive_computable : Computable positive := by
  have h := decode_computable.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 6) .id) (.const 3))
  exact h.of_eq (fun x => decode_encode (.positive x))

theorem negative_computable : Computable negative := by
  have h := decode_computable.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 6) .id) (.const 4))
  exact h.of_eq (fun x => decode_encode (.negative x))

private theorem pair_formula_codes_computable : Computable (fun p : Formula × Formula =>
    Nat.pair p.1.encode p.2.encode) :=
  Primrec₂.natPair.to_comp.comp (Formula.encode_computable.comp Computable.fst)
    (Formula.encode_computable.comp Computable.snd)

theorem logical1_computable : Computable (fun p : Formula × Formula => logical1 p.1 p.2) := by
  have h := decode_computable.comp
    (Primrec.nat_mul.to_comp.comp (.const 6) pair_formula_codes_computable)
  exact h.of_eq (fun p => decode_encode (.logical1 p.1 p.2))

theorem logical2_computable : Computable (fun p : Formula × Formula × Formula =>
    logical2 p.1 p.2.1 p.2.2) := by
  have hp : Computable (fun p : Formula × Formula × Formula =>
      Nat.pair p.1.encode (Nat.pair p.2.1.encode p.2.2.encode)) :=
    Primrec₂.natPair.to_comp.comp (Formula.encode_computable.comp Computable.fst)
      (pair_formula_codes_computable.comp Computable.snd)
  have h := decode_computable.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (.const 6) hp) (.const 1))
  exact h.of_eq (fun p => decode_encode (.logical2 p.1 p.2.1 p.2.2))

theorem logical3_computable : Computable (fun p : Formula × Formula => logical3 p.1 p.2) := by
  have h := decode_computable.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (.const 6) pair_formula_codes_computable) (.const 2))
  exact h.of_eq (fun p => decode_encode (.logical3 p.1 p.2))

theorem mp_computable : Computable (fun p : ProofTree × ProofTree => mp p.1 p.2) := by
  have hp : Computable (fun p : ProofTree × ProofTree => Nat.pair p.1.encode p.2.encode) :=
    Primrec₂.natPair.to_comp.comp (encode_computable.comp Computable.fst)
      (encode_computable.comp Computable.snd)
  have h := decode_computable.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (.const 6) hp) (.const 5))
  exact h.of_eq (fun p => decode_encode (.mp p.1 p.2))

theorem mapAtoms_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (mapAtoms f) := by
  have hs := Formula.mapAtoms_computable hf
  have hpair : Computable (fun p : Formula × Formula =>
      (Formula.mapAtoms f p.1,Formula.mapAtoms f p.2)) :=
    Computable.pair (hs.comp Computable.fst) (hs.comp Computable.snd)
  have htriple : Computable (fun p : Formula × Formula × Formula =>
      (Formula.mapAtoms f p.1,Formula.mapAtoms f p.2.1,Formula.mapAtoms f p.2.2)) :=
    Computable.pair (hs.comp Computable.fst) (hpair.comp Computable.snd)
  have h1 : Computable (fun p : Formula × Formula =>
      ProofTree.logical1 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2)) :=
    Computable.comp (f := fun p : Formula × Formula => ProofTree.logical1 p.1 p.2)
      (g := fun p : Formula × Formula => (Formula.mapAtoms f p.1,Formula.mapAtoms f p.2))
      logical1_computable hpair
  have h2 : Computable (fun p : Formula × Formula × Formula =>
      ProofTree.logical2 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2.1)
        (Formula.mapAtoms f p.2.2)) :=
    Computable.comp (f := fun p : Formula × Formula × Formula => ProofTree.logical2 p.1 p.2.1 p.2.2)
      (g := fun p : Formula × Formula × Formula =>
        (Formula.mapAtoms f p.1,Formula.mapAtoms f p.2.1,Formula.mapAtoms f p.2.2))
      logical2_computable htriple
  have h3 : Computable (fun p : Formula × Formula =>
      ProofTree.logical3 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2)) :=
    Computable.comp (f := fun p : Formula × Formula => ProofTree.logical3 p.1 p.2)
      (g := fun p : Formula × Formula => (Formula.mapAtoms f p.1,Formula.mapAtoms f p.2))
      logical3_computable hpair
  let g : ProofTree → ProofTree := fold
    (fun p => .logical1 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2))
    (fun p => .logical2 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2.1) (Formula.mapAtoms f p.2.2))
    (fun p => .logical3 (Formula.mapAtoms f p.1) (Formula.mapAtoms f p.2))
    (fun x => .positive (f x)) (fun x => .negative (f x)) (fun p => .mp p.1 p.2)
  letI : Inhabited ProofTree := ⟨.positive 0⟩
  have hg : Computable g := by
    unfold g
    apply fold_computable
    · exact h1
    · exact h2
    · exact h3
    · exact Computable.comp (f := ProofTree.positive) (g := f) positive_computable hf
    · exact Computable.comp (f := ProofTree.negative) (g := f) negative_computable hf
    · exact mp_computable
  apply hg.of_eq
  intro t
  induction t with
  | logical1 | logical2 | logical3 | positive | negative => rfl
  | mp t u iht ihu => exact congrArg₂ ProofTree.mp iht ihu

end ProofTree
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
