/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefill

/-! # A left-to-right primitive-recursion parser for postfix words -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open Coding

/-- Parser state zero is failure. State `stack+1` is a valid parser stack.
Every stack block is a pair of its literal word and its output sort. -/
def stepGraph (a b : RawPolynomial) : 𝚺₁.Semisentence 3 :=
  let A := refillGraph a
  let B := refillGraph b
  let WA := childrenWordGraph a
  let WB := childrenWordGraph b
  .mkSigma “o record state. ∃ s k st l lv ls r rv rs wa wb tw fw tb fb ts fs,
    !pi₁Def.val s record ∧ !pi₂Def.val k record ∧ !subDef.val st state 1 ∧
    !A.val l s st ∧ !fstIdxDef.val lv l ∧ !sndIdxDef.val ls l ∧
    !B.val r s st ∧ !fstIdxDef.val rv r ∧ !sndIdxDef.val rs r ∧
    !WA.val wa lv ∧ !WB.val wb rv ∧
    !concatDef.val tw wa record ∧ !concatDef.val fw wb record ∧
    !pairDef.val tb tw 0 ∧ !pairDef.val fb fw 1 ∧
    !adjoinDef.val ts tb ls ∧ !adjoinDef.val fs fb rs ∧
    (((state = 0 ∨ (k = 0 ∧ l = 0) ∨ (k = 1 ∧ r = 0) ∨ (k ≠ 0 ∧ k ≠ 1)) ∧ o = 0) ∨
      (state ≠ 0 ∧ k = 0 ∧ l ≠ 0 ∧ o = ts + 1) ∨
      (state ≠ 0 ∧ k = 1 ∧ r ≠ 0 ∧ o = fs + 1))”

/-- The numerical loop reads position i at step i, never the reverse
order of an adjoin-recursion traversal. -/
def blueprint (a b : RawPolynomial) : PR.Blueprint 2 where
  zero := .mkSigma “o word initial. o = initial”
  succ := let S := stepGraph a b
    .mkSigma “o prev i word initial. ∃ record, !nthDef.val record word i ∧ !S.val o record prev”

/-- Variables are output state, runPrefix length, word, initial state. -/
def prefixGraph (a b : RawPolynomial) : 𝚺₁.Semisentence 4 := (blueprint a b).resultDef

/-- The same runPrefix graph, in curried function argument order. -/
def prefixValueGraph (a b : RawPolynomial) : 𝚺₁.Semisentence 4 :=
  let R := prefixGraph a b
  .mkSigma “o word n initial. !R.val o n word initial”

def runGraph (a b : RawPolynomial) : 𝚺₁.Semisentence 3 :=
  let R := prefixGraph a b
  .mkSigma “o word initial. ∃ n, !lenDef.val n word ∧ !R.val o n word initial”

/-- Coefficient witnesses are existential data of this predicate, not
components of the syntax word or its constructor records. -/
def carrier (formula : Bool) (a b : RawPolynomial) : Carrier :=
  let R := runGraph a b
  let C := coefficients a b
  match formula with
  | false => .mkSigma “word. !C.val word ∧ ∃ o block stack,
      !R.val o word 1 ∧ !pairDef.val block word 0 ∧
      !adjoinDef.val stack block 0 ∧ o = stack + 1”
  | true => .mkSigma “word. !C.val word ∧ ∃ o block stack,
      !R.val o word 1 ∧ !pairDef.val block word 1 ∧
      !adjoinDef.val stack block 0 ∧ o = stack + 1”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

noncomputable def step (a b : RawPolynomial) (record state : M) : M :=
  let s := π₁ record
  let k := π₂ record
  let st := state - 1
  let l := refill a s st
  let r := refill b s st
  if state = 0 then 0 else
    if k = 0 then
      if l = 0 then 0 else
        adjoin ⟪concat (childrenWord a (fstIdx l)) record, 0⟫ (sndIdx l) + 1
    else if k = 1 then
      if r = 0 then 0 else
        adjoin ⟪concat (childrenWord b (fstIdx r)) record, 1⟫ (sndIdx r) + 1
    else 0

@[simp] private theorem firstDef_eval (o s : M) :
    fstIdxDef.val.Evalb ![o, s] ↔ o = fstIdx s := fstIdx_defined.iff
@[simp] private theorem restDef_eval (o s : M) :
    sndIdxDef.val.Evalb ![o, s] ↔ o = sndIdx s := sndIdx_defined.iff
@[simp] private theorem leftDef_eval (o s : M) :
    pi₁Def.val.Evalb ![o, s] ↔ o = π₁ s := pi₁_defined.iff
@[simp] private theorem rightDef_eval (o s : M) :
    pi₂Def.val.Evalb ![o, s] ↔ o = π₂ s := pi₂_defined.iff
@[simp] private theorem subtractDef_eval (o s t : M) :
    subDef.val.Evalb ![o, s, t] ↔ o = s - t := sub_defined.iff

@[simp] theorem stepGraph_eval (a b : RawPolynomial) (o record state : M) :
    (stepGraph a b).val.Evalb ![o, record, state] ↔ o = step a b record state := by
  have hh : (stepGraph a b).val.Evalb ![o, record, state] ↔
      (((state = 0 ∨ (π₂ record = 0 ∧ refill a (π₁ record) (state - 1) = 0) ∨
          (π₂ record = 1 ∧ refill b (π₁ record) (state - 1) = 0) ∨
          (π₂ record ≠ 0 ∧ π₂ record ≠ 1)) ∧ o = 0) ∨
        (state ≠ 0 ∧ π₂ record = 0 ∧ refill a (π₁ record) (state - 1) ≠ 0 ∧
          o = adjoin ⟪concat (childrenWord a (fstIdx (refill a (π₁ record) (state - 1)))) record, 0⟫
            (sndIdx (refill a (π₁ record) (state - 1))) + 1) ∨
        (state ≠ 0 ∧ π₂ record = 1 ∧ refill b (π₁ record) (state - 1) ≠ 0 ∧
          o = adjoin ⟪concat (childrenWord b (fstIdx (refill b (π₁ record) (state - 1)))) record, 1⟫
            (sndIdx (refill b (π₁ record) (state - 1))) + 1)) := by
    simp [stepGraph]
  rw [hh]
  by_cases hz : state = 0 <;> by_cases hk₀ : π₂ record = 0 <;>
    by_cases hk₁ : π₂ record = 1 <;>
    by_cases hl : refill a (π₁ record) (state - 1) = 0 <;>
    by_cases hr : refill b (π₁ record) (state - 1) = 0 <;>
      simp_all [step]

@[simp] theorem stepGraph_eval_vec (a b : RawPolynomial) (v : Fin 3 → M) :
    (stepGraph a b).val.Evalb v ↔ v 0 = step a b (v 1) (v 2) := by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using stepGraph_eval a b (v 0) (v 1) (v 2)

instance step_defined (a b : RawPolynomial) :
    𝚺₁-Function₂ (step a b : M → M → M) via stepGraph a b :=
  .mk fun v => by simp

instance step_definable (a b : RawPolynomial) : 𝚺₁-Function₂ (step a b : M → M → M) :=
  (step_defined a b).to_definable

@[simp] theorem step_zero (a b : RawPolynomial) (record : M) : step a b record 0 = 0 := by
  simp [step]

/-- This is a Foundation finite computation-record construction. -/
def construction (a b : RawPolynomial) : PR.Construction M (blueprint a b) where
  zero v := v 1
  succ v i prev := step a b (nth (v 0) i) prev
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint]

noncomputable def runPrefix (a b : RawPolynomial) (word n initial : M) : M :=
  (construction a b).result ![word, initial] n

noncomputable def run (a b : RawPolynomial) (word initial : M) : M :=
  runPrefix a b word (len word) initial

@[simp] theorem prefix_zero (a b : RawPolynomial) (word initial : M) :
    runPrefix a b word 0 initial = initial := by simp [runPrefix, construction]

@[simp] theorem prefix_succ (a b : RawPolynomial) (word n initial : M) :
    runPrefix a b word (n + 1) initial = step a b (nth word n) (runPrefix a b word n initial) := by
  simp [runPrefix, construction]

@[simp] theorem prefixGraph_eval (a b : RawPolynomial) (o n word initial : M) :
    (prefixGraph a b).val.Evalb ![o, n, word, initial] ↔ o = runPrefix a b word n initial := by
  have hp : (fun i : Fin 2 => ![o, n, word, initial] i.succ.succ) = ![word, initial] := by
    funext i
    fin_cases i <;> rfl
  simpa [prefixGraph, runPrefix, hp] using
    (construction (M := M) a b).result_defined_iff ![o, n, word, initial]

@[simp] theorem prefixGraph_eval_vec (a b : RawPolynomial) (v : Fin 4 → M) :
    (prefixGraph a b).val.Evalb v ↔ v 0 = runPrefix a b (v 2) (v 1) (v 3) := by
  have hv : ![v 0, v 1, v 2, v 3] = v := (Matrix.fun_eq_vec_four v).symm
  simpa [hv] using prefixGraph_eval a b (v 0) (v 1) (v 2) (v 3)

instance prefix_defined (a b : RawPolynomial) :
    𝚺₁-Function₃ (runPrefix a b : M → M → M → M) via prefixValueGraph a b :=
  .mk fun v => by simp [prefixValueGraph]

instance prefix_definable (a b : RawPolynomial) :
    𝚺₁-Function₃ (runPrefix a b : M → M → M → M) := (prefix_defined a b).to_definable

@[simp] theorem runGraph_eval (a b : RawPolynomial) (o word initial : M) :
    (runGraph a b).val.Evalb ![o, word, initial] ↔ o = run a b word initial := by
  simp [runGraph, run]

instance run_defined (a b : RawPolynomial) :
    𝚺₁-Function₂ (run a b : M → M → M) via runGraph a b := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using runGraph_eval a b (v 0) (v 1) (v 2)

instance run_definable (a b : RawPolynomial) : 𝚺₁-Function₂ (run a b : M → M → M) :=
  (run_defined a b).to_definable

@[simp] theorem carrier_eval (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] ∧
        run a b word 1 = adjoin ⟪word, if formula then 1 else 0⟫ 0 + 1 := by
  cases formula <;> simp [carrier]

@[simp] theorem run_nil (a b : RawPolynomial) (initial : M) : run a b 0 initial = initial := by
  simp [run]

@[simp] theorem not_carrier_nil (formula : Bool) (a b : RawPolynomial) :
    ¬(carrier formula a b).val.Evalb (M := M) ![0] := by
  intro h
  have he := ((carrier_eval formula a b (0 : M)).mp h).2
  simp at he

/-- Prefix computations depend only on the displayed runPrefix, even at
nonstandard lengths. The induction formula is Pi-one. -/
theorem prefix_congr (a b : RawPolynomial) (word other n initial : M)
    (h : ∀ i < n, nth word i = nth other i) :
    runPrefix a b word n initial = runPrefix a b other n initial := by
  induction n using ISigma1.pi1_succ_induction generalizing word other initial
  · definability
  case zero => simp
  case succ n ih =>
    have hp : ∀ i < n, nth word i = nth other i :=
      fun i hi => h i (lt_trans hi (by simp))
    rw [prefix_succ, prefix_succ, ih word other initial hp, h n (by simp)]

/-- Processing an appended suffix is left-to-right composition of the two stack
computations. -/
theorem prefix_append (a b : RawPolynomial) (word suffix k initial : M) :
    runPrefix a b (Words.append word suffix) (len word + k) initial =
      runPrefix a b suffix k (run a b word initial) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    simpa [run] using prefix_congr a b (Words.append word suffix) word (len word) initial
      (fun i hi => Words.nth_append_left word suffix i hi)
  case succ k ih =>
    have he : len word + (k + 1) = (len word + k) + 1 := by simp [add_assoc]
    rw [he, prefix_succ, prefix_succ, Words.nth_append_right, ih]

theorem run_append (a b : RawPolynomial) (word suffix initial : M) :
    run a b (Words.append word suffix) initial =
      run a b suffix (run a b word initial) := by
  unfold run
  rw [Words.len_append, prefix_append]
  rfl

/-- A final record is executed after the entire preceding word. This is the ordering
required by the postfix constructors. -/
@[simp] theorem run_snoc (a b : RawPolynomial) (word record initial : M) :
    run a b (concat word record) initial = step a b record (run a b word initial) := by
  rw [← Words.append_singleton, run_append]
  have hlen : len (adjoin record (0 : M)) = 0 + 1 := by simp
  change runPrefix a b (adjoin record 0) (len (adjoin record 0)) (run a b word initial) = _
  rw [hlen, prefix_succ]
  simp

/-- The canonical term constructor consumes exactly its ordered child stack and pushes its
complete postfix word. -/
theorem step_term_constructor {X Y : Carrier} (a b : RawPolynomial) (u st : M)
    (h : (rawCarrier X Y a).val.Evalb ![u]) :
    step a b ⟪shape a u, 0⟫ (childStack a u st + 1) =
      adjoin ⟪constructor false a u, 0⟫ st + 1 := by
  simp [step, refill_shape a u st h, constructor]

theorem step_formula_constructor {X Y : Carrier} (a b : RawPolynomial) (u st : M)
    (h : (rawCarrier X Y b).val.Evalb ![u]) :
    step a b ⟪shape b u, 1⟫ (childStack b u st + 1) =
      adjoin ⟪constructor true b u, 1⟫ st + 1 := by
  simp [step, refill_shape b u st h, constructor]

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
