/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46FiniteSigmaOne
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-! # Primitive recursive tag readers with PA-provable arithmetic graphs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.PrimitiveRecursiveTags

/-- The seven constructors of Mathlib's numerical primitive recursion. -/
inductive Code where
  | zero | succ | left | right
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code

namespace Code

def eval : Code → ℕ → ℕ
  | .zero, _ => 0
  | .succ, x => x + 1
  | .left, x => x.unpair.1
  | .right, x => x.unpair.2
  | .pair c d, x => Nat.pair (eval c x) (eval d x)
  | .comp c d, x => eval c (eval d x)
  | .prec c d, x => Nat.rec (eval c x.unpair.1)
      (fun i prev => eval d (Nat.pair x.unpair.1 (Nat.pair i prev))) x.unpair.2

end Code

/-- Elimination of the primitive recursion derivation constructs code;
no representation or totality assertion is supplied as input. -/
theorem exists_code {f : ℕ → ℕ} (hf : Nat.Primrec f) : ∃ c : Code, c.eval = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair hf hg ihf ihg =>
    obtain ⟨c, hc⟩ := ihf
    obtain ⟨d, hd⟩ := ihg
    exact ⟨.pair c d, by funext x; simp only [Code.eval, hc, hd]⟩
  | comp hf hg ihf ihg =>
    obtain ⟨c, hc⟩ := ihf
    obtain ⟨d, hd⟩ := ihg
    exact ⟨.comp c d, by funext x; simp only [Code.eval, hc, hd]⟩
  | prec hf hg ihf ihg =>
    obtain ⟨c, hc⟩ := ihf
    obtain ⟨d, hd⟩ := ihg
    exact ⟨.prec c d, by funext x; simp only [Code.eval, hc, hd, Nat.unpaired]⟩

theorem exists_code_primrec {f : ℕ → ℕ} (hf : _root_.Primrec f) :
    ∃ c : Code, c.eval = f := exists_code (_root_.Primrec.nat_iff.mp hf)

abbrev Graph := 𝚺₁.Semisentence 2

def zeroGraph : Graph := .mkSigma “y x. y = 0”
def succGraph : Graph := .mkSigma “y x. y = x + 1”
def leftGraph : Graph := .mkSigma pi₁Def.val pi₁Def.sigma_prop.of_zero
def rightGraph : Graph := .mkSigma pi₂Def.val pi₂Def.sigma_prop.of_zero

def pairGraph (A B : Graph) : Graph := .mkSigma
  “y x. ∃ a b, !A.val a x ∧ !B.val b x ∧ !pairDef.val y a b”

def compGraph (A B : Graph) : Graph := .mkSigma
  “y x. ∃ z, !B.val z x ∧ !A.val y z”

/-- Variables are output, previous value, recursion index, fixed parameter. -/
def stepGraph (B : Graph) : 𝚺₁.Semisentence 4 := .mkSigma
  “u prev i z. ∃ t s, !pairDef.val t i prev ∧ !pairDef.val s z t ∧ !B.val u s”

def precBlueprint (A B : Graph) : PR.Blueprint 1 where
  zero := A
  succ := stepGraph B

def precGraph (A B : Graph) : Graph := .mkSigma
  “y x. ∃ z n, !pi₁Def.val z x ∧ !pi₂Def.val n x ∧
    !(precBlueprint A B).resultDef.val y n z”

def Code.graph : Code → Graph
  | .zero => zeroGraph
  | .succ => succGraph
  | .left => leftGraph
  | .right => rightGraph
  | .pair c d => pairGraph c.graph d.graph
  | .comp c d => compGraph c.graph d.graph
  | .prec c d => precGraph c.graph d.graph

section Models

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem zeroGraph_eval (x y : M) : zeroGraph.val.Evalb ![y, x] ↔ y = 0 := by
  simp [zeroGraph]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem succGraph_eval (x y : M) : succGraph.val.Evalb ![y, x] ↔ y = x + 1 := by
  simp [succGraph]

@[simp] theorem leftGraph_eval (x y : M) : leftGraph.val.Evalb ![y, x] ↔ y = π₁ x :=
  pi₁_defined.iff

@[simp] theorem rightGraph_eval (x y : M) : rightGraph.val.Evalb ![y, x] ↔ y = π₂ x :=
  pi₂_defined.iff

@[simp] theorem pairGraph_eval (A B : Graph) (x y : M) :
    (pairGraph A B).val.Evalb ![y, x] ↔
      ∃ a b : M, A.val.Evalb ![a, x] ∧ B.val.Evalb ![b, x] ∧ y = ⟪a, b⟫ := by
  simp [pairGraph]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem compGraph_eval (A B : Graph) (x y : M) :
    (compGraph A B).val.Evalb ![y, x] ↔
      ∃ z : M, B.val.Evalb ![z, x] ∧ A.val.Evalb ![y, z] := by
  simp [compGraph]

@[simp] theorem stepGraph_eval (B : Graph) (u prev i z : M) :
    (stepGraph B).val.Evalb ![u, prev, i, z] ↔ B.val.Evalb ![u, ⟪z, ⟪i, prev⟫⟫] := by
  simp [stepGraph]

@[simp] theorem precGraph_eval (A B : Graph) (x y : M) :
    (precGraph A B).val.Evalb ![y, x] ↔
      (precBlueprint A B).resultDef.val.Evalb ![y, π₂ x, π₁ x] := by
  simp [precGraph]

/-- This is the actual instantiation of Foundation's coded primitive
recursion construction from two already proved child graphs. -/
def precConstruction (A B : Graph) (f g : M → M)
    (hA : ∀ x y : M, A.val.Evalb ![y, x] ↔ y = f x)
    (hB : ∀ x y : M, B.val.Evalb ![y, x] ↔ y = g x) :
    PR.Construction M (precBlueprint A B) where
  zero v := f (v 0)
  succ v i prev := g ⟪v 0, ⟪i, prev⟫⟫
  zero_defined := .mk fun v => by
    change A.val.Evalb v ↔ v 0 = f (v 1)
    simpa only [← Matrix.fun_eq_vec_two v] using hA (v 1) (v 0)
  succ_defined := .mk fun v => by
    change (stepGraph B).val.Evalb v ↔ v 0 = g ⟪v 3, ⟪v 2, v 1⟫⟫
    have hv : ![v 0, v 1, v 2, v 3] = v := (Matrix.fun_eq_vec_four v).symm
    simpa only [hv] using
      (stepGraph_eval B (v 0) (v 1) (v 2) (v 3)).trans
        (hB ⟪v 3, ⟪v 2, v 1⟫⟫ (v 0))

@[simp] theorem precConstruction_graph (A B : Graph) (f g : M → M)
    (hA : ∀ x y : M, A.val.Evalb ![y, x] ↔ y = f x)
    (hB : ∀ x y : M, B.val.Evalb ![y, x] ↔ y = g x) (x y : M) :
    (precGraph A B).val.Evalb ![y, x] ↔
      y = (precConstruction A B f g hA hB).result ![π₁ x] (π₂ x) := by
  rw [precGraph_eval]
  simpa [Matrix.constant_eq_singleton] using
    (precConstruction A B f g hA hB).result_defined_iff ![y, π₂ x, π₁ x]

def chosenValue (A : Graph) (hA : ∀ x : M, ∃! y : M, A.val.Evalb ![y, x]) (x : M) : M :=
  Classical.choose! (hA x)

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem chosenValue_graph (A : Graph) (hA : ∀ x : M, ∃! y : M, A.val.Evalb ![y, x])
    (x y : M) : A.val.Evalb ![y, x] ↔ y = chosenValue A hA x := by
  constructor
  · intro h
    exact (hA x).unique h (Classical.choose!_spec (hA x))
  · intro h
    subst y
    exact Classical.choose!_spec (hA x)

/-- Totality and functionality are proved for every compiled constructor
in every PA model, including every nonstandard input and recursion index. -/
theorem Code.graph_existsUnique (c : Code) (x : M) :
    ∃! y : M, c.graph.val.Evalb ![y, x] := by
  induction c generalizing x with
  | zero => simp [Code.graph]
  | succ => simp [Code.graph]
  | left => simp [Code.graph]
  | right => simp [Code.graph]
  | pair c d ihc ihd =>
    obtain ⟨a, ha, hua⟩ := ihc x
    obtain ⟨b, hb, hub⟩ := ihd x
    refine ⟨⟪a, b⟫, (pairGraph_eval c.graph d.graph x _).mpr ⟨a, b, ha, hb, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨a', b', ha', hb', he⟩ := (pairGraph_eval c.graph d.graph x y).mp hy
    simpa only [hua a' ha', hub b' hb'] using he
  | comp c d ihc ihd =>
    obtain ⟨b, hb, hub⟩ := ihd x
    obtain ⟨a, ha, hua⟩ := ihc b
    refine ⟨a, (compGraph_eval c.graph d.graph x a).mpr ⟨b, hb, ha⟩, ?_⟩
    intro y hy
    obtain ⟨b', hb', ha'⟩ := (compGraph_eval c.graph d.graph x y).mp hy
    have he := hub b' hb'
    subst b'
    exact hua y ha'
  | prec c d ihc ihd =>
    let f := chosenValue c.graph ihc
    let g := chosenValue d.graph ihd
    have hA : ∀ x y : M, c.graph.val.Evalb ![y, x] ↔ y = f x :=
      chosenValue_graph c.graph ihc
    have hB : ∀ x y : M, d.graph.val.Evalb ![y, x] ↔ y = g x :=
      chosenValue_graph d.graph ihd
    simp only [Code.graph, precConstruction_graph c.graph d.graph f g hA hB]
    exact ⟨_, rfl, fun _ h => h⟩

def interpret (c : Code) (x : M) : M := chosenValue c.graph c.graph_existsUnique x

@[simp] theorem interpret_graph (c : Code) (x y : M) :
    c.graph.val.Evalb ![y, x] ↔ y = interpret c x :=
  chosenValue_graph c.graph c.graph_existsUnique x y

/-- The primitive-recursion constructor uses the model's complete index
carrier; this equation is not restricted to standard natural indices. -/
theorem interpret_prec (c d : Code) (x : M) :
    interpret (.prec c d) x =
      (precConstruction c.graph d.graph (interpret c) (interpret d)
        (interpret_graph c) (interpret_graph d)).result ![π₁ x] (π₂ x) :=
  (precConstruction_graph c.graph d.graph (interpret c) (interpret d)
    (interpret_graph c) (interpret_graph d) x _).mp
      ((interpret_graph (.prec c d) x _).mpr rfl)

@[simp] theorem interpret_prec_zero (c d : Code) (z : M) :
    interpret (.prec c d) ⟪z, 0⟫ = interpret c z := by
  rw [interpret_prec]
  simp [precConstruction]

theorem interpret_prec_succ (c d : Code) (z n : M) :
    interpret (.prec c d) ⟪z, n + 1⟫ =
      interpret d ⟪z, ⟪n, interpret (.prec c d) ⟪z, n⟫⟫⟫ := by
  simp only [interpret_prec, pi₁_pair, pi₂_pair, PR.Construction.result_succ]
  rfl

def deltaGraph (c : Code) : 𝚫₁.Semisentence 2 := c.graph.graphDelta

/-- The Delta-one pair is proper in every PA model by the constructed
functional interpretation; no extra model or presentation assumption occurs. -/
theorem deltaGraph_defined (c : Code) :
    𝚫₁.DefinedFunction (fun v : Fin 1 → M => interpret c (v 0)) (deltaGraph c) := by
  have h : 𝚺₁.DefinedFunction (fun v : Fin 1 → M => interpret c (v 0)) c.graph :=
    .mk fun v => by
      change c.graph.val.Evalb v ↔ v 0 = interpret c (v 1)
      simpa only [← Matrix.fun_eq_vec_two v] using interpret_graph c (v 1) (v 0)
  exact h.graph_delta

@[simp] theorem deltaGraph_pi_eval (c : Code) (x y : M) :
    (deltaGraph c).pi.val.Evalb ![y, x] ↔ y = interpret c x :=
  (deltaGraph_defined c).iff_delta_pi

end Models

@[simp] theorem arithmetic_unpair_nat (x : ℕ) : unpair x = Nat.unpair x := by
  have hp : Nat.pair (π₁ x) (π₂ x) = x := by simpa only [nat_pair_eq] using pair_unpair x
  have hu := congrArg Nat.unpair hp
  simpa only [Nat.unpair_pair] using hu

@[simp] theorem arithmetic_pi₁_nat (x : ℕ) : π₁ x = x.unpair.1 :=
  congrArg Prod.fst (arithmetic_unpair_nat x)

@[simp] theorem arithmetic_pi₂_nat (x : ℕ) : π₂ x = x.unpair.2 :=
  congrArg Prod.snd (arithmetic_unpair_nat x)

/-- Standard evaluation agrees with the external numerical recursion
that the Mathlib derivation denotes. -/
theorem Code.graph_nat_iff (c : Code) (x y : ℕ) :
    c.graph.val.Evalb ![y, x] ↔ y = c.eval x := by
  induction c generalizing x y with
  | zero => simp [Code.graph, Code.eval]
  | succ => simp [Code.graph, Code.eval]
  | left => simp [Code.graph, Code.eval]
  | right => simp [Code.graph, Code.eval]
  | pair c d ihc ihd =>
    change (pairGraph c.graph d.graph).val.Evalb ![y, x] ↔
      y = Nat.pair (c.eval x) (d.eval x)
    simp [ihc, ihd, nat_pair_eq]
  | comp c d ihc ihd =>
    change (compGraph c.graph d.graph).val.Evalb ![y, x] ↔ y = c.eval (d.eval x)
    simp only [compGraph_eval, ihc, ihd, exists_eq_left]
  | prec c d ihc ihd =>
    let q := precConstruction c.graph d.graph c.eval d.eval ihc ihd
    have hr (z n : ℕ) : q.result ![z] n =
        Nat.rec (c.eval z) (fun i prev => d.eval (Nat.pair z (Nat.pair i prev))) n := by
      induction n with
      | zero => simp [q, precConstruction]
      | succ n ih =>
        rw [q.result_succ, ih]
        simp [q, precConstruction, nat_pair_eq]
    change (precGraph c.graph d.graph).val.Evalb ![y, x] ↔ _
    rw [precConstruction_graph c.graph d.graph c.eval d.eval ihc ihd, hr]
    simp only [arithmetic_pi₁_nat, arithmetic_pi₂_nat, Code.eval]

@[simp] theorem interpret_nat (c : Code) (x : ℕ) : interpret c x = c.eval x :=
  (c.graph_nat_iff x _).mp ((interpret_graph c x _).mpr rfl)

def totalSentence (A : Graph) : ArithmeticSentence := “∀ x, ∃! y, !A.val y x”

def piTotalSentence (P : 𝚷₁.Semisentence 2) : ArithmeticSentence :=
  “∀ x, ∃! y, !P.val y x”

def graphAgreementSentence (A : Graph) (P : 𝚷₁.Semisentence 2) : ArithmeticSentence :=
  “∀ y x, !A.val y x ↔ !P.val y x”

def coherentSentence (c : Code) : ArithmeticSentence :=
  graphAgreementSentence c.graph (deltaGraph c).pi

theorem graph_total_PA (c : Code) : 𝗣𝗔 ⊢ totalSentence c.graph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, totalSentence]

theorem graph_coherent_PA (c : Code) : 𝗣𝗔 ⊢ coherentSentence c := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, coherentSentence, graphAgreementSentence]

theorem graph_pi_total_PA (c : Code) : 𝗣𝗔 ⊢ piTotalSentence (deltaGraph c).pi := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, piTotalSentence]

def codeFor {f : ℕ → ℕ} (hf : Nat.Primrec f) : Code := Classical.choose (exists_code hf)

theorem codeFor_spec {f : ℕ → ℕ} (hf : Nat.Primrec f) : (codeFor hf).eval = f :=
  Classical.choose_spec (exists_code hf)

/-- Every numerical primitive-recursion derivation yields a Sigma-one
and a Pi-one arithmetic graph, with totality and their equivalence proved
in PA, and with their actual standard interpretation equal to the input function. -/
theorem natPrimrec_representation {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ (A : Graph) (P : 𝚷₁.Semisentence 2),
      (𝗣𝗔 ⊢ totalSentence A) ∧ (𝗣𝗔 ⊢ piTotalSentence P) ∧
      (𝗣𝗔 ⊢ graphAgreementSentence A P) ∧
      ∀ x y : ℕ, (A.val.Evalb ![y, x] ↔ y = f x) ∧
        (P.val.Evalb ![y, x] ↔ y = f x) := by
  let c := codeFor hf
  refine ⟨c.graph, (deltaGraph c).pi, graph_total_PA c, graph_pi_total_PA c,
    graph_coherent_PA c, ?_⟩
  intro x y
  constructor
  · simpa only [c, codeFor_spec] using c.graph_nat_iff x y
  · simp only [deltaGraph_pi_eval, interpret_nat, c, codeFor_spec]

theorem primrec_representation {f : ℕ → ℕ} (hf : _root_.Primrec f) :
    ∃ (A : Graph) (P : 𝚷₁.Semisentence 2),
      (𝗣𝗔 ⊢ totalSentence A) ∧ (𝗣𝗔 ⊢ piTotalSentence P) ∧
      (𝗣𝗔 ⊢ graphAgreementSentence A P) ∧
      ∀ x y : ℕ, (A.val.Evalb ![y, x] ↔ y = f x) ∧
        (P.val.Evalb ![y, x] ↔ y = f x) :=
  natPrimrec_representation (_root_.Primrec.nat_iff.mp hf)

def tagPi {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ) : 𝚷₁.Semisentence 1 := .mkPi
  “x. !(deltaGraph (codeFor hf)).pi.val !!(FiniteSigmaOne.numeralTerm j) x”

@[simp] theorem tagPi_eval {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M) :
    (tagPi hf j).val.Evalb ![x] ↔
      ORingStructure.numeral j = interpret (codeFor hf) x := by
  simp [tagPi, FiniteSigmaOne.numeralTerm]

@[simp] theorem tagPi_nat {f : ℕ → ℕ} (hf : Nat.Primrec f) (j x : ℕ) :
    (tagPi hf j).val.Evalb ![x] ↔ f x = j := by
  have hi : interpret (codeFor hf) x = f x := by
    have h := (Code.graph_nat_iff (codeFor hf) x (interpret (codeFor hf) x)).mp
      ((interpret_graph (codeFor hf) x _).mpr rfl)
    simpa only [codeFor_spec] using h
  simp [tagPi_eval, hi, Nat.numeral_eq, eq_comm]


def tagSigma {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ) : 𝚺₁.Semisentence 1 := .mkSigma
  “x. !(codeFor hf).graph.val !!(FiniteSigmaOne.numeralTerm j) x”

@[simp] theorem tagSigma_eval {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M) :
    (tagSigma hf j).val.Evalb ![x] ↔
      ORingStructure.numeral j = interpret (codeFor hf) x := by
  simp [tagSigma, FiniteSigmaOne.numeralTerm]

def tagCoherentSentence {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ) : ArithmeticSentence :=
  “∀ x, !(tagSigma hf j).val x ↔ !(tagPi hf j).val x”

theorem tag_coherent_PA {f : ℕ → ℕ} (hf : Nat.Primrec f) (j : ℕ) :
    𝗣𝗔 ⊢ tagCoherentSentence hf j := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, tagCoherentSentence]

def primrecTagPi {f : ℕ → ℕ} (hf : _root_.Primrec f) (j : ℕ) : 𝚷₁.Semisentence 1 :=
  tagPi (_root_.Primrec.nat_iff.mp hf) j

@[simp] theorem primrecTagPi_nat {f : ℕ → ℕ} (hf : _root_.Primrec f) (j x : ℕ) :
    (primrecTagPi hf j).val.Evalb ![x] ↔ f x = j := tagPi_nat _ j x

/-- A real finite tag test for an arbitrary primitive-recursive reader,
with an actual PA-total interpretation on all nonstandard inputs. -/
def selectedCondition {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → FiniteSigmaOne.Carrier) : FiniteSigmaOne.Carrier :=
  .mkSigma (Finset.udisj (fun j : Fin k => (tagSigma hf j.val).val ⋏ (C j).val)) (by
    simp only [Hierarchy.finset_udisj_iff, Hierarchy.and_iff]
    intro j
    exact ⟨(tagSigma hf j.val).sigma_prop, (C j).sigma_prop⟩)

@[simp] theorem selectedCondition_eval {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → FiniteSigmaOne.Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M) :
    (selectedCondition hf C).val.Evalb ![x] ↔
      ∃ j : Fin k, ORingStructure.numeral j.val = interpret (codeFor hf) x ∧
        (C j).val.Evalb ![x] := by
  simp [selectedCondition]

def selectedList {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → FiniteSigmaOne.Carrier) : FiniteSigmaOne.Carrier :=
  FiniteSigmaOne.finiteMembership (selectedCondition hf C)

theorem selectedList_eval {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → FiniteSigmaOne.Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (selectedList hf C).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin k,
        ORingStructure.numeral j.val = interpret (codeFor hf) (nth a i) ∧
          (C j).val.Evalb ![nth a i] := by
  rw [selectedList, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval]
  simp only [selectedCondition_eval]

theorem selected_membership_PA {f : ℕ → ℕ} (hf : Nat.Primrec f) {k : ℕ}
    (C : Fin k → FiniteSigmaOne.Carrier) :
    𝗣𝗔 ⊢ FiniteSigmaOne.finiteMembershipSentence (selectedCondition hf C) :=
  FiniteSigmaOne.finite_membership_PA _

end CategoricalEssentialIncompleteness.V46.PrimitiveRecursiveTags
