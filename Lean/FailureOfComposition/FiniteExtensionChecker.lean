/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.FiniteFunctionCoding
public import FailureOfComposition.FirstSuccessGraph
public import FailureOfComposition.SigmaOneRealization
public import FailureOfComposition.TypedNearProduct
public import PCats.DomSemilattice

/-!
# The finite-extension formula and checker

The formula `extensionFormula` is defined before the program that realizes it.
Its two free variables are an internal finite-function code and an internal
program index.  Only after proving its model semantics do we select a fixed
external production index `zeroTestIndex`, whose output is zero exactly when
the formula holds.  The checker index is the effective computation-domain
index of that zero test.

For standard external `c` and `i`, `Preceq T c i` is the finite family of
`T`-derivability assertions for the production eventual graph.  The passage
from the single closed `extensionFormula` instance to that family uses
first-order completeness and the fact that every element below a standard
bound is standard.  It assumes only `[PA ≼ T]`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CategoryTheory CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.FiniteExtensionChecker

open CodedObjectMembership ConcreteEvaluator FiniteFunctionCoding
open ProofSearch SigmaOneRealization TypedNearProduct TypedProgramCategory
open UniformIndexQuotient

noncomputable section

/-! ## The all-internal extension formula -/

/-- The fixed Sigma-one formula `Ext(c,i)`.  Its program-index variable is an
internal arithmetic variable; no fixed-index eventual-graph theorem is used in
its definition. -/
def extensionFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “c i. ∀ n < c, ∀ v < c,
    !finiteEntryFormula.val c n v →
      !canonicalPartrecGraphFormula.val i n v”

@[simp] theorem extensionFormula_eval_bounded
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : M) :
    extensionFormula.val.Evalb ![c, i] ↔
      ∀ n < c, ∀ v < c, FiniteEntryModel c n v →
        Semiformula.Evalb ![i, n, v]
          (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  simp [extensionFormula]

/-- The displayed bounds do not change the intended finite-entry reading,
because membership of the paired entry already puts both coordinates below
the code. -/
theorem extensionFormula_eval_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : M) :
    extensionFormula.val.Evalb ![c, i] ↔
      ∀ n v : M, FiniteEntryModel c n v →
        Semiformula.Evalb ![i, n, v]
          (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  rw [extensionFormula_eval_bounded]
  constructor
  · intro h n v hentry
    exact h n (finiteEntryModel_input_lt hentry) v
      (finiteEntryModel_output_lt hentry) hentry
  · intro h n _ v _ hentry
    exact h n v hentry

set_option maxHeartbeats 800000 in
-- Expanding the universal program graph exceeds the default heartbeat limit.
/-- A closed standard instance of `Ext` is exactly the finite family of
production graph assertions, interpreted in any PA model.  Here `i` is fixed
externally, which is precisely the scope in which the accepted first-success
comparison applies. -/
theorem extensionFormula_numeral_eval_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : ℕ) :
    extensionFormula.val.Evalb
        ![(ORingStructure.numeral c : M),
          (ORingStructure.numeral i : M)] ↔
      ∀ n v : ℕ, FiniteEntry c n v →
        (eventualGraph i).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral v : M)] := by
  rw [extensionFormula_eval_iff]
  constructor
  · intro h n v hentry
    apply (canonicalPartrecGraphFormula_eval_iff_eventualGraph i
      (ORingStructure.numeral n : M)
      (ORingStructure.numeral v : M)).mp
    apply h (ORingStructure.numeral n) (ORingStructure.numeral v)
    simpa only [numeral_eq_natCast] using
      (finiteEntryModel_numeral_iff (M := M) c n v).mpr hentry
  · intro h n v hentry
    have hn : n < (ORingStructure.numeral c : M) :=
      finiteEntryModel_input_lt hentry
    have hv : v < (ORingStructure.numeral c : M) :=
      finiteEntryModel_output_lt hentry
    obtain ⟨a, ha, rfl⟩ :=
      (iff_lt_numeral_exists_numeral (M := M)
        (x := n) (n := c)).mp hn
    obtain ⟨b, hb, rfl⟩ :=
      (iff_lt_numeral_exists_numeral (M := M)
        (x := v) (n := c)).mp hv
    apply (canonicalPartrecGraphFormula_eval_iff_eventualGraph i
      (ORingStructure.numeral a : M)
      (ORingStructure.numeral b : M)).mpr
    apply h a b
    apply (finiteEntryModel_numeral_iff (M := M) c a b).mp
    simpa only [numeral_eq_natCast] using hentry

/-- Evaluation of a closed `Ext` instance reduces to evaluation at its two
standard numerals. -/
@[simp] theorem extensionFormula_instance_eval
    {M : Type*} [ORingStructure M] (c i : ℕ) :
    (extensionFormula.val/[c, i]).Evalb (M := M) ![] ↔
      extensionFormula.val.Evalb
        ![(ORingStructure.numeral c : M),
          (ORingStructure.numeral i : M)] := by
  simp

/-- The production-numbering counterpart of `c \preceq_T i`: each selected
finite entry has a `T`-proof of the corresponding eventual-graph instance. -/
def Preceq (T : ArithmeticTheory) (c i : ℕ) : Prop :=
  ∀ n v : ℕ, FiniteEntry c n v →
    T ⊢ (eventualGraph i).val/[n, v]

/-- For fixed external parameters, the single closed `Ext` formula and the
finite family of graph derivations are equivalent.  No consistency, semantic
soundness of `T` in the standard model, or Delta-one hypothesis is used. -/
theorem proves_extensionFormula_iff_preceq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔ Preceq T c i := by
  constructor
  · intro hext n v hentry
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have hextM := consequence_iff.mp (Theory.Proof.sound hext) M hM
    rw [models_iff, extensionFormula_instance_eval,
      extensionFormula_numeral_eval_iff] at hextM
    rw [models_iff, graph_instance_eval]
    exact hextM n v hentry
  · intro hall
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    rw [models_iff, extensionFormula_instance_eval,
      extensionFormula_numeral_eval_iff]
    intro n v hentry
    have hp := hall n v hentry
    have hpM := consequence_iff.mp (Theory.Proof.sound hp) M hM
    rw [models_iff, graph_instance_eval] at hpM
    exact hpM

/-! ## A fixed zero test and its computation domain -/

/-- The functional zero-valued graph used to semidecide `Ext`.  The input is
an arithmetic pair; pairing here is Foundation's arithmetic pairing. -/
def zeroTestGraph : Graph := .mkSigma
  “x y. y = 0 ∧ ∃ c, ∃ i,
    !natPairFormula.val x c i ∧ !extensionFormula.val c i”

@[simp] theorem zeroTestGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    zeroTestGraph.val.Evalb ![x, y] ↔
      y = 0 ∧ extensionFormula.val.Evalb ![pi₁ x, pi₂ x] := by
  rw [show zeroTestGraph.val.Evalb ![x, y] ↔
      y = 0 ∧ ∃ c i : M, x = pair c i ∧
        extensionFormula.val.Evalb ![c, i] by simp [zeroTestGraph]]
  constructor
  · rintro ⟨hy, c, i, rfl, hext⟩
    simpa only [pi₁_pair, pi₂_pair] using ⟨hy, hext⟩
  · rintro ⟨hy, hext⟩
    exact ⟨hy, pi₁ x, pi₂ x, (pair_unpair x).symm, hext⟩

theorem zeroTestGraph_functional : Functional zeroTestGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact (zeroTestGraph_eval x y).mp hy |>.1 |>.trans
    ((zeroTestGraph_eval x z).mp hz).1.symm

/-- One fixed external production index realizing the zero test. -/
def zeroTestIndex : ℕ :=
  Classical.choose (realize_graph zeroTestGraph zeroTestGraph_functional)

theorem zeroTestIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph zeroTestIndex) zeroTestGraph :=
  Classical.choose_spec (realize_graph zeroTestGraph zeroTestGraph_functional)

@[simp] theorem eventualGraph_zeroTestIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph zeroTestIndex).val.Evalb ![x, y] ↔
      y = 0 ∧ extensionFormula.val.Evalb ![pi₁ x, pi₂ x] := by
  have h := consequence_iff.mp (Theory.Proof.sound zeroTestIndex_uniform)
    M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (zeroTestGraph_eval x y)

@[simp] theorem eventualGraph_zeroTestIndex_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i y : M) :
    (eventualGraph zeroTestIndex).val.Evalb ![pair c i, y] ↔
      y = 0 ∧ extensionFormula.val.Evalb ![c, i] := by
  simpa only [pi₁_pair, pi₂_pair] using
    eventualGraph_zeroTestIndex_eval (pair c i) y

/-- The checker index is the effective computation-domain program of the zero
test, not a second selected realizer. -/
def extensionCheckerIndex : ℕ := domainIndex zeroTestIndex

/-- The explicit graph of the finite-extension partial identity. -/
def extensionCheckerGraph : Graph := .mkSigma
  “x y. y = x ∧ ∃ c, ∃ i,
    !natPairFormula.val x c i ∧ !extensionFormula.val c i”

@[simp] theorem extensionCheckerGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    extensionCheckerGraph.val.Evalb ![x, y] ↔
      y = x ∧ extensionFormula.val.Evalb ![pi₁ x, pi₂ x] := by
  rw [show extensionCheckerGraph.val.Evalb ![x, y] ↔
      y = x ∧ ∃ c i : M, x = pair c i ∧
        extensionFormula.val.Evalb ![c, i] by
    simp [extensionCheckerGraph]]
  constructor
  · rintro ⟨hy, c, i, rfl, hext⟩
    simpa only [pi₁_pair, pi₂_pair] using ⟨hy, hext⟩
  · rintro ⟨hy, hext⟩
    exact ⟨hy, pi₁ x, pi₂ x, (pair_unpair x).symm, hext⟩

/-- PA-uniform graph equation for the checker. -/
theorem extensionCheckerIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph extensionCheckerIndex)
      extensionCheckerGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [extensionCheckerIndex, eventualGraph_domainIndex_eval,
    extensionCheckerGraph_eval]
  constructor
  · rintro ⟨hy, z, hz⟩
    exact ⟨hy, (eventualGraph_zeroTestIndex_eval x z).mp hz |>.2⟩
  · rintro ⟨hy, hext⟩
    exact ⟨hy, 0,
      (eventualGraph_zeroTestIndex_eval x 0).mpr ⟨rfl, hext⟩⟩

@[simp] theorem eventualGraph_extensionCheckerIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph extensionCheckerIndex).val.Evalb ![x, y] ↔
      y = x ∧ extensionFormula.val.Evalb ![pi₁ x, pi₂ x] := by
  rw [extensionCheckerIndex, eventualGraph_domainIndex_eval]
  constructor
  · rintro ⟨hy, z, hz⟩
    exact ⟨hy, (eventualGraph_zeroTestIndex_eval x z).mp hz |>.2⟩
  · rintro ⟨hy, hext⟩
    exact ⟨hy, 0,
      (eventualGraph_zeroTestIndex_eval x 0).mpr ⟨rfl, hext⟩⟩

@[simp] theorem eventualGraph_extensionCheckerIndex_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i y : M) :
    (eventualGraph extensionCheckerIndex).val.Evalb ![pair c i, y] ↔
      y = pair c i ∧ extensionFormula.val.Evalb ![c, i] := by
  simpa only [pi₁_pair, pi₂_pair] using
    eventualGraph_extensionCheckerIndex_eval (pair c i) y

/-! ## Typed checker domain -/

abbrev PairOmega : STObjectCode := .product .omega .omega

/-- The typed zero test on the actual product of two number objects. -/
def zeroTestArrow (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T PairOmega ⟶ omegaObject T :=
  arrowOfIndex T PairOmega .omega zeroTestIndex

/-- The typed finite-extension partial identity. -/
def extensionCheckerArrow (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T PairOmega ⟶ object T PairOmega :=
  arrowOfIndex T PairOmega PairOmega extensionCheckerIndex

/-- The product of two number objects has the total selected idempotent. -/
theorem objectIdempotent_pairOmega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    objectIdempotent T PairOmega = 1 := by
  rw [objectIdempotent_product, objectIdempotent_omega,
    tensorClass_one_one]

/-- Normalization of the zero test preserves its quotient class. -/
theorem zeroTestArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (zeroTestArrow T).1 = classOf T zeroTestIndex := by
  change objectIdempotent T .omega * classOf T zeroTestIndex *
      objectIdempotent T PairOmega = classOf T zeroTestIndex
  rw [objectIdempotent_omega, objectIdempotent_pairOmega]
  simp

/-- Normalization of the checker preserves its quotient class. -/
theorem extensionCheckerArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (extensionCheckerArrow T).1 = classOf T extensionCheckerIndex := by
  change objectIdempotent T PairOmega * classOf T extensionCheckerIndex *
      objectIdempotent T PairOmega = classOf T extensionCheckerIndex
  rw [objectIdempotent_pairOmega]
  simp

theorem eqIndex_normalize_zeroTestIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (normalizeIndex PairOmega .omega zeroTestIndex)
      zeroTestIndex := by
  apply (classOf_eq_classOf_iff T _ _).mp
  rw [← arrowOfIndex_val]
  exact zeroTestArrow_val T

theorem eqIndex_normalize_extensionCheckerIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (normalizeIndex PairOmega PairOmega extensionCheckerIndex)
      extensionCheckerIndex := by
  apply (classOf_eq_classOf_iff T _ _).mp
  rw [← arrowOfIndex_val]
  exact extensionCheckerArrow_val T

/-- The typed checker is the concrete computation-domain restriction of the
typed zero test. -/
theorem extensionCheckerArrow_eq_domainArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    extensionCheckerArrow T = domainArrow T (zeroTestArrow T) := by
  apply CodedHom.ext
  change (extensionCheckerArrow T).1 =
    domainClass T (zeroTestArrow T).1
  rw [extensionCheckerArrow_val, zeroTestArrow_val, domainClass_classOf]
  rfl

/-- The checker as an element of the domain semilattice on the actual typed
product object. -/
def extensionDomain
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    CategoryTheory.DomSemilattice (object T PairOmega) where
  hom := extensionCheckerArrow T
  isDomain := by
    rw [extensionCheckerArrow_eq_domainArrow, domainArrow_eq_rst]
    exact PCategory.rst_rst (zeroTestArrow T)

@[simp] theorem extensionDomain_hom
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (extensionDomain T).hom = extensionCheckerArrow T :=
  rfl

/-! ## Closed-point derivability -/

/-- The zero-test graph tag is derivably equivalent to the independently
defined closed `Ext` instance. -/
theorem proves_zeroTest_iff_extension
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (c i : ℕ) :
    (T ⊢ (eventualGraph zeroTestIndex).val/[
      Nat.pair c i, (0 : ℕ)]) ↔
      T ⊢ extensionFormula.val/[c, i] := by
  constructor
  · intro htest
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have hMtest := consequence_iff.mp (Theory.Proof.sound htest) M hM
    rw [models_iff, graph_instance_eval] at hMtest
    rw [models_iff, extensionFormula_instance_eval]
    have hpair : (ORingStructure.numeral (Nat.pair c i) : M) =
        pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
      simpa only [numeral_eq_natCast] using
        (coe_pair_eq_pair_coe (V := M) c i)
    rw [hpair, eventualGraph_zeroTestIndex_pair_eval] at hMtest
    exact hMtest.2
  · intro hext
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have hMext := consequence_iff.mp (Theory.Proof.sound hext) M hM
    rw [models_iff, extensionFormula_instance_eval] at hMext
    rw [models_iff, graph_instance_eval]
    have hpair : (ORingStructure.numeral (Nat.pair c i) : M) =
        pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
      simpa only [numeral_eq_natCast] using
        (coe_pair_eq_pair_coe (V := M) c i)
    rw [hpair, eventualGraph_zeroTestIndex_pair_eval]
    exact ⟨rfl, hMext⟩

theorem proves_checker_iff_extension
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (c i : ℕ) :
    (T ⊢ (eventualGraph extensionCheckerIndex).val/[
      Nat.pair c i, Nat.pair c i]) ↔
      T ⊢ extensionFormula.val/[c, i] := by
  constructor
  · intro hcheck
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have hMcheck := consequence_iff.mp (Theory.Proof.sound hcheck) M hM
    rw [models_iff, graph_instance_eval] at hMcheck
    rw [models_iff, extensionFormula_instance_eval]
    have hpair : (ORingStructure.numeral (Nat.pair c i) : M) =
        pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
      simpa only [numeral_eq_natCast] using
        (coe_pair_eq_pair_coe (V := M) c i)
    rw [hpair, eventualGraph_extensionCheckerIndex_pair_eval] at hMcheck
    exact hMcheck.2
  · intro hext
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have hMext := consequence_iff.mp (Theory.Proof.sound hext) M hM
    rw [models_iff, extensionFormula_instance_eval] at hMext
    rw [models_iff, graph_instance_eval]
    have hpair : (ORingStructure.numeral (Nat.pair c i) : M) =
        pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
      simpa only [numeral_eq_natCast] using
        (coe_pair_eq_pair_coe (V := M) c i)
    rw [hpair, eventualGraph_extensionCheckerIndex_pair_eval]
    exact ⟨rfl, hMext⟩

/-- Representative-independent closed-point theorem for the typed checker
domain. -/
theorem extensionDomain_provableAt_iff
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (c i : ℕ) :
    ProvableAt T (extensionDomain T).hom.val
        (Nat.pair c i) (Nat.pair c i) ↔
      T ⊢ extensionFormula.val/[c, i] := by
  rw [extensionDomain_hom, extensionCheckerArrow_val, provableAt_classOf]
  exact proves_checker_iff_extension T c i

/-- The checker, the all-internal `Ext` formula, and the external finite family
of graph derivations have exactly the same closed points. -/
theorem extensionDomain_provableAt_iff_preceq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (c i : ℕ) :
    ProvableAt T (extensionDomain T).hom.val
        (Nat.pair c i) (Nat.pair c i) ↔
      Preceq T c i :=
  (extensionDomain_provableAt_iff T c i).trans
    (proves_extensionFormula_iff_preceq T c i)

/-! ## Closed finite-code applications -/

/-- The empty finite function is extended by every external program index. -/
theorem preceq_zero (T : ArithmeticTheory) (i : ℕ) :
    Preceq T 0 i := by
  intro n v hentry
  exact False.elim (not_finiteEntry_zero n v hentry)

theorem proves_extensionFormula_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (i : ℕ) :
    T ⊢ extensionFormula.val/[(0 : ℕ), i] :=
  (proves_extensionFormula_iff_preceq T 0 i).mpr (preceq_zero T i)

theorem extensionDomain_fixes_empty
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (i : ℕ) :
    ProvableAt T (extensionDomain T).hom.val
      (Nat.pair 0 i) (Nat.pair 0 i) :=
  (extensionDomain_provableAt_iff T 0 i).mpr
    (proves_extensionFormula_zero T i)

/-- Every selected entry of code one is the single pair `(0,0)`. -/
theorem finiteEntry_one_eq {n v : ℕ} (h : FiniteEntry 1 n v) :
    n = 0 ∧ v = 0 := by
  have hn := finiteEntry_input_lt h
  have hv := finiteEntry_output_lt h
  omega

/-- Code one, which contains `(0,0)`, is extended by the production identity
program. -/
theorem preceq_one_identity :
    Preceq 𝗣𝗔 1 Kleene.identityIndex := by
  intro n v hentry
  obtain ⟨rfl, rfl⟩ := finiteEntry_one_eq hentry
  rw [← provableAt_classOf]
  simpa only [← one_eq_classOf 𝗣𝗔] using provableAt_one 𝗣𝗔 0

theorem pa_proves_extensionFormula_one_identity :
    𝗣𝗔 ⊢ extensionFormula.val/[(1 : ℕ), Kleene.identityIndex] :=
  (proves_extensionFormula_iff_preceq 𝗣𝗔 1 Kleene.identityIndex).mpr
    preceq_one_identity

/-- The two displayed competing bits select the smaller output and reject the
larger one. -/
theorem competing_bits_select_smaller :
    FiniteEntry competingZeroOneCode 0 0 ∧
      ¬FiniteEntry competingZeroOneCode 0 1 :=
  ⟨finiteEntry_competing_zero, not_finiteEntry_competing_one⟩

end

end FailureOfComposition.FiniteExtensionChecker
