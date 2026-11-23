/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuringSpecialization

/-! # Domains and values of the specialized tuple programs -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open NumericalTuples (Point code)
open EnumerableCarriers (val)

theorem positiveTuple_surjective (m : ℕ) : Function.Surjective (code (m+1)) := by
  induction m with
  | zero => exact fun n => ⟨n, rfl⟩
  | succ m ih =>
    intro n
    obtain ⟨x, hx⟩ := ih (Nat.unpair n).2
    exact ⟨((Nat.unpair n).1, x), (congrArg (Nat.pair (Nat.unpair n).1) hx).trans (Nat.pair_unpair n)⟩

/-- The recursive tuple bijections used by specialization in positive arity. -/
def positiveTupleCoding (m : ℕ) : NumericalTuples.Tuple (m+1) ≃ ℕ :=
  Equiv.ofBijective (code (m+1)) ⟨NumericalTuples.code_injective _, positiveTuple_surjective m⟩

theorem positiveTuple_computable (m : ℕ) :
    Computable (positiveTupleCoding m) ∧ Computable (positiveTupleCoding m).symm :=
  ⟨Computable.encode, (NumericalTuples.decodeTuple_partrec _).of_eq_tot
    (fun n => (NumericalTuples.mem_decodeTuple _ _ _).mpr ((positiveTupleCoding m).apply_symm_apply n))⟩

def vertexCode (j : WalkingSpan) : tupleCode.obj ((evaluation j).obj universal) ≅ EffectiveFork.natCarrier := by
  rcases j with _ | (_ | _)
  exacts [centerCode, endpointIso, endpointIso]

theorem vertex_hom (j : WalkingSpan) (n m : ℕ) : m ∈ val (vertexCode j).hom n ↔ m = n := by
  rcases j with _ | (_ | _)
  · have h : n ∈ (NumericalTuples.codedObject (ForkDiagonalObstruction.tupleSpace 4)).obj.support := by
      rw [codedCenterEq]
      exact Set.mem_univ _
    exact (val_eqToHom codedCenterEq n m).trans (and_iff_right h)
  · exact labelCode_hom n m
  · exact labelCode_hom n m

theorem vertex_inv (j : WalkingSpan) (n m : ℕ) : m ∈ val (vertexCode j).inv n ↔ m = n := by
  rcases j with _ | (_ | _)
  · exact (val_eqToHom codedCenterEq.symm n m).trans (and_iff_right (Set.mem_univ n))
  · exact labelCode_inv n m
  · exact labelCode_inv n m

def componentProgram {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal) :
    EnumerableCarriers.product (tupleCode.obj ((evaluation j).obj Y)) EffectiveFork.natCarrier ⟶
      EffectiveFork.natCarrier := by
  rcases j with _ | (_ | _)
  exacts [(forkProgram f).center, (forkProgram f).left, (forkProgram f).right]

theorem componentProgram_eq {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal) :
    componentProgram j f = EnumerableCarriers.partialProdMap (𝟙 _) (vertexCode j).inv ≫
      (componentProductIso j Y universal).inv ≫ component j (forkCode.map f) ≫ (vertexCode j).hom := by
  rcases j with _ | (_ | _) <;> rfl

theorem componentIndex_program {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal)
    (n x : ℕ) : eval (componentIndex f j n) x = val (componentProgram j f) (Nat.pair n x) := by
  rcases j with _ | (_ | _)
  all_goals
    exact (EffectiveFork.eval_specialize _ n x).trans (congrFun (EffectiveFork.eval_program _) _)

theorem componentIndex_outside {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal)
    (z : NumericalTuples.Tuple (Y.obj.obj j).dimension) (hz : z ∉ (Y.obj.obj j).support) (x : ℕ) :
    eval (componentIndex f j (code _ z)) x = Part.none := by
  rw [componentIndex_program]
  apply Part.eq_none_iff.mpr
  intro w hw
  have hs := EnumerableCarriers.val_source _ _ _ hw
  change (Nat.unpair (Nat.pair (code _ z) x)).1 ∈ NumericalTuples.codedSupport (Y.obj.obj j) ∧ _ at hs
  exact hz ((NumericalTuples.code_mem_codedSupport _ _).mp (by simpa only [Nat.unpair_pair] using hs.1))

def componentMorphism {X Y Z : ForkSpans} (j : WalkingSpan) (f : forkProduct X Y ⟶ Z) :
    tupleProduct ((evaluation j).obj X) ((evaluation j).obj Y) ⟶ (evaluation j).obj Z :=
  (productComparison j X Y).inv ≫ (evaluation j).map f

theorem componentMorphism_value {X Y Z : ForkSpans} (j : WalkingSpan) (f : forkProduct X Y ⟶ Z)
    (a b : ℕ) : binaryValue (componentMorphism j f) a b =
      val ((componentProductIso j X Y).inv ≫ component j (forkCode.map f)) (Nat.pair a b) := by
  let i := productComparison j X Y
  let p := tupleProductIso ((evaluation j).obj X) ((evaluation j).obj Y)
  have he : tupleCode.mapIso i ≪≫ p = componentProductIso j X Y :=
    Iso.ext (component_product_comparison j X Y)
  have hi : p.inv ≫ tupleCode.map i.inv = (componentProductIso j X Y).inv := congrArg Iso.inv he
  change val (p.inv ≫ tupleCode.map (i.inv ≫ (evaluation j).map f)) _ = _
  rw [tupleCode.map_comp, ← Category.assoc, hi, evaluation_value]

theorem componentIndex_value {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal)
    (z : Point (Y.obj.obj j)) (x : ℕ) :
    eval (componentIndex f j (code _ z.val)) x = binaryValue (componentMorphism j f) (code _ z.val) x := by
  let n := code _ z.val
  have hs : n ∈ (tupleCode.obj ((evaluation j).obj Y)).support :=
    (NumericalTuples.code_mem_codedSupport _ z.val).mpr z.property
  have hi : val (EnumerableCarriers.partialProdMap (𝟙 (tupleCode.obj ((evaluation j).obj Y)))
      (vertexCode j).inv) (Nat.pair n x) = Part.some (Nat.pair n x) := by
    apply Part.eq_some_iff.mpr
    rw [EnumerableCarriers.mem_partialProdMap_iff]
    simp [EnumerableCarriers.val_id, mem_supportIdentity, vertex_inv, hs]
  rw [componentIndex_program, componentProgram_eq, componentMorphism_value]
  apply Part.ext
  intro w
  dsimp only [n] at hi
  simp only [EnumerableCarriers.mem_val_comp, hi, Part.mem_some_iff, vertex_hom,
    exists_eq_left, exists_eq_right']

/-- Each component program has exactly the graph of the given partial span at its
parameter, including inputs outside the span's domain. -/
theorem component_fibre {Y : ForkSpans} (j : WalkingSpan) (f : forkProduct Y universal ⟶ universal)
    (z : Point (Y.obj.obj j)) (x w : Point (universal.obj.obj j)) :
    code _ w.val ∈ eval (componentIndex f j (code _ z.val)) (code _ x.val) ↔
      Graph (componentMorphism j f) (pairPoint z x) w := by
  rw [componentIndex_value]
  exact binaryValue_graph (componentMorphism j f) z x w

/-- Decoding the program selected at an endpoint parameter gives the fibre of the
original partial span. -/
theorem endpoint_decoded_fibre {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint)
    (z : Point Z.obj) (l x a b : ℕ) :
    Graph f (pairPoint z (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval (endpointIndex f (code _ z.val)) (Nat.pair l x)) := by
  rw [← binaryValue_graph, endpointIndex_value]
  change Nat.pair a b ∈ binaryValue f _ (Nat.pair l x) ↔ _
  constructor
  · intro h
    exact (Part.mem_map_iff _).mpr ⟨_, h, Nat.unpair_pair _ _⟩
  · intro h
    obtain ⟨n, hn, he⟩ := (Part.mem_map_iff _).mp h
    have en : n = Nat.pair a b := (Nat.pair_unpair n).symm.trans (congrArg Nat.pairEquiv he)
    rwa [← en]

theorem componentProgram_partrec {Y : ForkSpans} (j : WalkingSpan)
    (f : forkProduct Y universal ⟶ universal) :
    Partrec (fun t : NumericalTuples.Tuple (Y.obj.obj j).dimension ×
      NumericalTuples.Tuple (universal.obj.obj j).dimension =>
        val (componentProgram j f) (Nat.pair (code _ t.1) (code _ t.2))) :=
  (EnumerableCarriers.val_partrec _).comp Computable.encode

theorem domain_enumerable {X Y : TupleSpans} (f : X ⟶ Y) :
    REPred (fun t : NumericalTuples.Tuple X.obj.dimension => (val (tupleCode.map f) (code _ t)).Dom) :=
  ((EnumerableCarriers.val_partrec _).comp Computable.encode).dom_re

theorem graph_domain {X Y : TupleSpans} (f : X ⟶ Y) (x : Point X.obj) :
    (val (tupleCode.map f) (code _ x.val)).Dom ↔ ∃ y : Point Y.obj, Graph f x y := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, rfl⟩ := EnumerableCarriers.val_target _ _ _ hv
    exact ⟨⟨w, hw⟩, hv⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, hy⟩

/-- A single diagram of tuple carriers represents all three component domains
and computations of the Turing morphism. -/
theorem tau_span : ∃ s : PartialMaps.Raw (forkProduct universal universal) universal,
    PartialMaps.ofSpan s = tau ∧ ∀ (j : WalkingSpan) (x : Point ((forkProduct universal universal).obj.obj j))
      (y : Point (universal.obj.obj j)), Graph ((evaluation j).map tau) x y ↔
        ∃ z : Point (s.apex.obj j), (s.l.app j).toFun z = x ∧ (s.r.app j).toFun z = y := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep tau
  refine ⟨s, hs, ?_⟩
  intro j x y
  rw [← hs]
  exact span_graph (⟨s.apex.obj j, s.l.app j, s.r.app j, by infer_instance, by trivial⟩ :
    PartialMaps.Raw ((evaluation j).obj (forkProduct universal universal)) ((evaluation j).obj universal)) x y

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
