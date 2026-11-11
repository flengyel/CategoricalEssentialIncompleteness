/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable
public import CategoricalEssentialIncompleteness.OracleRestrictedCoding

/-! # One finite-table algorithm for every representation of a point

Uniform enumerability places the ordinary finite-table predicate before
the representation quantifier. Its graph presentation is proved equivalent
to the actual oracle-program presentation, including undefinedness. No
ordinary partial-recursive value extension is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleComputation (Ty)

/-- A family supplies the common oracle domain for one numerical index.
The point and singleton instances below construct nonemptiness directly. -/
structure Family where
  oracles : Set Bits
  nonempty : oracles.Nonempty

namespace Family

def ofPoint (z : Point) : Family :=
  ⟨Miller.representations z,Miller.representations_nonempty z⟩

def singleton (p : Bits) : Family := ⟨{p},⟨p,rfl⟩⟩

@[simp] theorem ofPoint_oracles (z : Point) : (ofPoint z).oracles = Miller.representations z := rfl
@[simp] theorem singleton_oracles (p : Bits) : (singleton p).oracles = {p} := rfl

end Family

def Enumerable (z : Family) {α : Type} [Primcodable α] (P : α → Prop) : Prop :=
  ∃ Q : α × List ℕ → Prop,REPred Q ∧
    (∀ x l l',l <+: l' → Q (x,l) → Q (x,l')) ∧
    ∀ p ∈ z.oracles,∀ x,P x ↔ ∃ k,Q (x,OracleProgram.numericalPrefix p k)

namespace Enumerable
variable {z : Family} {α β : Type} [Primcodable α] [Primcodable β]
variable {P R : α → Prop}

theorem of_eq (hP : Enumerable z P) (h : ∀ x,P x ↔ R x) : Enumerable z R := by
  obtain ⟨Q,hQ,hM,hP⟩ := hP
  exact ⟨Q,hQ,hM,fun p hp x => (h x).symm.trans (hP p hp x)⟩

theorem of_re (hP : REPred P) : Enumerable z P :=
  ⟨fun a => P a.1,REPred.comp Computable.fst hP,
    fun _ _ _ _ h => h,fun _ _ _ => ⟨fun h => ⟨0,h⟩,fun ⟨_,h⟩ => h⟩⟩

theorem comp {f : β → α} (hf : Computable f) (hP : Enumerable z P) :
    Enumerable z (fun x => P (f x)) := by
  obtain ⟨Q,hQ,hM,hP⟩ := hP
  exact ⟨fun a => Q (f a.1,a.2),
    REPred.comp (Computable.pair (hf.comp Computable.fst) Computable.snd) hQ,
    fun x l l' h => hM (f x) l l' h,fun p hp x => hP p hp (f x)⟩

theorem and (hP : Enumerable z P) (hR : Enumerable z R) : Enumerable z (fun x => P x ∧ R x) := by
  obtain ⟨Q,hQ,hMQ,hP⟩ := hP
  obtain ⟨T,hT,hMT,hR⟩ := hR
  refine ⟨fun a => Q a ∧ T a,hQ.and hT,
    fun x l l' h ⟨hq,ht⟩ => ⟨hMQ x l l' h hq,hMT x l l' h ht⟩,?_⟩
  intro p hp x
  change (P x ∧ R x) ↔ ∃ k,Q (x,OracleProgram.numericalPrefix p k) ∧
    T (x,OracleProgram.numericalPrefix p k)
  rw [hP p hp x,hR p hp x]
  constructor
  · rintro ⟨⟨k,hk⟩,⟨m,hm⟩⟩
    exact ⟨max k m,hMQ x _ _ (OracleProgram.numericalPrefix_le p (le_max_left _ _)) hk,
      hMT x _ _ (OracleProgram.numericalPrefix_le p (le_max_right _ _)) hm⟩
  · rintro ⟨k,hq,ht⟩
    exact ⟨⟨k,hq⟩,⟨k,ht⟩⟩

theorem or (hP : Enumerable z P) (hR : Enumerable z R) : Enumerable z (fun x => P x ∨ R x) := by
  obtain ⟨Q,hQ,hMQ,hP⟩ := hP
  obtain ⟨T,hT,hMT,hR⟩ := hR
  refine ⟨fun a => Q a ∨ T a,hQ.or hT,
    fun x l l' h => Or.imp (hMQ x l l' h) (hMT x l l' h),?_⟩
  intro p hp x
  simp only [hP p hp x,hR p hp x,exists_or]

theorem projection {P : α × β → Prop} (hP : Enumerable z P) :
    Enumerable z (fun x => ∃ y,P (x,y)) := by
  obtain ⟨Q,hQ,hM,hP⟩ := hP
  have hQ' : REPred (fun a : (α × List ℕ) × β => Q ((a.1.1,a.2),a.1.2)) :=
    REPred.comp (Computable.pair
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.snd.comp Computable.fst)) hQ
  refine ⟨fun a => ∃ y,Q ((a.1,y),a.2),hQ'.projection,?_,?_⟩
  · rintro x l l' h ⟨y,hy⟩
    exact ⟨y,hM (x,y) l l' h hy⟩
  · intro p hp x
    simp only [hP p hp]
    exact exists_comm
end Enumerable

section WitnessSearch
variable {α : Type} [Primcodable α] (Q : α × ℕ → Prop) (hQ : REPred Q)

private def witnessCode : OracleProgram.Code :=
  Classical.choose (OracleComputation.predicate_code hQ)

private theorem witnessCode_domain (a : α) (y : ℕ) :
    ((witnessCode Q hQ).eval (encode (a,y))).Dom ↔ Q (a,y) :=
  Classical.choose_spec (OracleComputation.predicate_code hQ) (a,y)

private def witnessStage (a : α) (t : ℕ) : Option ℕ :=
  ((witnessCode Q hQ).evaln (Nat.unpair t).2 (encode (a,(Nat.unpair t).1))).map
    (fun _ => (Nat.unpair t).1)

private theorem witnessStage_computable : Computable₂ (witnessStage Q hQ) := by
  have hx : Computable (fun a : α × ℕ => (Nat.unpair a.2).1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have ht : Computable (fun a : α × ℕ => (Nat.unpair a.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have he : Computable (fun a : α × ℕ =>
      (witnessCode Q hQ).evaln (Nat.unpair a.2).2 (encode (a.1,(Nat.unpair a.2).1))) :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (Computable.pair (Computable.pair ht (Computable.const (witnessCode Q hQ)))
        (Computable.encode.comp (Computable.pair Computable.fst hx)))
  exact Computable.option_map he (hx.comp Computable.fst).to₂

/-- Search runs over a paired output/fuel enumeration, so it does not
wait for a divergent smaller candidate output. -/
private def witnessSearch (a : α) : Part ℕ := Nat.rfindOpt (witnessStage Q hQ a)

private theorem witnessSearch_partrec : Partrec (witnessSearch Q hQ) :=
  Partrec.rfindOpt (witnessStage_computable Q hQ)

private theorem witnessSearch_sound (a : α) (y : ℕ) (hy : y ∈ witnessSearch Q hQ a) : Q (a,y) := by
  obtain ⟨t,ht⟩ := Nat.rfindOpt_spec hy
  cases he : (witnessCode Q hQ).evaln (Nat.unpair t).2 (encode (a,(Nat.unpair t).1)) with
  | none => simp only [witnessStage,he,Option.map_none,Option.mem_def,reduceCtorEq] at ht
  | some v =>
    have hty : y = (Nat.unpair t).1 := by
      simpa only [witnessStage,he,Option.map_some,Option.mem_def,Option.some.injEq,eq_comm] using ht
    subst y
    exact (witnessCode_domain Q hQ a _).mp (Nat.Partrec.Code.evaln_sound he).1

private theorem witnessSearch_domain (a : α) :
    (witnessSearch Q hQ a).Dom ↔ ∃ y,Q (a,y) := by
  constructor
  · intro h
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
    exact ⟨y,witnessSearch_sound Q hQ a y hy⟩
  · rintro ⟨y,hy⟩
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((witnessCode_domain Q hQ a y).mpr hy)
    obtain ⟨fuel,hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    change (witnessCode Q hQ).evaln fuel (encode (a,y)) = some v at hfuel
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Nat.pair y fuel,y,?_⟩
    simp only [witnessStage,Nat.unpair_pair,hfuel,Option.map_some,Option.mem_def]
end WitnessSearch

/-- An ordinary partial-recursive positive choice for an arbitrary
r.e. relation. No uniqueness condition is needed, including outside the
oracle representations used later. -/
@[no_expose] def positiveChoice {α : Type} [Primcodable α]
    (Q : α × ℕ → Prop) (hQ : REPred Q) : α → Part ℕ := witnessSearch Q hQ

theorem positiveChoice_partrec {α : Type} [Primcodable α]
    (Q : α × ℕ → Prop) (hQ : REPred Q) : Partrec (positiveChoice Q hQ) :=
  witnessSearch_partrec Q hQ

theorem positiveChoice_sound {α : Type} [Primcodable α]
    (Q : α × ℕ → Prop) (hQ : REPred Q) (a : α) (y : ℕ)
    (hy : y ∈ positiveChoice Q hQ a) : Q (a,y) := witnessSearch_sound Q hQ a y hy

theorem positiveChoice_domain {α : Type} [Primcodable α]
    (Q : α × ℕ → Prop) (hQ : REPred Q) (a : α) :
    (positiveChoice Q hQ a).Dom ↔ ∃ y,Q (a,y) := witnessSearch_domain Q hQ a

/-- Exactly one ordinary numerical index is supplied before every
representation of z, with the full partial-function graph equality. -/
def Numerical (z : Family) (f : ℕ → Part ℕ) : Prop :=
  ∃ e : ℕ,∀ p ∈ z.oracles,∀ n y,
    y ∈ f n ↔ y ∈ OracleProgram.numberedEval e p n

theorem numerical_graph_enumerable {z : Family} {f : ℕ → Part ℕ} (hf : Numerical z f) :
    Enumerable z (fun a : ℕ × ℕ => a.2 ∈ f a.1) := by
  obtain ⟨e,he⟩ := hf
  let c := Denumerable.ofNat OracleProgram.Code e
  have hfinite : Partrec (fun a : List ℕ × ℕ => OracleProgram.finiteEval c a.1 a.2) :=
    OracleProgram.finiteEval_partrec.comp
      (Computable.pair (Computable.pair (Computable.const c) Computable.fst) Computable.snd)
  have hgraph := OracleComputation.partrecGraph hfinite
  refine ⟨fun a => a.1.2 ∈ OracleProgram.finiteEval c a.2 a.1.1,
    REPred.comp (Computable.pair
      (Computable.pair Computable.snd (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)) hgraph,?_,?_⟩
  · intro a l l' hll' hy
    exact OracleProgram.finiteEval_mono c hll' a.1 a.2 hy
  · intro p hp a
    exact (he p hp a.1 a.2).trans (OracleProgram.eval_graph c p a.1 a.2)

theorem numerical_of_graph_enumerable {z : Family} {f : ℕ → Part ℕ}
    (hf : Enumerable z (fun a : ℕ × ℕ => a.2 ∈ f a.1)) : Numerical z f := by
  obtain ⟨Q,hQ,hM,hgraph⟩ := hf
  let R : (List ℕ × ℕ) × ℕ → Prop := fun a => Q ((a.1.2,a.2),a.1.1)
  have hR : REPred R := REPred.comp (Computable.pair
    (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
    (Computable.fst.comp Computable.fst)) hQ
  let F : List ℕ × ℕ → Part ℕ := witnessSearch R hR
  have hF : Partrec F := witnessSearch_partrec R hR
  have hs (p : Bits) (hp : p ∈ z.oracles) (k n y : ℕ)
      (hy : y ∈ F (OracleProgram.numericalPrefix p k,n)) : y ∈ f n :=
    (hgraph p hp (n,y)).mpr ⟨k,witnessSearch_sound R hR _ y hy⟩
  have hcoh (p : Bits) (hp : p ∈ z.oracles) (n i j a b : ℕ)
      (ha : a ∈ F (OracleProgram.numericalPrefix p i,n))
      (hb : b ∈ F (OracleProgram.numericalPrefix p j,n)) : a = b :=
    Part.mem_unique (hs p hp i n a ha) (hs p hp j n b hb)
  refine ⟨encode (OracleProgram.ofTable F hF),?_⟩
  intro p hp n y
  rw [OracleProgram.numberedEval_encode,OracleProgram.ofTable_graph_at F hF p n (hcoh p hp n)]
  constructor
  · intro hy
    obtain ⟨k,hk⟩ := (hgraph p hp (n,y)).mp hy
    have hd : (F (OracleProgram.numericalPrefix p k,n)).Dom :=
      (witnessSearch_domain R hR _).mpr ⟨y,hk⟩
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hd
    have he : v = y := Part.mem_unique (hs p hp k n v hv) hy
    exact ⟨k,he ▸ hv⟩
  · rintro ⟨k,hk⟩
    exact hs p hp k n y hk

theorem numerical_iff_graph_enumerable (z : Family) (f : ℕ → Part ℕ) :
    Numerical z f ↔ Enumerable z (fun a : ℕ × ℕ => a.2 ∈ f a.1) :=
  ⟨numerical_graph_enumerable,numerical_of_graph_enumerable⟩

/-- The prescribed manuscript realization property, with original formal
objects and their already proved recursive numerical bijections. -/
def Represented (z : Family) (X Y : Ty) (f : X.carrier → Part Y.carrier) : Prop :=
  ∃ e : ℕ,∀ p ∈ z.oracles,∀ x y,
    y ∈ f x ↔ Y.toNat y ∈ OracleProgram.numberedEval e p (X.toNat x)

def encodeFunction (X Y : Ty) (f : X.carrier → Part Y.carrier) : ℕ → Part ℕ :=
  fun n => (f (X.fromNat n)).map Y.toNat

theorem encodeFunction_graph (X Y : Ty) (f : X.carrier → Part Y.carrier) (n m : ℕ) :
    m ∈ encodeFunction X Y f n ↔ Y.fromNat m ∈ f (X.fromNat n) := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := (Part.mem_map_iff _).mp h
    have hy' : Y.fromNat m = y := by rw [← he,Y.from_toNat]
    exact hy'.symm ▸ hy
  · intro h
    exact (Part.mem_map_iff _).mpr ⟨Y.fromNat m,h,Y.to_fromNat m⟩

theorem represented_iff_numerical (z : Family) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented z X Y f ↔ Numerical z (encodeFunction X Y f) := by
  constructor
  · rintro ⟨e,he⟩
    refine ⟨e,?_⟩
    intro p hp n m
    exact (encodeFunction_graph X Y f n m).trans (by
      simpa only [Y.to_fromNat,X.to_fromNat] using he p hp (X.fromNat n) (Y.fromNat m))
  · rintro ⟨e,he⟩
    refine ⟨e,?_⟩
    intro p hp x y
    have h := (encodeFunction_graph X Y f (X.toNat x) (Y.toNat y)).symm.trans
      (he p hp (X.toNat x) (Y.toNat y))
    simpa only [X.from_toNat,Y.from_toNat] using h

theorem represented_iff_graph_enumerable (z : Family) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented z X Y f ↔ Enumerable z (fun a : X.carrier × Y.carrier => a.2 ∈ f a.1) := by
  constructor
  · intro hf
    have hn := numerical_graph_enumerable ((represented_iff_numerical z X Y f).mp hf)
    have hc := Enumerable.comp (Computable.pair
      (X.toNat_computable.comp Computable.fst) (Y.toNat_computable.comp Computable.snd)) hn
    exact hc.of_eq (fun a => by simp only [encodeFunction_graph,X.from_toNat,Y.from_toNat])
  · intro hf
    apply (represented_iff_numerical z X Y f).mpr
    apply numerical_of_graph_enumerable
    have hc := Enumerable.comp (Computable.pair
      (X.fromNat_computable.comp Computable.fst) (Y.fromNat_computable.comp Computable.snd)) hf
    exact hc.of_eq (fun a => (encodeFunction_graph X Y f a.1 a.2).symm)

namespace Represented
variable {z : Family} {X Y Z : Ty}

theorem of_eq {f g : X.carrier → Part Y.carrier} (hf : Represented z X Y f)
    (h : ∀ x,f x = g x) : Represented z X Y g := (funext h) ▸ hf

theorem of_partrec {f : X.carrier → Part Y.carrier} (hf : Partrec f) : Represented z X Y f :=
  (represented_iff_graph_enumerable z X Y f).mpr
    (Enumerable.of_re (OracleComputation.partrecGraph hf))

theorem comp {f : X.carrier → Part Y.carrier} {g : Y.carrier → Part Z.carrier}
    (hf : Represented z X Y f) (hg : Represented z Y Z g) :
    Represented z X Z (fun x => (f x).bind g) := by
  have ef := (represented_iff_graph_enumerable z X Y f).mp hf
  have eg := (represented_iff_graph_enumerable z Y Z g).mp hg
  have hp := (Enumerable.comp (Computable.pair (Computable.fst.comp Computable.fst)
    Computable.snd) ef).and
    (Enumerable.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)) eg)
  apply (represented_iff_graph_enumerable z X Z _).mpr
  exact hp.projection.of_eq (fun a => by
    change (∃ y,y ∈ f a.1 ∧ a.2 ∈ g y) ↔ a.2 ∈ (f a.1).bind g
    exact Part.mem_bind_iff.symm)

theorem domain {f : X.carrier → Part Y.carrier} (hf : Represented z X Y f) :
    Enumerable z (fun x => (f x).Dom) :=
  ((represented_iff_graph_enumerable z X Y f).mp hf).projection.of_eq
    (fun x => by
      change (∃ y,y ∈ f x) ↔ (f x).Dom
      exact Part.dom_iff_mem.symm)

theorem image {f : X.carrier → Part Y.carrier} (hf : Represented z X Y f) :
    Enumerable z (fun y => ∃ x,y ∈ f x) :=
  (Enumerable.comp (Computable.pair Computable.snd Computable.fst)
    ((represented_iff_graph_enumerable z X Y f).mp hf)).projection

theorem identityOn (X : Ty) (A : Set X.carrier) (hA : Enumerable z (· ∈ A)) :
    Represented z X X (fun x => Part.assert (x ∈ A) (fun _ => Part.some x)) := by
  have heq : REPred (fun a : X.carrier × X.carrier => a.2 = a.1) :=
    (Primrec.eq.comp Primrec.snd Primrec.fst).computablePred.to_re
  apply (represented_iff_graph_enumerable z X X _).mpr
  exact ((Enumerable.comp Computable.fst hA).and (Enumerable.of_re heq)).of_eq
    (fun _ => by simp only [Part.mem_assert_iff,Part.mem_some_iff,exists_prop])

theorem pair {W X Y : Ty} {f : W.carrier → Part X.carrier} {g : W.carrier → Part Y.carrier}
    (hf : Represented z W X f) (hg : Represented z W Y g) :
    Represented z W (.product X Y) (fun w => (f w).bind (fun x => (g w).map (Prod.mk x))) := by
  have ef := (represented_iff_graph_enumerable z W X f).mp hf
  have eg := (represented_iff_graph_enumerable z W Y g).mp hg
  have hp := (Enumerable.comp (Computable.pair Computable.fst
    (Computable.fst.comp Computable.snd)) ef).and
    (Enumerable.comp (Computable.pair Computable.fst (Computable.snd.comp Computable.snd)) eg)
  apply (represented_iff_graph_enumerable z W (.product X Y) _).mpr
  exact hp.of_eq (fun a => (OracleComputation.Restricted.mem_rawPair f g a.1 a.2.1 a.2.2).symm)

theorem sum {X Y Z : Ty} {f : X.carrier → Part Z.carrier} {g : Y.carrier → Part Z.carrier}
    (hf : Represented z X Z f) (hg : Represented z Y Z g) :
    Represented z (.coproduct X Y) Z (Sum.elim f g) := by
  have ef := (represented_iff_graph_enumerable z X Z f).mp hf
  have eg := (represented_iff_graph_enumerable z Y Z g).mp hg
  have hl : Enumerable z (fun a : ((X.carrier ⊕ Y.carrier) × Z.carrier) × X.carrier =>
      a.1.1 = .inl a.2 ∧ a.1.2 ∈ f a.2) :=
    (Enumerable.of_re ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.sumInl.comp Primrec.snd)).computablePred.to_re)).and
      (Enumerable.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)) ef)
  have hr : Enumerable z (fun a : ((X.carrier ⊕ Y.carrier) × Z.carrier) × Y.carrier =>
      a.1.1 = .inr a.2 ∧ a.1.2 ∈ g a.2) :=
    (Enumerable.of_re ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.sumInr.comp Primrec.snd)).computablePred.to_re)).and
      (Enumerable.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)) eg)
  apply (represented_iff_graph_enumerable z (.coproduct X Y) Z _).mpr
  exact (hl.projection.or hr.projection).of_eq (fun a => by
    rcases a with ⟨s,y⟩
    cases s <;> simp)
end Represented

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
