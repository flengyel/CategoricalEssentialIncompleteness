/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableUnderlying
import CategoricalEssentialIncompleteness.ClassicalSplitEquivalence

/-! # Finite-dimensional c.e. carriers with actual tuple-valued maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open Encodable
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalTuples

/-- The empty tuple is literally a unit value, the one-tuple a natural
number, and higher tuples iterated Cartesian products. -/
def Tuple : ℕ → Type
  | 0 => Unit
  | 1 => ℕ
  | n + 2 => ℕ × Tuple (n + 1)

instance tuplePrimcodable : (m : ℕ) → Primcodable (Tuple m)
  | 0 => inferInstanceAs (Primcodable Unit)
  | 1 => inferInstanceAs (Primcodable ℕ)
  | n + 2 =>
    letI := tuplePrimcodable (n + 1)
    inferInstanceAs (Primcodable (ℕ × Tuple (n + 1)))

/-- These are the chosen numerical coordinates: zero for the empty
tuple, identity in dimension one and numerical pairing above it. -/
def code (m : ℕ) : Tuple m → ℕ := encode

@[simp] theorem code_zero (x : Tuple 0) : code 0 x = 0 := by cases x; rfl
@[simp] theorem code_one (x : ℕ) : code 1 x = x := rfl
@[simp] theorem code_succ_succ (n : ℕ) (x : ℕ × Tuple (n + 1)) :
    code (n + 2) x = Nat.pair x.1 (code (n + 1) x.2) := rfl

theorem code_injective (m : ℕ) : Function.Injective (code m) := encode_injective

def codeSet (m : ℕ) : Set ℕ := Set.range (code m)

theorem codeSet_recursive (m : ℕ) : ComputablePred (· ∈ codeSet m) :=
  (Primcodable.mem_range_encode (α := Tuple m)).computablePred

@[simp] theorem codeSet_zero : codeSet 0 = {0} := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hn
    exact ⟨(), by simpa using hn.symm⟩

@[simp] theorem codeSet_one : codeSet 1 = Set.univ := by
  ext n
  exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨n, rfl⟩⟩

theorem codeSet_zero_proper : codeSet 0 ≠ Set.univ := by
  intro h
  have : (1 : ℕ) ∈ codeSet 0 := h.symm ▸ Set.mem_univ 1
  simp at this

/-- Guarded decoding fails outside the image; in particular it fails at
every positive input in dimension zero. -/
def decodeTuple (m : ℕ) (n : ℕ) : Part (Tuple m) := Part.ofOption (decode₂ (Tuple m) n)

theorem decodeTuple_partrec (m : ℕ) : Partrec (decodeTuple m) :=
  Computable.ofOption Primrec.decode₂.to_comp

@[simp] theorem mem_decodeTuple (m : ℕ) (n : ℕ) (x : Tuple m) :
    x ∈ decodeTuple m n ↔ code m x = n := by
  unfold decodeTuple
  rw [Part.mem_ofOption]
  exact Encodable.mem_decode₂

@[simp] theorem decodeTuple_code (m : ℕ) (x : Tuple m) :
    decodeTuple m (code m x) = Part.some x :=
  Part.eq_some_iff.mpr ((mem_decodeTuple m _ x).mpr rfl)

@[simp] theorem decodeTuple_zero_succ (n : ℕ) : decodeTuple 0 (n + 1) = Part.none := by
  apply Part.ext
  intro x
  simp

theorem decodeTuple_domain (m n : ℕ) : (decodeTuple m n).Dom ↔ n ∈ codeSet m := by
  rw [Part.dom_iff_mem]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, (mem_decodeTuple m n x).mp hx⟩,
    fun ⟨x, hx⟩ => ⟨x, (mem_decodeTuple m n x).mpr hx⟩⟩

/-- An object is a dimension and an actual c.e. subset of that tuple
space. No numerical carrier is substituted for its tuple carrier. -/
structure Object where
  dimension : ℕ
  support : Set (Tuple dimension)
  enumerable : REPred (· ∈ support)

abbrev Point (C : Object) := {x : Tuple C.dimension // x ∈ C.support}

/-- A morphism is a function on the actual carriers. Its program can be
partial elsewhere, but computes that function on every carrier input. -/
structure Map (C D : Object) where
  toFun : Point C → Point D
  represented : ∃ p : Tuple C.dimension → Part (Tuple D.dimension),
    Partrec p ∧ ∀ x : Point C, p x.val = Part.some (toFun x).val

@[ext] theorem Map.ext {C D : Object} {f g : Map C D} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Map.identity (C : Object) : Map C C :=
  ⟨id, ⟨Part.some, Partrec.some, fun _ => rfl⟩⟩

def Map.composition {C D E : Object} (f : Map C D) (g : Map D E) : Map C E where
  toFun := g.toFun ∘ f.toFun
  represented := by
    obtain ⟨p, hp, hf⟩ := f.represented
    obtain ⟨q, hq, hg⟩ := g.represented
    exact ⟨fun x => (p x).bind q, hp.bind (hq.comp Computable.snd).to₂, by
      intro x
      change (p x.val).bind q = Part.some (g.toFun (f.toFun x)).val
      rw [hf x, Part.bind_some, hg (f.toFun x)]⟩

instance : Category Object where
  Hom := Map
  id := Map.identity
  comp := Map.composition
  id_comp _f := Map.ext rfl
  comp_id _f := Map.ext rfl
  assoc _f _g _h := Map.ext rfl

@[simp] theorem identity_apply (C : Object) (x : Point C) :
    (𝟙 C : C ⟶ C).toFun x = x := rfl

@[simp] theorem composition_apply {C D E : Object} (f : C ⟶ D) (g : D ⟶ E) (x : Point C) :
    (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

/-- Tuple-function equality is exactly categorical arrow equality. -/
theorem map_eq_iff {C D : Object} (f g : C ⟶ D) :
    f = g ↔ ∀ x : Point C, f.toFun x = g.toFun x :=
  ⟨fun h => h ▸ fun _ => rfl, fun h => Map.ext (funext h)⟩

/-- The manuscript's zero-dimensional singleton, with its literal unit
carrier, is an actual terminal object of the tuple-function category. -/
def terminalObject : Object := ⟨0, Set.univ, REPred.const True⟩

def terminalMap (C : Object) : C ⟶ terminalObject where
  toFun _ := ⟨(), Set.mem_univ _⟩
  represented := ⟨fun _ => Part.some (), Computable.const (), fun _ => rfl⟩

def terminalIsTerminal : CategoryTheory.Limits.IsTerminal (C := Object) terminalObject :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom terminalMap (by
    intro C f
    apply Map.ext
    funext x
    apply Subtype.ext
    exact Subsingleton.elim (α := Unit) _ _)

/-- The numerical support is the actual coding image of the tuple set. -/
def codedSupport (C : Object) : Set ℕ := code C.dimension '' C.support

theorem codedSupport_re (C : Object) : REPred (· ∈ codedSupport C) := by
  have he : ComputablePred (fun z : ℕ × Tuple C.dimension => code C.dimension z.2 = z.1) :=
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst).computablePred
  exact (he.to_re.and (REPred.comp Computable.snd C.enumerable)).projection.of_eq
    (fun _ => by simp [codedSupport, Set.mem_image, and_comm])

@[simp] theorem code_mem_codedSupport (C : Object) (x : Tuple C.dimension) :
    code C.dimension x ∈ codedSupport C ↔ x ∈ C.support := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (code_injective C.dimension he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

@[simp] theorem codedSupport_terminalObject : codedSupport terminalObject = {0} := by
  ext n
  constructor
  · rintro ⟨x, _, rfl⟩
    exact code_zero x
  · intro hn
    exact ⟨(), Set.mem_univ _, by change 0 = n; exact hn.symm⟩

def codedCarrier (C : Object) : EnumerableCarriers.Carrier := ⟨codedSupport C, codedSupport_re C⟩
def codedObject (C : Object) : EnumerableCarriers.Total := ⟨codedCarrier C⟩

/-- Coding and guarded decoding are inverse on the actual carrier. -/
def pointEquiv (C : Object) : Point C ≃ {n // n ∈ codedSupport C} where
  toFun x := ⟨code C.dimension x.val, x.val, x.property, rfl⟩
  invFun z := ⟨Classical.choose z.property, (Classical.choose_spec z.property).1⟩
  left_inv x := by
    apply Subtype.ext
    exact code_injective C.dimension (Classical.choose_spec
      (show code C.dimension x.val ∈ codedSupport C from ⟨x.val, x.property, rfl⟩)).2
  right_inv z := Subtype.ext (Classical.choose_spec z.property).2

@[simp] theorem pointEquiv_val (C : Object) (x : Point C) :
    (pointEquiv C x).val = code C.dimension x.val := rfl

@[simp] theorem pointEquiv_symm_code (C : Object) (z : {n // n ∈ codedSupport C}) :
    code C.dimension ((pointEquiv C).symm z).val = z.val :=
  congrArg Subtype.val ((pointEquiv C).apply_symm_apply z)

/-- The chosen tuple program is only an implementation witness; arrow
equality and category composition are equality/composition of functions. -/
def Map.program {C D : Object} (f : C ⟶ D) : Tuple C.dimension → Part (Tuple D.dimension) :=
  Classical.choose f.represented

theorem Map.program_partrec {C D : Object} (f : C ⟶ D) : Partrec f.program :=
  (Classical.choose_spec f.represented).1

@[simp] theorem Map.program_apply {C D : Object} (f : C ⟶ D) (x : Point C) :
    f.program x.val = Part.some (f.toFun x).val := (Classical.choose_spec f.represented).2 x

/-- Decode, run the tuple-valued program, and encode its result. -/
def Map.codeProgram {C D : Object} (f : C ⟶ D) : ℕ → Part ℕ :=
  fun n => (decodeTuple C.dimension n).bind (fun x => (f.program x).map (code D.dimension))

theorem Map.codeProgram_partrec {C D : Object} (f : C ⟶ D) : Partrec f.codeProgram := by
  exact (decodeTuple_partrec C.dimension).bind
    ((f.program_partrec.map (Computable.encode.comp Computable.snd).to₂).comp
      Computable.snd).to₂

@[simp] theorem Map.codeProgram_apply {C D : Object} (f : C ⟶ D) (x : Point C) :
    f.codeProgram (code C.dimension x.val) = Part.some (code D.dimension (f.toFun x).val) := by
  change (decodeTuple C.dimension (code C.dimension x.val)).bind
    (fun a => (f.program a).map (code D.dimension)) = _
  rw [decodeTuple_code, Part.bind_some, f.program_apply x]
  rfl

/-- The support semidecision makes the numerical domain exactly the
coded source carrier, even if the original program halts elsewhere. -/
def Map.restrictedProgram {C D : Object} (f : C ⟶ D) : ℕ → Part ℕ :=
  fun n => (supportIdentity (codedSupport C) n).bind f.codeProgram

theorem Map.restrictedProgram_partrec {C D : Object} (f : C ⟶ D) : Partrec f.restrictedProgram :=
  (supportIdentity_partrec _ (codedSupport_re C)).bind
    (f.codeProgram_partrec.comp Computable.snd).to₂

@[simp] theorem Map.restrictedProgram_apply {C D : Object} (f : C ⟶ D) (x : Point C) :
    f.restrictedProgram (code C.dimension x.val) =
      Part.some (code D.dimension (f.toFun x).val) := by
  have hi : supportIdentity (codedSupport C) (code C.dimension x.val) =
      Part.some (code C.dimension x.val) := Part.eq_some_iff.mpr
    ((mem_supportIdentity _ _ _).mpr ⟨⟨x.val, x.property, rfl⟩, rfl⟩)
  simp only [Map.restrictedProgram, hi, Part.bind_some, Map.codeProgram_apply]

theorem Map.restrictedProgram_graph {C D : Object} (f : C ⟶ D) (n k : ℕ) :
    k ∈ f.restrictedProgram n ↔ ∃ x : Point C,
      code C.dimension x.val = n ∧ code D.dimension (f.toFun x).val = k := by
  constructor
  · intro h
    obtain ⟨z, hz, hk⟩ := Part.mem_bind_iff.mp h
    obtain ⟨hn, he⟩ := (mem_supportIdentity _ _ _).mp hz
    subst z
    obtain ⟨x, hx, rfl⟩ := hn
    rw [f.codeProgram_apply ⟨x, hx⟩] at hk
    exact ⟨⟨x, hx⟩, rfl, (Part.mem_some_iff.mp hk).symm⟩
  · rintro ⟨x, rfl, rfl⟩
    rw [f.restrictedProgram_apply]
    exact Part.mem_some _

/-- The numerical function has the exact coded source as domain. -/
theorem Map.restrictedProgram_domain {C D : Object} (f : C ⟶ D) (n : ℕ) :
    (f.restrictedProgram n).Dom ↔ n ∈ codedSupport C := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨x, he, _⟩ := (f.restrictedProgram_graph n k).mp hk
    exact he ▸ (code_mem_codedSupport C x.val).mpr x.property
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (f.restrictedProgram_graph _ _).mpr ⟨⟨x, hx⟩, rfl, rfl⟩⟩

def comparisonMap {C D : Object} (f : C ⟶ D) : codedObject C ⟶ codedObject D :=
  ⟨EnumerableCarriers.arrow f.restrictedProgram f.restrictedProgram_partrec
    (by
      intro n k h
      obtain ⟨x, he, _⟩ := (f.restrictedProgram_graph n k).mp h
      exact he ▸ (code_mem_codedSupport C x.val).mpr x.property)
    (by
      intro n k h
      obtain ⟨x, _, he⟩ := (f.restrictedProgram_graph n k).mp h
      exact he ▸ (code_mem_codedSupport D (f.toFun x).val).mpr (f.toFun x).property),
    (EnumerableCarriers.total_iff _).mpr (fun n hn => (f.restrictedProgram_domain n).mpr hn)⟩

@[simp] theorem comparisonMap_graph {C D : Object} (f : C ⟶ D) (n k : ℕ) :
    k ∈ EnumerableCarriers.val (comparisonMap f).hom n ↔ ∃ x : Point C,
      code C.dimension x.val = n ∧ code D.dimension (f.toFun x).val = k :=
  f.restrictedProgram_graph n k

@[simp] theorem comparisonMap_function {C D : Object} (f : C ⟶ D) (x : Point C) :
    EnumerableCarriers.totalFunction (comparisonMap f) (pointEquiv C x) =
      pointEquiv D (f.toFun x) := by
  apply Subtype.ext
  exact Part.mem_unique (EnumerableCarriers.totalFunction_mem _ _) (Part.eq_some_iff.mp
    (f.restrictedProgram_apply x))

def comparison : Object ⥤ EnumerableCarriers.Total where
  obj := codedObject
  map := comparisonMap
  map_id C := by
    apply WideSubcategory.hom_ext
    apply EnumerableCarriers.val_ext_on_source
    intro n hn
    obtain ⟨x, hx, rfl⟩ := hn
    rw [show EnumerableCarriers.val (comparisonMap (𝟙 C)).hom
      (code C.dimension x) =
      Part.some (code C.dimension x) from (𝟙 C : C ⟶ C).restrictedProgram_apply ⟨x, hx⟩]
    symm
    exact Part.eq_some_iff.mpr ((mem_supportIdentity _ _ _).mpr
      ⟨⟨x, hx, rfl⟩, rfl⟩)
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply EnumerableCarriers.val_ext_on_source
    intro n hn
    obtain ⟨x, hx, rfl⟩ := hn
    change (f ≫ g).restrictedProgram (code _ x) =
      (f.restrictedProgram (code _ x)).bind g.restrictedProgram
    rw [(f ≫ g).restrictedProgram_apply ⟨x, hx⟩,
      f.restrictedProgram_apply ⟨x, hx⟩, Part.bind_some,
      g.restrictedProgram_apply (f.toFun ⟨x, hx⟩)]
    rfl

instance comparison_faithful : comparison.Faithful where
  map_injective {C D} f g h := by
    apply Map.ext
    funext x
    apply Subtype.ext
    apply code_injective D.dimension
    have he := congrArg (fun k => EnumerableCarriers.totalFunction k (pointEquiv C x)) h
    change EnumerableCarriers.totalFunction (comparisonMap f) (pointEquiv C x) =
      EnumerableCarriers.totalFunction (comparisonMap g) (pointEquiv C x) at he
    rw [comparisonMap_function, comparisonMap_function] at he
    exact congrArg Subtype.val he

/-- Recover an actual tuple function from any total numerical arrow between
coded carriers, using the proved inverse coding on its output. -/
def recoverMap {C D : Object} (g : codedObject C ⟶ codedObject D) : C ⟶ D where
  toFun x := (pointEquiv D).symm (EnumerableCarriers.totalFunction g (pointEquiv C x))
  represented := by
    refine ⟨fun x =>
      (EnumerableCarriers.val g.hom (code C.dimension x)).bind (decodeTuple D.dimension),
      ((EnumerableCarriers.val_partrec g.hom).comp Computable.encode).bind
        ((decodeTuple_partrec D.dimension).comp Computable.snd).to₂, ?_⟩
    intro x
    change (EnumerableCarriers.val g.hom (code C.dimension x.val)).bind
      (decodeTuple D.dimension) = Part.some
        ((pointEquiv D).symm (EnumerableCarriers.totalFunction g (pointEquiv C x))).val
    have hv : EnumerableCarriers.val g.hom (code C.dimension x.val) =
        Part.some (EnumerableCarriers.totalFunction g (pointEquiv C x)).val :=
      Part.eq_some_iff.mpr (EnumerableCarriers.totalFunction_mem g (pointEquiv C x))
    rw [hv, Part.bind_some,
      ← pointEquiv_symm_code D (EnumerableCarriers.totalFunction g (pointEquiv C x)),
      decodeTuple_code]

/-- Fullness is proved by decoding the function and constructing its
partial-recursive tuple-valued realization, rather than postulated. -/
theorem comparison_recoverMap {C D : Object} (g : codedObject C ⟶ codedObject D) :
    comparison.map (recoverMap g) = g := by
  apply WideSubcategory.hom_ext
  apply EnumerableCarriers.val_ext_on_source
  intro n hn
  obtain ⟨x, hx, rfl⟩ := hn
  change (recoverMap g).restrictedProgram (code C.dimension x) =
    EnumerableCarriers.val g.hom (code C.dimension x)
  rw [(recoverMap g).restrictedProgram_apply ⟨x, hx⟩]
  change Part.some (code D.dimension ((pointEquiv D).symm
    (EnumerableCarriers.totalFunction g (pointEquiv C ⟨x, hx⟩))).val) = _
  rw [pointEquiv_symm_code]
  exact (Part.eq_some_iff.mpr
    (EnumerableCarriers.totalFunction_mem g (pointEquiv C ⟨x, hx⟩))).symm

instance comparison_full : comparison.Full where
  map_surjective g := ⟨recoverMap g, comparison_recoverMap g⟩

/-- Every c.e. numerical carrier occurs in dimension one. -/
def unary (X : EnumerableCarriers.Total) : Object :=
  ⟨1, X.obj.support, X.obj.enumerable⟩

@[simp] theorem codedSupport_unary (X : EnumerableCarriers.Total) :
    codedSupport (unary X) = X.obj.support := by
  ext n
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hn
    exact ⟨n, hn, rfl⟩

@[simp] theorem codedObject_unary (X : EnumerableCarriers.Total) :
    codedObject (unary X) = X := by
  apply WideSubcategory.ext
  change (⟨codedSupport (unary X), codedSupport_re (unary X)⟩ : EnumerableCarriers.Carrier) =
    X.obj
  rcases X with ⟨⟨S, hS⟩⟩
  change (⟨codedSupport (unary ⟨⟨S, hS⟩⟩), _⟩ : EnumerableCarriers.Carrier) = ⟨S, hS⟩
  congr 1
  exact codedSupport_unary (⟨⟨S, hS⟩⟩ : EnumerableCarriers.Total)

instance comparison_essSurj : comparison.EssSurj where
  mem_essImage X := ⟨unary X, ⟨eqToIso (codedObject_unary X)⟩⟩

instance comparison_isEquivalence : comparison.IsEquivalence := {}

/-- The actual finite-tuple function category is equivalent to the
existing total category of c.e. numerical carriers. -/
def equivalence : Object ≌ EnumerableCarriers.Total := comparison.asEquivalence

/-- Hence it presents every total object of the classical restriction
splitting, not only the included numerical base object. -/
def classicalTotalEquivalence :
    Object ≌ WideSubcategory (isTotal (C := SplitObject ClassicalPrograms.Rec)) :=
  equivalence.trans EnumerableCarriers.inclusion_rst.totalEquivalence

end CategoricalEssentialIncompleteness.V46.NumericalTuples
