/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalRegular
public import CategoricalEssentialIncompleteness.V46MillerTotalUnderlying
public import CategoricalEssentialIncompleteness.V46MillerCategoryRelative

/-! # Restriction idempotents on uniformly semidecidable carriers

The split object for A has base N and domain A. Its top restriction idempotent
therefore has support A, including for proper sentence carriers and the empty carrier.
The correspondence below reuses the existing split idempotents, uniform graphs, and
concrete regular image construction.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.CarrierIdempotents
attribute [instance 2000] Uniform.nativeRestriction
variable {P : Uniform.Family}

abbrev SplitCarrier (A : Total.Carrier P) : SplitObject (Uniform.Object P) := Total.inclusion.obj A

theorem base_eq (A : Total.Carrier P) : (SplitCarrier A).base=Uniform.N P := rfl
theorem domain_eq (A : Total.Carrier P) :
    (SplitCarrier A).domain=Uniform.setIdem (Uniform.N P) A.support A.enumerable := rfl

def support {A : Total.Carrier P} (c : Idem (SplitCarrier A)) : Set ℕ :=
  Total.support (Total.ofSplitIdem c)

theorem mem_value_idem {A : Total.Carrier P} (c : Idem (SplitCarrier A)) (x y : ℕ) :
    y∈c.hom.hom.val x ↔ x∈support c ∧ y=x :=
  Total.mem_val_idem (Total.ofSplitIdem c) x y

theorem value_idem {A : Total.Carrier P} (c : Idem (SplitCarrier A)) :
    c.hom.hom.val=Total.supportIdentity (support c) := by
  funext x
  apply Part.ext
  intro y
  exact (mem_value_idem c x y).trans (Total.mem_supportIdentity (support c) x y).symm

theorem support_enumerable {A : Total.Carrier P} (c : Idem (SplitCarrier A)) :
    Uniform.Enumerable P (·∈support c) := Total.support_re (Total.ofSplitIdem c)

theorem support_subset {A : Total.Carrier P} (c : Idem (SplitCarrier A)) :
    support c⊆A.support := Total.support_subset (Total.ofSplitIdem c)

theorem support_injective {A : Total.Carrier P} : Function.Injective (support (A := A)) := by
  intro c d h
  have he : Total.ofSplitIdem c=Total.ofSplitIdem d := Total.support_injective h
  exact congrArg Total.toSplitIdem he

theorem support_le_iff {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    c≤d ↔ support c⊆support d := Total.support_le_iff (Total.ofSplitIdem c) (Total.ofSplitIdem d)

def ofSet (A : Total.Carrier P) (B : Set ℕ) (hB : Uniform.Enumerable P (·∈B))
    (hBA : B⊆A.support) : Idem (SplitCarrier A) :=
  Total.toSplitIdem (Total.relativeIdem B hB hBA)

theorem support_ofSet (A : Total.Carrier P) (B : Set ℕ) (hB : Uniform.Enumerable P (·∈B))
    (hBA : B⊆A.support) : support (ofSet A B hB hBA)=B := Total.support_relativeIdem B hB hBA

theorem ofSet_support {A : Total.Carrier P} (c : Idem (SplitCarrier A)) :
    ofSet A (support c) (support_enumerable c) (support_subset c)=c :=
  support_injective (support_ofSet A _ _ _)

/-- This is an order isomorphism of the existing idempotents, with the uniform
enumerability and proper-carrier inclusion predicates. -/
def supportOrderIso (A : Total.Carrier P) : Idem (SplitCarrier A) ≃o
    {B : Set ℕ // Uniform.Enumerable P (·∈B) ∧ B⊆A.support} where
  toFun c := ⟨support c,support_enumerable c,support_subset c⟩
  invFun B := ofSet A B.val B.property.1 B.property.2
  left_inv := ofSet_support
  right_inv B := Subtype.ext (support_ofSet A B.val B.property.1 B.property.2)
  map_rel_iff' := (support_le_iff _ _).symm

theorem exists_unique_support (A : Total.Carrier P) (B : Set ℕ)
    (hB : Uniform.Enumerable P (·∈B)) (hBA : B⊆A.support) :
    ∃! c : Idem (SplitCarrier A),support c=B := by
  refine ⟨ofSet A B hB hBA,support_ofSet A B hB hBA,?_⟩
  intro c hc
  exact support_injective (hc.trans (support_ofSet A B hB hBA).symm)

theorem support_inf {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    support (c⊓d)=support c∩support d := Total.support_inf (Total.ofSplitIdem c) (Total.ofSplitIdem d)
theorem support_sup {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    support (c⊔d)=support c∪support d := Total.support_sup (Total.ofSplitIdem c) (Total.ofSplitIdem d)
theorem support_bot (A : Total.Carrier P) : support (⊥ : Idem (SplitCarrier A))=∅ :=
  Total.support_bot A
theorem support_top (A : Total.Carrier P) : support (⊤ : Idem (SplitCarrier A))=A.support :=
  Total.support_top A

theorem eq_top_iff {A : Total.Carrier P} (c : Idem (SplitCarrier A)) :
    c=⊤ ↔ support c=A.support := by
  constructor
  · rintro rfl
    exact support_top A
  · intro h
    exact support_injective (h.trans (support_top A).symm)

theorem join_eq_top_iff {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    c⊔d=⊤ ↔ support c∪support d=A.support := by rw [eq_top_iff,support_sup]

theorem join_ne_top_iff {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    c⊔d≠⊤ ↔ support c∪support d≠A.support := not_congr (join_eq_top_iff c d)

theorem disjoint_iff {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    c⊓d=⊥ ↔ Disjoint (support c) (support d) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  constructor
  · intro h
    have he := congrArg support h
    simpa only [support_inf,support_bot] using he
  · intro h
    apply support_injective
    rw [support_inf,support_bot]
    exact h

theorem complementary_iff {A : Total.Carrier P} (c d : Idem (SplitCarrier A)) :
    Complementary c d ↔ Disjoint (support c) (support d) ∧ support c∪support d=A.support :=
  ⟨fun h => ⟨(disjoint_iff c d).mp h.disjoint,(join_eq_top_iff c d).mp h.cover⟩,
    fun h => ⟨(disjoint_iff c d).mpr h.1,(join_eq_top_iff c d).mpr h.2⟩⟩

/-- The entire partial graph is used; no total extension outside A is chosen. -/
theorem support_pull {A B : Total.Carrier P} (f : A ⟶ B) (c : Idem (SplitCarrier B)) :
    support (Idem.pull (Total.inclusion.map f) c)=
      {x | ∃ y,y∈Total.val f x ∧ y∈support c} := Total.support_pull f (Total.ofSplitIdem c)

theorem support_pull_total {A B : Total.TotalCategory P} (f : A ⟶ B)
    (c : Idem (SplitCarrier B.obj)) (x : {n // n∈A.obj.support}) :
    x.val∈support (Idem.pull (Total.inclusion.map f.hom) c) ↔
      (Total.totalFunction f x).val∈support c := by
  rw [support_pull]
  constructor
  · rintro ⟨y,hy,hc⟩
    have he : y=(Total.totalFunction f x).val := Part.mem_unique hy (Total.totalFunction_mem f x)
    exact he ▸ hc
  · intro hc
    exact ⟨_,Total.totalFunction_mem f x,hc⟩

theorem total_inverseImage {A B : Total.TotalCategory P} (f : A ⟶ B)
    (c : Idem (SplitCarrier B.obj)) :
    (Subtype.val : {n // n∈A.obj.support} → ℕ) ⁻¹'
        support (Idem.pull (Total.inclusion.map f.hom) c)=
      (Total.totalFunction f) ⁻¹' ((Subtype.val : {n // n∈B.obj.support} → ℕ) ⁻¹' support c) := by
  ext x
  exact support_pull_total f c x

def finiteSup {A : Total.Carrier P} (L : List (Idem (SplitCarrier A))) : Idem (SplitCarrier A) :=
  L.foldr (·⊔·) ⊥

theorem support_finiteSup {A : Total.Carrier P} (L : List (Idem (SplitCarrier A))) :
    support (finiteSup L)={x | ∃ c∈L,x∈support c} := by
  induction L with
  | nil => simp only [finiteSup,List.foldr_nil,support_bot]; ext x; simp
  | cons c L ih =>
      change support (c⊔finiteSup L)={x | ∃ d∈c::L,x∈support d}
      rw [support_sup,ih]
      ext x
      simp only [Set.mem_union,Set.mem_ofPred_eq,List.mem_cons]
      constructor
      · exact fun h => h.elim (fun hc => ⟨c,Or.inl rfl,hc⟩) (fun ⟨d,hd,hx⟩ => ⟨d,Or.inr hd,hx⟩)
      · rintro ⟨d,rfl | hd,hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨d,hd,hx⟩

theorem pull_finiteSup {A B : Total.Carrier P} (f : A ⟶ B)
    (L : List (Idem (SplitCarrier B))) :
    Idem.pull (Total.inclusion.map f) (finiteSup L)=
      finiteSup (L.map (Idem.pull (Total.inclusion.map f))) := by
  apply support_injective
  rw [support_pull,support_finiteSup,support_finiteSup]
  ext x
  constructor
  · rintro ⟨y,hy,c,hc,hyc⟩
    exact ⟨Idem.pull (Total.inclusion.map f) c,List.mem_map.mpr ⟨c,hc,rfl⟩,
      (Set.ext_iff.mp (support_pull f c) x).mpr ⟨y,hy,hyc⟩⟩
  · rintro ⟨d,hd,hxd⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    obtain ⟨y,hy,hyc⟩ := (Set.ext_iff.mp (support_pull f c) x).mp hxd
    exact ⟨y,hy,c,hc,hyc⟩

theorem support_range {A B : Total.Carrier P} (f : A ⟶ B) :
    support (Ranges.range (Total.inclusion.map f))={y | ∃ x,y∈Total.val f x} := Total.support_range f

theorem image_subset {A B : Total.Carrier P} (f : A ⟶ B) :
    {y | ∃ x,y∈Total.val f x}⊆B.support := by
  rintro y ⟨x,hx⟩
  exact Total.val_target f x y hx

theorem range_ofSet {A B : Total.Carrier P} (f : A ⟶ B) :
    Ranges.range (Total.inclusion.map f)=ofSet B {y | ∃ x,y∈Total.val f x}
      (Total.val_represented f).image (image_subset f) := by
  apply support_injective
  rw [support_range,support_ofSet]

theorem imageObject_support {A B : Total.TotalCategory P} (f : A ⟶ B) :
    (Total.imageObject f).obj.support=support (Ranges.range (Total.inclusion.map f.hom)) := rfl

theorem range_totalFunction {A B : Total.TotalCategory P} (f : A ⟶ B) :
    support (Ranges.range (Total.inclusion.map f.hom))=
      Set.range (fun x : {n // n∈A.obj.support} => (Total.totalFunction f x).val) := by
  rw [support_range]
  ext y
  constructor
  · rintro ⟨x,hx⟩
    let xx : {n // n∈A.obj.support} := ⟨x,Total.val_source f.hom x y hx⟩
    exact ⟨xx,Part.mem_unique (Total.totalFunction_mem f xx) hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x.val,hx ▸ Total.totalFunction_mem f x⟩

theorem range_eq_top_iff {A B : Total.Carrier P} (f : A ⟶ B) :
    Ranges.range (Total.inclusion.map f)=⊤ ↔ {y | ∃ x,y∈Total.val f x}=B.support := by
  rw [eq_top_iff,support_range]

private theorem encodeFunction_nat (f : ℕ → Part ℕ) : Uniform.encodeFunction .nat .nat f=f := by
  funext n
  change (f n).map (fun y => y)=f n
  exact Part.map_id' (fun _ => rfl) (f n)

private theorem supportIdentity_domain (B : Set ℕ) (n : ℕ) :
    (Total.supportIdentity B n).Dom ↔ n∈B := by
  rw [Part.dom_iff_mem]
  simp only [Total.mem_supportIdentity,exists_eq_right]

/-- The singleton-family target has exactly the ordinary p-semidecidable subset supports,
expressed by their partial identities. -/
theorem singleton_enumerable_iff_recursive_identity (p : Bits) (B : Set ℕ) :
    Uniform.Enumerable (Uniform.Family.singleton p) (·∈B) ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (Total.supportIdentity B) := by
  constructor
  · intro hB
    have hr := (Uniform.identityOn (Uniform.N (Uniform.Family.singleton p)) B hB).represented
    have hc := (Uniform.singleton_represented_iff_recursiveIn p .nat .nat _).mp hr
    exact hc.of_eq (fun n => congrFun (encodeFunction_nat (Total.supportIdentity B)) n)
  · intro hB
    have hc : Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (Uniform.encodeFunction .nat .nat (Total.supportIdentity B)) :=
      hB.of_eq (fun n => (congrFun (encodeFunction_nat (Total.supportIdentity B)) n).symm)
    have hr := (Uniform.singleton_represented_iff_recursiveIn p .nat .nat _).mpr hc
    exact hr.domain.of_eq (supportIdentity_domain B)

theorem singleton_support_recursive (p : Bits) {A : Total.Carrier (Uniform.Family.singleton p)}
    (c : Idem (SplitCarrier A)) :
    Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
      (Total.supportIdentity (support c)) :=
  (singleton_enumerable_iff_recursive_identity p _).mp (support_enumerable c)

theorem singleton_exists_support_iff (p : Bits) (A : Total.Carrier (Uniform.Family.singleton p))
    (B : Set ℕ) : (∃ c : Idem (SplitCarrier A),support c=B) ↔
      B⊆A.support ∧ Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (Total.supportIdentity B) := by
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨support_subset c,singleton_support_recursive p c⟩
  · rintro ⟨hBA,hB⟩
    have he := (singleton_enumerable_iff_recursive_identity p B).mpr hB
    exact ⟨ofSet A B he hBA,support_ofSet A B he hBA⟩

end CategoricalEssentialIncompleteness.V46.Miller.CarrierIdempotents
