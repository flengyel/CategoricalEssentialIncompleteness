/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapRanges
public import CategoricalEssentialIncompleteness.V46LogicalComparison

/-! # Sentence theories interpreted in the generic partial-map category -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u₂} [Category.{v₂} D] [Regular D]

/-- A total splitting inclusion of a conclusion range is a subobject
of every ordinary monomorphism through which the conclusions factor. -/
theorem theory_subobject_factorization {P T S : Par D}
    (c : P ⟶ S) (hc : isTotal c) (m : T ⟶ S) (hm : isTotal m) (r : S ⟶ T)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = (Ranges.range c).hom)
    {V : D} (v : V ⟶ S.obj) [Mono v] (k : P.obj ⟶ V)
    (hfac : k ≫ v = totalValue c hc) :
    ∃ w : T.obj ⟶ V, w ≫ v = totalValue m hm := by
  let VP : Par D := ⟨V⟩
  let k' : P ⟶ VP := ofTotal k
  let v' : VP ⟶ S := ofTotal v
  let q : S ⟶ VP := inverseMono v
  have hfac' : c = k' ≫ v' := by
    dsimp [k', v']
    rw [← ofTotal_comp, hfac, ofTotal_totalValue]
  obtain ⟨w, hw, hwv⟩ := theory_inclusion_factors c m r hm hmr hrm
    k' v' q (ofTotal_total v) (total_inverseMono v) (inverseMono_total v) hfac'
  refine ⟨totalValue w hw, ?_⟩
  apply ofTotal_injective (X := T) (Y := S)
  rw [ofTotal_comp, ofTotal_totalValue, ofTotal_totalValue]
  exact hwv

theorem theory_subobject {P T S : Par D}
    (c : P ⟶ S) (hc : isTotal c) (m : T ⟶ S) (hm : isTotal m) (r : S ⟶ T)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = (Ranges.range c).hom)
    {V : D} (v : V ⟶ S.obj) [Mono v] (k : P.obj ⟶ V)
    (hfac : k ≫ v = totalValue c hc) :
    Mono (totalValue m hm) ∧ ∃ w : T.obj ⟶ V, w ≫ v = totalValue m hm :=
  ⟨totalValue_mono_of_retraction m hm r hmr,
    theory_subobject_factorization c hc m hm r hmr hrm v k hfac⟩

/-- The partial identity of a validity subobject, constructed from its monic span. -/
def validityDomain {S : Par D} {V : D} (v : V ⟶ S.obj) [Mono v] : Idem S :=
  Idem.ofRestrict (inverseMono (X := Par.mk V) (Y := S) v)

@[simp] theorem range_ofTotal {X Y : Par D} (f : X.obj ⟶ Y.obj) :
    Ranges.range (ofTotal f) = validityDomain (S := Y) (image.ι f) :=
  range_ofSpan (Raw.total f)

theorem range_totalValue {X Y : Par D} (f : X ⟶ Y) (hf : isTotal f) :
    Ranges.range f = validityDomain (S := Y) (image.ι (totalValue f hf)) := by
  calc
    Ranges.range f = Ranges.range (ofTotal (totalValue f hf)) :=
      congrArg Ranges.range (ofTotal_totalValue f hf).symm
    _ = _ := range_ofTotal _

theorem validity_receives {S : Par D} {V : D} (v : V ⟶ S.obj) [Mono v] :
    ofTotal (X := Par.mk V) (Y := S) v ≫ (validityDomain v).hom =
      ofTotal (X := Par.mk V) (Y := S) v := by
  change ofTotal v ≫ rst (inverseMono v) = ofTotal v
  rw [← inverseMono_total, ← Category.assoc, total_inverseMono, Category.id_comp]

section Interpretation

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C] [Ranges C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [HasZeroMorphisms C]
variable [CoprodStruct (Par D)] [CategoryTheory.HasCoproducts (Par D)]
variable [HasZeroMorphisms (Par D)]

/-- Proposition 4.1's subobject conclusion in the category `Par(D,Mono)`. The inverse of
the validity monomorphism is constructed by its span, rather than supplied as an extra
hypothesis. -/
theorem interpreted_theory_subobject (G : RangeFunctor C (Par D)) {P T S : C}
    (c : P ⟶ S) (hc : isTotal c) (m : T ⟶ S) (hm : isTotal m)
    (r : S ⟶ T) (t : Idem S) (ht : t = Ranges.range c)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = t.hom)
    {V : D} (v : V ⟶ (G.toFunctor.obj S).obj) [Mono v]
    (k : (G.toFunctor.obj P).obj ⟶ V)
    (hfac : k ≫ v = totalValue (G.toFunctor.map c) (G.map_total c hc)) :
    Mono (totalValue (G.toFunctor.map m) (G.map_total m hm)) ∧
      ∃ w : (G.toFunctor.obj T).obj ⟶ V,
        w ≫ v = totalValue (G.toFunctor.map m) (G.map_total m hm) := by
  have he := interpreted_theory_equations G c m r t ht hmr hrm
  exact theory_subobject (G.toFunctor.map c) (G.map_total c hc)
    (G.toFunctor.map m) (G.map_total m hm) (G.toFunctor.map r) he.2.2
    (he.2.1.trans (congrArg Idem.hom he.1)) v k hfac

variable [RestrictionZero (Par D)]

/-- Soundness through a validity subobject and validity/negation
disjointness imply consistency of the interpreted sentence theory. -/
theorem interpreted_theory_consistency (G : RangeFunctor C (Par D)) {P S : C}
    (c : P ⟶ S) (hc : isTotal c) (t : Idem S) (ht : t = Ranges.range c)
    (ν : S ⟶ S) {V : D} (v : V ⟶ (G.toFunctor.obj S).obj) [Mono v]
    (k : (G.toFunctor.obj P).obj ⟶ V)
    (hfac : k ≫ v = totalValue (G.toFunctor.map c) (G.map_total c hc))
    (hconsistent : validityDomain v ⊓
      Idem.pull (G.toFunctor.map ν) (validityDomain v) = ⊥) :
    G.mapIdem t ⊓ Idem.pull (G.toFunctor.map ν) (G.mapIdem t) = ⊥ := by
  have ht' : G.mapIdem t = Ranges.range (G.toFunctor.map c) := by
    apply Idem.ext
    rw [ht]
    exact G.map_range c
  rw [ht']
  let VP : Par D := ⟨V⟩
  let k' : G.toFunctor.obj P ⟶ VP := ofTotal k
  let v' : VP ⟶ G.toFunctor.obj S := ofTotal v
  have hfac' : G.toFunctor.map c = k' ≫ v' := by
    dsimp [k', v']
    rw [← ofTotal_comp, hfac, ofTotal_totalValue]
  exact consistency_of_sound_factorization (G.toFunctor.map c) k' v'
    (validityDomain v) hfac' (validity_receives v) (G.toFunctor.map ν) hconsistent

/-- Proposition 4.1 in the generic category `Par(D,Mono)`: the interpreted
range and splitting equations, the ordinary validity-subobject inclusion,
and semantic consistency. All monomorphism inverses used here are the
canonical inverse spans of the constructed partial-map category. -/
theorem interpreted_theory (G : RangeFunctor C (Par D)) {P T S : C}
    (c : P ⟶ S) (hc : isTotal c) (m : T ⟶ S) (hm : isTotal m)
    (r : S ⟶ T) (t : Idem S) (ht : t = Ranges.range c)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = t.hom)
    {V : D} (v : V ⟶ (G.toFunctor.obj S).obj) [Mono v]
    (k : (G.toFunctor.obj P).obj ⟶ V)
    (hfac : k ≫ v = totalValue (G.toFunctor.map c) (G.map_total c hc)) (ν : S ⟶ S) :
    G.mapIdem t = Ranges.range (G.toFunctor.map c) ∧
      G.toFunctor.map r ≫ G.toFunctor.map m = (G.mapIdem t).hom ∧
      G.toFunctor.map m ≫ G.toFunctor.map r = 𝟙 (G.toFunctor.obj T) ∧
      Mono (totalValue (G.toFunctor.map m) (G.map_total m hm)) ∧
      (∃ w : (G.toFunctor.obj T).obj ⟶ V,
        w ≫ v = totalValue (G.toFunctor.map m) (G.map_total m hm)) ∧
      (validityDomain v ⊓ Idem.pull (G.toFunctor.map ν) (validityDomain v) = ⊥ →
        G.mapIdem t ⊓ Idem.pull (G.toFunctor.map ν) (G.mapIdem t) = ⊥) := by
  have he := interpreted_theory_equations G c m r t ht hmr hrm
  have hf := interpreted_theory_subobject G c hc m hm r t ht hmr hrm v k hfac
  refine ⟨he.1, he.2.1, he.2.2, hf.1, hf.2, ?_⟩
  intro hd
  exact interpreted_theory_consistency G c hc t ht ν v k hfac hd

end Interpretation

end CategoricalEssentialIncompleteness.V46.PartialMaps
