/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Ultrapower

/-! # Transport of soundness and consistency along the ultrapower comparison -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

open CategoryTheory CategoryTheory.Limits Filter

namespace CategoricalEssentialIncompleteness.V46.Ultrapower

variable {I : Type u} (U : Ultrafilter I)

/-- Ultrapowers preserve disjointness of a validity subset and its
inverse image under a negation map. -/
theorem maps_disjoint {X V : Type u} (ν : X → X) (v : V → X)
    (h : Disjoint (Set.range v) (ν ⁻¹' Set.range v)) :
    Disjoint (Set.range (Germ.map v : Obj U V → Obj U X))
      ((Germ.map ν) ⁻¹' Set.range (Germ.map v : Obj U V → Obj U X)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  induction a using Germ.inductionOn with | _ a =>
    induction b using Germ.inductionOn with | _ b =>
      have he := Germ.coe_eq.mp hb
      obtain ⟨i, hi⟩ := he.exists
      exact Set.disjoint_left.mp h ⟨a i, rfl⟩ ⟨b i, hi⟩

variable {C : Type v} [Category.{w} C] {G H : C ⥤ Type u}
variable (η : G ⋙ functor U ≅ H)

/-- The interpreted validity inclusion. -/
def transportValidity {S : C} {V : Type u} (v : V ⟶ G.obj S) :
    (functor U).obj V ⟶ H.obj S :=
  (functor U).map v ≫ η.hom.app S

/-- The transported proof-to-validity factor. -/
def transportSoundness {P : C} {V : Type u} (e : G.obj P ⟶ V) :
    H.obj P ⟶ (functor U).obj V :=
  η.inv.app P ≫ (functor U).map e

instance transportValidity_mono {S : C} {V : Type u} (v : V ⟶ G.obj S) [Mono v] :
    Mono (transportValidity U η v) := by
  dsimp [transportValidity]
  infer_instance

/-- Naturality transports the soundness square. -/
theorem transport_factorization {P S : C} (c : P ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S) (e : G.obj P ⟶ V) (he : e ≫ v = G.map c) :
    transportSoundness U η e ≫ transportValidity U η v = H.map c := by
  have hn : (functor U).map (G.map c) ≫ η.hom.app S = η.hom.app P ≫ H.map c :=
    η.hom.naturality c
  have hi : η.inv.app P ≫ η.hom.app P = 𝟙 (H.obj P) := (η.app P).inv_hom_id
  dsimp [transportSoundness, transportValidity]
  calc
    _ = η.inv.app P ≫ ((functor U).map (e ≫ v) ≫ η.hom.app S) := by
      rw [(functor U).map_comp]
      simp only [Category.assoc]
    _ = η.inv.app P ≫ (η.hom.app P ≫ H.map c) := by rw [he, hn]
    _ = H.map c := by rw [← Category.assoc, hi, Category.id_comp]

/-- Naturality identifies negation after transport, so semantic
consistency is preserved together with the validity inclusion. -/
theorem transport_disjoint {S : C} (ν : S ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S)
    (h : Disjoint (Set.range v) ((G.map ν) ⁻¹' Set.range v)) :
    Disjoint (Set.range (transportValidity U η v))
      ((H.map ν) ⁻¹' Set.range (transportValidity U η v)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  change η.hom.app S (Germ.map v b) =
    H.map ν (η.hom.app S (Germ.map v a)) at hb
  have hn : η.hom.app S (Germ.map (G.map ν) (Germ.map v a)) =
      H.map ν (η.hom.app S (Germ.map v a)) :=
    congrArg (fun (f : (G ⋙ functor U).obj S ⟶ H.obj S) =>
      f (Germ.map (fun x => v x) a)) (η.hom.naturality ν)
  have he : Germ.map v b = Germ.map (G.map ν) (Germ.map v a) :=
    (η.app S).toEquiv.injective (hb.trans hn.symm)
  exact Set.disjoint_left.mp (maps_disjoint U (G.map ν) v h) ⟨a, rfl⟩ ⟨b, he⟩

/-- Given the standard soundness factorization and the natural
ultrapower comparison, its transport is monic, factors conclusions, and
is disjoint from its negation inverse image. -/
theorem soundness_transport {P S : C} (c : P ⟶ S) (ν : S ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S) [Mono v] (e : G.obj P ⟶ V)
    (he : e ≫ v = G.map c)
    (hc : Disjoint (Set.range v) ((G.map ν) ⁻¹' Set.range v)) :
    Mono (transportValidity U η v) ∧
      transportSoundness U η e ≫ transportValidity U η v = H.map c ∧
      Disjoint (Set.range (transportValidity U η v))
        ((H.map ν) ⁻¹' Set.range (transportValidity U η v)) :=
  ⟨inferInstance, transport_factorization U η c v e he, transport_disjoint U η ν v hc⟩

include U η in
/-- The interpreted conclusion image is consistent whenever the
transported validity subobject is consistent. -/
theorem conclusion_range_consistent {P S : C} (c : P ⟶ S) (ν : S ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S) (e : G.obj P ⟶ V) (he : e ≫ v = G.map c)
    (hc : Disjoint (Set.range v) ((G.map ν) ⁻¹' Set.range v)) :
    Disjoint (Set.range (H.map c)) ((H.map ν) ⁻¹' Set.range (H.map c)) := by
  have hs : Set.range (H.map c) ⊆ Set.range (transportValidity U η v) := by
    rintro x ⟨p, rfl⟩
    refine ⟨transportSoundness U η e p, ?_⟩
    exact congrArg (fun (f : H.obj P ⟶ H.obj S) => f p)
      (transport_factorization U η c v e he)
  exact (transport_disjoint U η ν v hc).mono hs (Set.preimage_mono hs)

end CategoricalEssentialIncompleteness.V46.Ultrapower
