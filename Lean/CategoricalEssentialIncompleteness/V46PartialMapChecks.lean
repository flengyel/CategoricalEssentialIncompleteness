import CategoricalEssentialIncompleteness.V46PartialMapTheory

/-! Explicit generic partial-map and interpreted-subobject statements. -/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.PartialMaps

section Pullbacks

variable {D : Type u₂} [Category.{v₂} D] [HasPullbacks D]

example : RestrictionCategory (Par D) := inferInstance

example : Splits (Par D) := inferInstance

example : D ≌ Tot D := totalEquivalence

example {X Y : Par D} (v : X.obj ⟶ Y.obj) [Mono v] :
    isTotal (ofTotal v) ∧ ofTotal v ≫ inverseMono v = 𝟙 X ∧
      inverseMono v ≫ ofTotal v = rst (inverseMono v) :=
  ⟨ofTotal_total v, total_inverseMono v, inverseMono_total v⟩

end Pullbacks

section Regular

variable {D : Type u₂} [Category.{v₂} D] [Regular D]

example : Ranges (Par D) := inferInstance

example {P T S : Par D} (c : P ⟶ S) (hc : isTotal c)
    (m : T ⟶ S) (hm : isTotal m) (r : S ⟶ T)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = (Ranges.range c).hom)
    {V : D} (v : V ⟶ S.obj) [Mono v] (k : P.obj ⟶ V)
    (hfac : k ≫ v = totalValue c hc) :
    Mono (totalValue m hm) ∧ ∃ w : T.obj ⟶ V, w ≫ v = totalValue m hm :=
  theory_subobject c hc m hm r hmr hrm v k hfac

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C] [Ranges C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [HasZeroMorphisms C]
variable [CoprodStruct (Par D)] [CategoryTheory.HasCoproducts (Par D)]
variable [HasZeroMorphisms (Par D)] [RestrictionZero (Par D)]

example (G : RangeFunctor C (Par D)) {P S : C}
    (c : P ⟶ S) (hc : isTotal c) (t : Idem S) (ht : t = Ranges.range c)
    (ν : S ⟶ S) {V : D} (v : V ⟶ (G.toFunctor.obj S).obj) [Mono v]
    (k : (G.toFunctor.obj P).obj ⟶ V)
    (hfac : k ≫ v = totalValue (G.toFunctor.map c) (G.map_total c hc))
    (hd : validityDomain v ⊓
      Idem.pull (G.toFunctor.map ν) (validityDomain v) = ⊥) :
    G.mapIdem t ⊓ Idem.pull (G.toFunctor.map ν) (G.mapIdem t) = ⊥ :=
  interpreted_theory_consistency G c hc t ht ν v k hfac hd

example (G : RangeFunctor C (Par D)) {P T S : C}
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
        G.mapIdem t ⊓ Idem.pull (G.toFunctor.map ν) (G.mapIdem t) = ⊥) :=
  interpreted_theory G c hc m hm r t ht hmr hrm v k hfac ν

end Regular
