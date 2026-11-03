import CategoricalEssentialIncompleteness.V46UltrapowerTransport

/-! Explicit hypotheses for conditional ultrapower soundness transport.
The standard-code soundness factor and arithmetic comparison are inputs here.
-/

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46

example {I : Type u} (U : Ultrafilter I) {C : Type v} [Category.{w} C]
    (G H : C ⥤ Type u) (η : G ⋙ Ultrapower.functor U ≅ H)
    {P S : C} (c : P ⟶ S) (ν : S ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S) [Mono v] (e : G.obj P ⟶ V)
    (he : e ≫ v = G.map c)
    (hc : Disjoint (Set.range v) ((G.map ν) ⁻¹' Set.range v)) :
    Mono (Ultrapower.transportValidity U η v) ∧
      Ultrapower.transportSoundness U η e ≫
        Ultrapower.transportValidity U η v = H.map c ∧
      Disjoint (Set.range (Ultrapower.transportValidity U η v))
        ((H.map ν) ⁻¹' Set.range (Ultrapower.transportValidity U η v)) :=
  Ultrapower.soundness_transport U η c ν v e he hc

example {I : Type u} (U : Ultrafilter I) {C : Type v} [Category.{w} C]
    (G H : C ⥤ Type u) (η : G ⋙ Ultrapower.functor U ≅ H)
    {P S : C} (c : P ⟶ S) (ν : S ⟶ S) {V : Type u}
    (v : V ⟶ G.obj S) (e : G.obj P ⟶ V) (he : e ≫ v = G.map c)
    (hc : Disjoint (Set.range v) ((G.map ν) ⁻¹' Set.range v)) :
    Disjoint (Set.range (H.map c)) ((H.map ν) ⁻¹' Set.range (H.map c)) :=
  Ultrapower.conclusion_range_consistent U η c ν v e he hc
