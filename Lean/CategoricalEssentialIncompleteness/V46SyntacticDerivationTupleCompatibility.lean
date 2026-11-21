/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTuples

/-! Literal ordered tuple action agrees with the polynomial power map. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
/-- The exact finite powers and maps used by the inference functor. -/
def premisePowerFunctor (n : ℕ) : PredicateCategory T ⥤ PredicateCategory T where
  obj F := finitePower (D := PredicateCategory T) F n
  map f := finitePowerMap f n
  map_id F := finitePowerMap_id F n
  map_comp f g := finitePowerMap_comp f g n

def premiseProductFunctor (F G : PredicateCategory T ⥤ PredicateCategory T) :
    PredicateCategory T ⥤ PredicateCategory T where
  obj X := F.obj X ⨯ G.obj X
  map f := prod.map (F.map f) (G.map f)
  map_id X := by simp
  map_comp f g := by rw [F.map_comp, G.map_comp, prod.map_map]

/-- Equality of the entire functors supplies the needed transport
naturality, including the chosen unit and each binary product. -/
theorem premisePowerFunctor_eq (n : ℕ) :
    premisePowerFunctor T n = Functor.diag (PredicateCategory T) ⋙
      (SyntaxPolynomial.power .term n).eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change premiseProductFunctor T (premisePowerFunctor T (n + 1))
          (𝟭 (PredicateCategory T)) =
        premiseProductFunctor T (Functor.diag (PredicateCategory T) ⋙
          (SyntaxPolynomial.power .term (n + 1)).eval) (𝟭 (PredicateCategory T))
      rw [ih]

theorem finitePower_cast_natural {F G : PredicateCategory T} (f : F ⟶ G) (n : ℕ) :
    finitePowerMap f n ≫ eqToHom (C := PredicateCategory T)
        (finitePower_eq_polynomial T G n) =
      eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T F n) ≫
        (SyntaxPolynomial.power .term n).eval.map ((f, f) : (F, F) ⟶ (G, G)) := by
  have hn := (eqToHom (premisePowerFunctor_eq T n)).naturality f
  simp only [eqToHom_app] at hn
  exact hn

theorem finitePowerEncoder_arrow (F : PredicateCategory T) (n : ℕ) :
    representedArrow T (finitePowerEncoder T F n) =
      eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T F n) ≫
        representedArrow T (encodePolynomial T F F (SyntaxPolynomial.power .term n)) := by
  change representedArrow T (chosenGraph T
      (eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T F n))) ≫
        representedArrow T (encodePolynomial T F F (SyntaxPolynomial.power .term n)) = _
  rw [chosenGraph_class]

/-- Total graph morphisms are equal once inclusion of their relations
has been proved in every model of T. -/
theorem hom_eq_of_relation_imp {A B : PredicateCategory T} (f g : A ⟶ B)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M),
      relation T f M x y → relation T g M x y) : f = g := by
  apply hom_ext T
  intro M _ hM x y
  constructor
  · exact h M x y
  · intro hgy
    obtain ⟨z, hfz, _⟩ := relation_total T f M x (relation_support T g M x y hgy).1
    have hzy := relation_functional T g M x z y (h M x z hfz) hgy
    simpa only [hzy] using hfz

section ModelsForCompatibility
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The product-map equations determine both component relations. -/
theorem product_map_components {A B C D : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ D)
    (x y a b c d : M)
    (hm : relation T (prod.map f g) M x y)
    (ha : relation T (prod.fst : A ⨯ B ⟶ A) M x a)
    (hb : relation T (prod.snd : A ⨯ B ⟶ B) M x b)
    (hc : relation T (prod.fst : C ⨯ D ⟶ C) M y c)
    (hd : relation T (prod.snd : C ⨯ D ⟶ D) M y d) :
    relation T f M a c ∧ relation T g M b d := by
  have h₁ : relation T (prod.map f g ≫ prod.fst) M x c :=
    (relation_comp T _ _ M x c).mpr ⟨y, hm, hc⟩
  rw [prod.map_fst] at h₁
  obtain ⟨a', ha', hf⟩ := (relation_comp T _ _ M x c).mp h₁
  have hea := relation_functional T (prod.fst : A ⨯ B ⟶ A) M x a' a ha' ha
  have h₂ : relation T (prod.map f g ≫ prod.snd) M x d :=
    (relation_comp T _ _ M x d).mpr ⟨y, hm, hd⟩
  rw [prod.map_snd] at h₂
  obtain ⟨b', hb', hg⟩ := (relation_comp T _ _ M x d).mp h₂
  have heb := relation_functional T (prod.snd : A ⨯ B ⟶ B) M x b' b hb' hb
  exact ⟨by simpa only [hea] using hf, by simpa only [heb] using hg⟩

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- This compares the chosen categorical power map with its raw coordinates, using given
representation graphs in every model of T. -/
theorem power_map_coordinates {F G : PredicateCategory T} (f : GraphMorphism T F G)
    (n : ℕ) (u v x y : M)
    (hu : (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb ![u, x])
    (hv : (baseRepresentation T G G (SyntaxPolynomial.power .term n)).val.Evalb ![v, y])
    (hxy : relation T ((SyntaxPolynomial.power .term n).eval.map
      ((representedArrow T f, representedArrow T f) :
      (F, F) ⟶ (G, G))) M x y) :
    (tupleGraph f.graph n).val.Evalb ![u, v] := by
  induction n generalizing u v x y with
  | zero =>
    have hu' : u = 0 := (baseRepresentation_unit_eval T M F F u x).mp hu |>.2
    have hv' : v = 0 := (baseRepresentation_unit_eval T M G G v y).mp hv |>.2
    exact (tupleGraph_zero _ u v).mpr ⟨hu', hv'⟩
  | succ n ih =>
    cases n with
    | zero =>
      have hux : x = u := (baseRepresentation_term_eval T M F F u x).mp hu |>.2
      have hvy : y = v := (baseRepresentation_term_eval T M G G v y).mp hv |>.2
      change relation T (representedArrow T f) M x y at hxy
      simpa only [Nat.zero_add, tupleGraph_one, ← hux, ← hvy] using
        (relation_class T f M x y).mp hxy
    | succ n =>
      obtain ⟨u₁, u₂, x₁, x₂, hue, hu₁, hu₂, hx₁, hx₂⟩ :=
        (baseRepresentation_product_eval T M F F
          (SyntaxPolynomial.power .term (n + 1)) .term u x).mp hu
      obtain ⟨v₁, v₂, y₁, y₂, hve, hv₁, hv₂, hy₁, hy₂⟩ :=
        (baseRepresentation_product_eval T M G G
          (SyntaxPolynomial.power .term (n + 1)) .term v y).mp hv
      have hmap : relation T
          (prod.map ((SyntaxPolynomial.power .term (n + 1)).eval.map
            ((representedArrow T f, representedArrow T f) : (F, F) ⟶ (G, G)))
            (representedArrow T f)) M x y := hxy
      have hc := product_map_components T M
        ((SyntaxPolynomial.power .term (n + 1)).eval.map
          ((representedArrow T f, representedArrow T f) : (F, F) ⟶ (G, G)))
        (representedArrow T f) x y x₁ x₂ y₁ y₂ hmap
        ((chosenGraph_eval T _ M x x₁).mp hx₁)
        ((chosenGraph_eval T _ M x x₂).mp hx₂)
        ((chosenGraph_eval T _ M y y₁).mp hy₁)
        ((chosenGraph_eval T _ M y y₂).mp hy₂)
      have hleft := ih u₁ v₁ x₁ y₁ hu₁ hv₁ hc.1
      have hux : x₂ = u₂ := (baseRepresentation_term_eval T M F F u₂ x₂).mp hu₂ |>.2
      have hvy : y₂ = v₂ := (baseRepresentation_term_eval T M G G v₂ y₂).mp hv₂ |>.2
      have hright : f.graph.val.Evalb ![u₂, v₂] := by
        simpa only [← hux, ← hvy] using (relation_class T f M x₂ y₂).mp hc.2
      exact (tupleGraph_product _ n u v).mpr
        ⟨u₁, u₂, v₁, v₂, hue, hve, hleft, hright⟩

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem finitePowerEncoder_relation (F : PredicateCategory T) (n : ℕ) (x u : M) :
    relation T (representedArrow T (finitePowerEncoder T F n)) M x u ↔
      ∃ z : M, relation T (eqToHom (C := PredicateCategory T)
          (finitePower_eq_polynomial T F n)) M x z ∧
        (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb ![u, z] := by
  rw [finitePowerEncoder_arrow, relation_comp]
  simp only [relation_class]
  simp [encodePolynomial]

end ModelsForCompatibility

/-- The constructed arithmetic tuple action commutes with the original
categorical finite-power map and both constructed finite-power encoders. -/
theorem tupleMorphism_compatibility {F G : PredicateCategory T}
    (f : GraphMorphism T F G) (n : ℕ) :
    finitePowerMap (representedArrow T f) n ≫ representedArrow T (finitePowerEncoder T G n) =
      representedArrow T (finitePowerEncoder T F n) ≫ representedArrow T (tupleMorphism f n) := by
  apply hom_eq_of_relation_imp T
  intro M _ hM x v hleft
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  obtain ⟨y, hxy, hy⟩ := (relation_comp T _ _ M x v).mp hleft
  obtain ⟨y', hyy', hv⟩ := (finitePowerEncoder_relation T M G n y v).mp hy
  obtain ⟨u, hu, _⟩ := relation_total T
    (representedArrow T (finitePowerEncoder T F n)) M x
    (relation_support T (finitePowerMap (representedArrow T f) n) M x y hxy).1
  obtain ⟨x', hxx', hu'⟩ := (finitePowerEncoder_relation T M F n x u).mp hu
  have hs : relation T (finitePowerMap (representedArrow T f) n ≫
      eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T G n)) M x y' :=
    (relation_comp T _ _ M x y').mpr ⟨y, hxy, hyy'⟩
  rw [finitePower_cast_natural] at hs
  obtain ⟨x'', hxx'', hm⟩ := (relation_comp T _ _ M x y').mp hs
  have he := relation_functional T
    (eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T F n))
    M x x'' x' hxx'' hxx'
  subst x''
  have hraw := power_map_coordinates T M f n u v x' y' hu' hv hm
  exact (relation_comp T _ _ M x v).mpr
    ⟨u, hu, (relation_class T (tupleMorphism f n) M u v).mpr hraw⟩

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
