import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPowers
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! Success reflection under every interpretation preserving sums and pullbacks.
The interpretation need not preserve the terminal object, so the same
lemmas apply to underlying model interpretations of parameter slices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionModels
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable (K : D ⥤ Type) [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K]

omit [Regular D] [PreservesLimitsOfShape WalkingCospan K] in
theorem sum_cases (A B : D) (x : K.obj (A ⨿ B)) :
    (∃ a : K.obj A, K.map coprod.inl a = x) ∨
      (∃ b : K.obj B, K.map coprod.inr b = x) := by
  have hc := (SyntacticSyntax.preservedSum_properties K A B).2.2
  have hx : x ∈ Set.range (K.map (coprod.inl : A ⟶ A ⨿ B)) ⊔
      Set.range (K.map (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [hc.sup_eq_top]
    trivial
  exact hx

omit [Regular D] [PreservesLimitsOfShape WalkingCospan K] in
theorem sum_disjoint (A B : D) (a : K.obj A) (b : K.obj B) :
    K.map (coprod.inl : A ⟶ A ⨿ B) a ≠ K.map (coprod.inr : B ⟶ A ⨿ B) b := by
  intro h
  exact Set.disjoint_left.mp (SyntacticSyntax.preservedSum_properties K A B).2.2.disjoint
    ⟨a, rfl⟩ ⟨b, h.symm⟩

omit [Regular D] [PreservesColimitsOfShape (Discrete WalkingPair) K] in
theorem caseOf_inl {X A B Y : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y)
    (x : K.obj X) (a : K.obj A) (hx : K.map f x = K.map coprod.inl a) :
    ∃ p : K.obj (pullback f coprod.inl),
      K.map (pullback.fst f coprod.inl) p = x ∧
      K.map (SumFibers.caseOf f g₀ g₁) x = K.map g₀ p := by
  obtain ⟨p, hp, _⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback f coprod.inl).map K) x a hx
  refine ⟨p, hp, ?_⟩
  rw [← hp]
  have he := congrArg K.map (SumFibers.inl_caseOf f g₀ g₁)
  rw [Functor.map_comp] at he
  exact ConcreteCategory.congr_hom he p

omit [Regular D] [PreservesColimitsOfShape (Discrete WalkingPair) K] in
theorem caseOf_inr {X A B Y : D} (f : X ⟶ A ⨿ B)
    (g₀ : pullback f coprod.inl ⟶ Y) (g₁ : pullback f coprod.inr ⟶ Y)
    (x : K.obj X) (b : K.obj B) (hx : K.map f x = K.map coprod.inr b) :
    ∃ p : K.obj (pullback f coprod.inr),
      K.map (pullback.fst f coprod.inr) p = x ∧
      K.map (SumFibers.caseOf f g₀ g₁) x = K.map g₁ p := by
  obtain ⟨p, hp, _⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback f coprod.inr).map K) x b hx
  refine ⟨p, hp, ?_⟩
  rw [← hp]
  have he := congrArg K.map (SumFibers.inr_caseOf f g₀ g₁)
  rw [Functor.map_comp] at he
  exact ConcreteCategory.congr_hom he p

/-- A successful output cannot have come from the designated failure
fiber. This uses sum disjointness, not a decision of a carrier predicate. -/
theorem caseOf_success {X A B Z : D} (f : X ⟶ A ⨿ B)
    (g : pullback f coprod.inr ⟶ OptionSyntax.obj Z)
    (x : K.obj X) (z : K.obj Z)
    (hz : K.map (SumFibers.caseOf f OptionSyntax.fail g) x = K.map coprod.inr z) :
    ∃ p : K.obj (pullback f coprod.inr), K.map (pullback.fst f coprod.inr) p = x ∧
      K.map g p = K.map coprod.inr z := by
  rcases sum_cases K A B (K.map f x) with ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨p, _, hp⟩ := caseOf_inl K f OptionSyntax.fail g x a ha.symm
    have h := hp.symm.trans hz
    change K.map (terminal.from _ ≫ coprod.inl) p = K.map coprod.inr z at h
    rw [Functor.map_comp] at h
    exact False.elim (sum_disjoint K (⊤_ D) Z (K.map (terminal.from _) p) z h)
  · obtain ⟨p, hp, he⟩ := caseOf_inr K f OptionSyntax.fail g x b hb.symm
    exact ⟨p, hp, he.symm.trans hz⟩

theorem caseOf_map_isPullback {X A B Z W : D} (f : X ⟶ A ⨿ B)
    (g : pullback f coprod.inr ⟶ OptionSyntax.obj Z)
    (m : W ⟶ pullback f coprod.inr) (h : W ⟶ Z)
    (hp : IsPullback m h g (coprod.inr : Z ⟶ OptionSyntax.obj Z)) :
    IsPullback (K.map (m ≫ pullback.fst f coprod.inr)) (K.map h)
      (K.map (SumFibers.caseOf f OptionSyntax.fail g))
      (K.map (coprod.inr : Z ⟶ OptionSyntax.obj Z)) := by
  have hm := hp.map K
  have hpb := (IsPullback.of_hasPullback f coprod.inr).map K
  let : Mono (K.map (coprod.inr : B ⟶ A ⨿ B)) :=
    (mono_iff_injective _).mpr (SyntacticSyntax.preservedSum_properties K A B).2.1
  let : Mono (K.map (pullback.fst f coprod.inr)) := hpb.mono_fst_of_mono
  have hinj : Function.Injective (K.map (pullback.fst f coprod.inr)) :=
    (mono_iff_injective _).mp inferInstance
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hw : (m ≫ pullback.fst f coprod.inr) ≫
        SumFibers.caseOf f OptionSyntax.fail g = h ≫ coprod.inr := by
      rw [Category.assoc, SumFibers.inr_caseOf, hp.w]
    have he := congrArg K.map hw
    simpa only [Functor.map_comp] using he
  · intro x y hh
    apply Types.ext_of_isPullback hm
    · apply hinj
      simpa only [Functor.map_comp_apply] using hh.1
    · exact hh.2
  · intro x z hz
    obtain ⟨p, hpx, hpg⟩ := caseOf_success K f g x z hz
    obtain ⟨w, hwm, hwh⟩ := Types.exists_of_isPullback hm p z hpg
    exact ⟨w, by simpa only [Functor.map_comp_apply, hwm] using hpx, hwh⟩

theorem pair_reflects_some (A B : D)
    (x : K.obj (OptionSyntax.obj A ⨯ OptionSyntax.obj B)) (z : K.obj (A ⨯ B))
    (hz : K.map (OptionPowers.pair A B) x = K.map coprod.inr z) :
    K.map (prod.map (coprod.inr : A ⟶ OptionSyntax.obj A)
      (coprod.inr : B ⟶ OptionSyntax.obj B)) z = x := by
  let t := (prod.fst : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ OptionSyntax.obj A)
  let s := pullback.fst t coprod.inr ≫
    (prod.snd : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ OptionSyntax.obj B)
  let values : pullback s coprod.inr ⟶ A ⨯ B :=
    prod.lift (pullback.fst s coprod.inr ≫ pullback.snd t coprod.inr)
      (pullback.snd s coprod.inr)
  let source : pullback s coprod.inr ⟶ OptionSyntax.obj A ⨯ OptionSyntax.obj B :=
    pullback.fst s coprod.inr ≫ pullback.fst t coprod.inr
  have hs : values ≫ prod.map (coprod.inr : A ⟶ OptionSyntax.obj A)
      (coprod.inr : B ⟶ OptionSyntax.obj B) = source := by
    apply prod.hom_ext
    · have he := congrArg (fun k => pullback.fst s coprod.inr ≫ k)
        (pullback.condition (f := t) (g := coprod.inr))
      simpa only [Category.assoc, values, source, t, prod.map_fst, prod.lift_fst_assoc] using he.symm
    · simpa only [Category.assoc, values, source, s, prod.map_snd, prod.lift_snd_assoc] using
        (pullback.condition (f := s) (g := coprod.inr)).symm
  change K.map (SumFibers.caseOf t OptionSyntax.fail
    (SumFibers.caseOf s OptionSyntax.fail (values ≫ coprod.inr))) x = K.map coprod.inr z at hz
  obtain ⟨p, hp, hz⟩ := caseOf_success K t _ x z hz
  obtain ⟨q, hq, hz⟩ := caseOf_success K s _ p z hz
  have hv : K.map values q = z :=
    (SyntacticSyntax.preservedSum_properties K (⊤_ D) (A ⨯ B)).2.1 (by
      simpa only [Functor.map_comp_apply] using hz)
  calc
    _ = K.map (values ≫ prod.map (coprod.inr : A ⟶ OptionSyntax.obj A)
        (coprod.inr : B ⟶ OptionSyntax.obj B)) q := by rw [Functor.map_comp_apply, hv]
    _ = K.map source q := by rw [hs]
    _ = x := by simp only [source, Functor.map_comp_apply]; rw [hq, hp]

omit [FinitaryExtensive D] [PreservesColimitsOfShape (Discrete WalkingPair) K] in
theorem product_ext {A B : D} {x y : K.obj (A ⨯ B)}
    (hx : K.map (prod.fst : A ⨯ B ⟶ A) x = K.map prod.fst y)
    (hy : K.map (prod.snd : A ⨯ B ⟶ B) x = K.map prod.snd y) : x = y :=
  Types.ext_of_isPullback ((IsPullback.of_hasBinaryProduct' A B).map K) hx hy

omit [FinitaryExtensive D] [PreservesLimitsOfShape WalkingCospan K]
    [PreservesColimitsOfShape (Discrete WalkingPair) K] in
@[simp] theorem map_product_fst {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B')
    (x : K.obj (A ⨯ B)) :
    K.map (prod.fst : A' ⨯ B' ⟶ A') (K.map (prod.map f g) x) =
      K.map f (K.map prod.fst x) := by
  have h := congrArg K.map (prod.map_fst f g)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

omit [FinitaryExtensive D] [PreservesLimitsOfShape WalkingCospan K]
    [PreservesColimitsOfShape (Discrete WalkingPair) K] in
@[simp] theorem map_product_snd {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B')
    (x : K.obj (A ⨯ B)) :
    K.map (prod.snd : A' ⨯ B' ⟶ B') (K.map (prod.map f g) x) =
      K.map g (K.map prod.snd x) := by
  have h := congrArg K.map (prod.map_snd f g)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

/-- Success contains exactly tuples of successful children. This is a
fixed-arity induction, valid for every interpreted point and every model;
no recursion over global elements of the syntactic category is used. -/
theorem collect_reflects_some (Q : D) (n : ℕ)
    (x : K.obj (finitePower (OptionSyntax.obj Q) n))
    (z : K.obj (finitePower Q n))
    (hz : K.map (OptionPowers.collect Q n) x = K.map coprod.inr z) :
    K.map (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n) z = x := by
  induction n with
  | zero =>
    have he : x = z :=
      (SyntacticSyntax.preservedSum_properties K (⊤_ D) (finitePower Q 0)).2.1 hz
    change K.map (𝟙 (⊤_ D)) z = x
    rw [Functor.map_id_apply]
    exact he.symm
  | succ n ih =>
    cases n with
    | zero =>
      change K.map (𝟙 (OptionSyntax.obj Q)) x = K.map coprod.inr z at hz
      rw [Functor.map_id_apply] at hz
      exact hz.symm
    | succ n =>
      have hh : K.map (OptionPowers.pair (finitePower Q (n + 1)) Q)
          (K.map (prod.map (OptionPowers.collect Q (n + 1)) (𝟙 _)) x) =
          K.map coprod.inr z := by
        change K.map (prod.map (OptionPowers.collect Q (n + 1)) (𝟙 _) ≫
          OptionPowers.pair (finitePower Q (n + 1)) Q) x = K.map coprod.inr z at hz
        simpa only [Functor.map_comp_apply] using hz
      have hr := pair_reflects_some K (finitePower Q (n + 1)) Q _ z hh
      have h₁ := congrArg (K.map (prod.fst :
        OptionSyntax.obj (finitePower Q (n + 1)) ⨯ OptionSyntax.obj Q ⟶ _)) hr
      simp only [map_product_fst] at h₁
      have h₂ := congrArg (K.map (prod.snd :
        OptionSyntax.obj (finitePower Q (n + 1)) ⨯ OptionSyntax.obj Q ⟶ _)) hr
      simp only [map_product_snd, Functor.map_id_apply] at h₂
      apply product_ext K
      · change K.map prod.fst (K.map (prod.map
          (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) (n + 1)) coprod.inr) z) = _
        rw [map_product_fst]
        exact ih (K.map prod.fst x) (K.map prod.fst z) h₁.symm
      · change K.map prod.snd (K.map (prod.map
          (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) (n + 1)) coprod.inr) z) = _
        rw [map_product_snd]
        exact h₂

theorem collect_map_isPullback (Q : D) (n : ℕ) :
    IsPullback (K.map (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n))
      (K.map (𝟙 (finitePower Q n))) (K.map (OptionPowers.collect Q n))
      (K.map (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n))) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have h : finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n ≫
        OptionPowers.collect Q n = (𝟙 (finitePower Q n)) ≫ coprod.inr := by
      rw [Category.id_comp]
      exact OptionPowers.collect_some Q n
    simpa only [Functor.map_comp] using congrArg K.map h
  · intro x y h
    simpa only [Functor.map_id_apply] using h.2
  · intro x z h
    exact ⟨z, collect_reflects_some K Q n x z h, by simp⟩

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionModels
