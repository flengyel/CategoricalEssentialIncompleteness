/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersNumeralsPredicate

/-! # The actual numeral/complement split in the arithmetic total category

The primitive maps are defined first. The generic constructors derive their
copair equations, and the concrete isomorphism/proof records are sealed only
after all comparisons have been checked by the kernel.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u₁ u₂ v₁ v₂
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature

/-- The morphisms are indices of the data, so projection of a proved
leg equation does not unfold the concrete transported isomorphism. -/
structure SpecifiedSplitData {D : Type u₂} [Category.{v₂} D] [HasFiniteCoproducts D]
    (A B W : D) (l : A ⟶ W) (r : B ⟶ W) where
  iso : A ⨿ B ≅ W
  inl : coprod.inl ≫ iso.hom = l
  inr : coprod.inr ≫ iso.hom = r

section Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (E : C ≌ D) {A B W : C} {A' W' : D}
variable (b : A ⨿ B ≅ W) (a : E.functor.obj A ≅ A') (w : E.functor.obj W ≅ W')

def transportSplit : A' ⨿ E.functor.obj B ≅ W' :=
  coprod.mapIso a.symm (Iso.refl _) ≪≫
    asIso (coprodComparison E.functor A B) ≪≫ E.functor.mapIso b ≪≫ w

@[reassoc] theorem transportSplit_inl :
    coprod.inl ≫ (transportSplit E b a w).hom =
      a.inv ≫ E.functor.map (coprod.inl ≫ b.hom) ≫ w.hom := by
  simp only [transportSplit,Iso.trans_hom,coprod.mapIso_hom,Iso.symm_hom,Iso.refl_hom,
    asIso_hom,Functor.mapIso_hom,coprod.inl_map_assoc,coprodComparison,coprod.inl_desc_assoc,
    Functor.map_comp,Category.assoc]

@[reassoc] theorem transportSplit_inr :
    coprod.inr ≫ (transportSplit E b a w).hom =
      E.functor.map (coprod.inr ≫ b.hom) ≫ w.hom := by
  simp only [transportSplit,Iso.trans_hom,coprod.mapIso_hom,Iso.symm_hom,Iso.refl_hom,
    asIso_hom,Functor.mapIso_hom,coprod.inr_map_assoc,coprodComparison,coprod.inr_desc_assoc,
    Functor.map_comp,Category.assoc,Category.id_comp]

/-- Only primitive map comparisons are supplied. The copair equations
are derived from the source equations and the transported isomorphism. -/
def transportSpecified (f : A ⟶ W) (g : B ⟶ W)
    (hf : coprod.inl ≫ b.hom = f) (hg : coprod.inr ≫ b.hom = g)
    (l : A' ⟶ W') (r : E.functor.obj B ⟶ W')
    (hl : a.inv ≫ E.functor.map f ≫ w.hom = l)
    (hr : E.functor.map g ≫ w.hom = r) :
    SpecifiedSplitData A' (E.functor.obj B) W' l r where
  iso := transportSplit E b a w
  inl := (transportSplit_inl E b a w).trans
    ((congrArg (fun k => a.inv ≫ E.functor.map k ≫ w.hom) hf).trans hl)
  inr := (transportSplit_inr E b a w).trans
    ((congrArg (fun k => E.functor.map k ≫ w.hom) hg).trans hr)
/-- The original comparison is passed in its inverse orientation so
concrete equations use its named inverse without unfolding an iso. -/
def transportSpecifiedInverse (w₀ : W' ≅ E.functor.obj W)
    (f : A ⟶ W) (g : B ⟶ W)
    (hf : coprod.inl ≫ b.hom = f) (hg : coprod.inr ≫ b.hom = g)
    (l : A' ⟶ W') (r : E.functor.obj B ⟶ W')
    (hl : a.inv ≫ E.functor.map f ≫ w₀.inv = l)
    (hr : E.functor.map g ≫ w₀.inv = r) :
    SpecifiedSplitData A' (E.functor.obj B) W' l r :=
  transportSpecified E b a w₀.symm f g hf hg l r
    (by simpa only [Iso.symm_hom] using hl)
    (by simpa only [Iso.symm_hom] using hr)

/-- The actual morphisms and their primitive comparisons are returned
by one generic construction. No concrete morphism equation is an input. -/
structure TransportedSplitData (w₀ : W' ≅ E.functor.obj W)
    (f : A ⟶ W) (g : B ⟶ W) where
  left : A' ⟶ W'
  right : E.functor.obj B ⟶ W'
  specified : SpecifiedSplitData A' (E.functor.obj B) W' left right
  left_primitive : left = a.inv ≫ E.functor.map f ≫ w₀.inv
  right_primitive : right = E.functor.map g ≫ w₀.inv

def transportWhole (w₀ : W' ≅ E.functor.obj W)
    (f : A ⟶ W) (g : B ⟶ W)
    (hf : coprod.inl ≫ b.hom = f) (hg : coprod.inr ≫ b.hom = g) :
    TransportedSplitData E a w₀ f g where
  left := a.inv ≫ E.functor.map f ≫ w₀.inv
  right := E.functor.map g ≫ w₀.inv
  specified := transportSpecifiedInverse E b a w₀ f g hf hg _ _ rfl rfl
  left_primitive := rfl
  right_primitive := rfl

end Transport

abbrev complement (e : ℕ) : TotalSplit 𝗣𝗔 := (predicateEquivalence 𝗣𝗔).functor.obj (complementPredicate e)
abbrev parameter : TotalSplit 𝗣𝗔 := ArithmeticIndexedAxioms.parameter

def predicateTerminalIso : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (⊤_ (PredicateCategory 𝗣𝗔)) terminalCarrier :=
  (Limits.terminalIsTerminal (C := PredicateCategory 𝗣𝗔)).uniqueUpToIso
    (SyntacticPredicates.terminalIsTerminal 𝗣𝗔)

def realizedTerminalIso : (predicateEquivalence 𝗣𝗔).functor.obj terminalCarrier ≅ ⊤_ (TotalSplit 𝗣𝗔) :=
  ((predicateEquivalence 𝗣𝗔).functor.mapIso predicateTerminalIso).symm ≪≫
    asIso (terminalComparison (predicateEquivalence 𝗣𝗔).functor)

/-- The original literal predicate split is transported once, together
with its maps and all primitive and coproduct equations. -/
opaque numeralData (e : ℕ) : TransportedSplitData (predicateEquivalence 𝗣𝗔)
    realizedTerminalIso (ArithmeticOmegaComparison.omegaIso 𝗣𝗔)
    (numeralPredicate e) (complementPredicateInclusion e) :=
  transportWhole (predicateEquivalence 𝗣𝗔) (predicateSplitIso e) realizedTerminalIso
    (ArithmeticOmegaComparison.omegaIso 𝗣𝗔) (numeralPredicate e)
    (complementPredicateInclusion e) (predicateSplitIso_inl e) (predicateSplitIso_inr e)

/-- The primitive numeral morphism from the printed terminal object. -/
def numeral (e : ℕ) : ⊤_ (TotalSplit 𝗣𝗔) ⟶ parameter := (numeralData e).left

def complementInclusion (e : ℕ) : complement e ⟶ parameter := (numeralData e).right

abbrev numeral_primitive (e : ℕ) := (numeralData e).left_primitive
abbrev complementInclusion_primitive (e : ℕ) := (numeralData e).right_primitive

def numeralSplitIso (e : ℕ) : (⊤_ (TotalSplit 𝗣𝗔)) ⨿ complement e ≅ parameter :=
  (numeralData e).specified.iso

theorem numeralSplitIso_inl (e : ℕ) :
    coprod.inl ≫ (numeralSplitIso e).hom = numeral e := (numeralData e).specified.inl

theorem numeralSplitIso_inr (e : ℕ) :
    coprod.inr ≫ (numeralSplitIso e).hom = complementInclusion e := (numeralData e).specified.inr


section Product
variable {D : Type u₁} [Category.{v₁} D] [Regular D] [FinitaryExtensive D]
variable {B E : D} (b : (⊤_ D) ⨿ B ≅ E) (X : D)

def unitProductSplit : X ⨿ (B ⨯ X) ≅ E ⨯ X :=
  coprod.mapIso (prod.leftUnitor X).symm (Iso.refl _) ≪≫
    productSumIso (⊤_ D) B X ≪≫ prod.mapIso b (Iso.refl _)

@[reassoc] theorem unitProductSplit_inl :
    coprod.inl ≫ (unitProductSplit b X).hom =
      prod.lift (terminal.from X ≫ (coprod.inl ≫ b.hom)) (𝟙 X) := by
  simp only [unitProductSplit,Iso.trans_hom,coprod.mapIso_hom,Iso.symm_hom,Iso.refl_hom,
    coprod.inl_map_assoc,productSumIso_inl_assoc,prod.mapIso_hom]
  apply prod.hom_ext <;> simp [prod.leftUnitor_inv]

@[reassoc] theorem unitProductSplit_inr :
    coprod.inr ≫ (unitProductSplit b X).hom = prod.map (coprod.inr ≫ b.hom) (𝟙 X) := by
  simp only [unitProductSplit,Iso.trans_hom,coprod.mapIso_hom,Iso.symm_hom,Iso.refl_hom,
    coprod.inr_map_assoc,productSumIso_inr_assoc,prod.mapIso_hom,Category.id_comp]
  simp only [prod.map_map,Category.id_comp]

def unitProductSpecified {ε : ⊤_ D ⟶ E} {u : B ⟶ E}
    (d : SpecifiedSplitData (⊤_ D) B E ε u) (X : D)
    (l : X ⟶ E ⨯ X) (r : B ⨯ X ⟶ E ⨯ X)
    (hl : prod.lift (terminal.from X ≫ ε) (𝟙 X) = l) (hr : prod.map u (𝟙 X) = r) :
    SpecifiedSplitData X (B ⨯ X) (E ⨯ X) l r where
  iso := unitProductSplit d.iso X
  inl := (unitProductSplit_inl d.iso X).trans
    ((congrArg (fun k => prod.lift (terminal.from X ≫ k) (𝟙 X)) d.inl).trans hl)
  inr := (unitProductSplit_inr d.iso X).trans
    ((congrArg (fun k => prod.map k (𝟙 X)) d.inr).trans hr)
structure ProductSplitData (ε : ⊤_ D ⟶ E) (u : B ⟶ E) (X : D) where
  left : X ⟶ E ⨯ X
  right : B ⨯ X ⟶ E ⨯ X
  specified : SpecifiedSplitData X (B ⨯ X) (E ⨯ X) left right
  left_primitive : left = prod.lift (terminal.from X ≫ ε) (𝟙 X)
  right_primitive : right = prod.map u (𝟙 X)

def unitProductWhole {ε : ⊤_ D ⟶ E} {u : B ⟶ E}
    (d : SpecifiedSplitData (⊤_ D) B E ε u) (X : D) : ProductSplitData ε u X where
  left := prod.lift (terminal.from X ≫ ε) (𝟙 X)
  right := prod.map u (𝟙 X)
  specified := unitProductSpecified d X _ _ rfl rfl
  left_primitive := rfl
  right_primitive := rfl
end Product

opaque baseData (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    ProductSplitData (numeral e) (complementInclusion e) X :=
  unitProductWhole (numeralData e).specified X

def fiberMap (e : ℕ) (X : TotalSplit 𝗣𝗔) : X ⟶ parameter ⨯ X := (baseData e X).left

def complementMap (e : ℕ) (X : TotalSplit 𝗣𝗔) : complement e ⨯ X ⟶ parameter ⨯ X :=
  (baseData e X).right

def baseSumIso (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    X ⨿ (complement e ⨯ X) ≅ parameter ⨯ X := (baseData e X).specified.iso

theorem baseSumIso_inl (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    coprod.inl ≫ (baseSumIso e X).hom = fiberMap e X := (baseData e X).specified.inl

theorem baseSumIso_inr (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    coprod.inr ≫ (baseSumIso e X).hom = complementMap e X := (baseData e X).specified.inr

abbrev fiberMap_primitive (e : ℕ) (X : TotalSplit 𝗣𝗔) := (baseData e X).left_primitive
abbrev complementMap_primitive (e : ℕ) (X : TotalSplit 𝗣𝗔) := (baseData e X).right_primitive

def fiberSplit (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    Over (parameter ⨯ X) ⥤ Over X × Over (complement e ⨯ X) :=
  (Over.pullback (fiberMap e X)).prod' (Over.pullback (complementMap e X))

instance fiberSplit_isEquivalence (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    (fiberSplit e X).IsEquivalence := by
  have h := splitAtIso_isEquivalence X (complement e ⨯ X) (baseSumIso e X)
  simpa only [splitAtIso,baseSumIso_inl,baseSumIso_inr,fiberSplit] using h

def sliceEquivalence (e : ℕ) (X : TotalSplit 𝗣𝗔) :
    Over (parameter ⨯ X) ≌ Over X × Over (complement e ⨯ X) :=
  (fiberSplit e X).asEquivalence

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
