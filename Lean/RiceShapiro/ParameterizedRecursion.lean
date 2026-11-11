/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Recursion
public import RiceShapiro.Approximation

/-!
# Uniform indices and parameterized recursion

The subsection "Uniform indices and parameterized recursion" of the manuscript.

A uniform index morphism for an approximation datum is a total `q : A ⟶ I`
with `α = ε(q ⊠ 1_X)`. `exists_uniformIndex` obtains one from the Turing
property of `ε`.

`HasImportedParameterizedRecursion ε` records the parameterized fixed-point
theorem of Di Paola–Heller as used by the manuscript: for every object `Z` and
every total `g : Z ⊠ I ⟶ I` there is a total `h : Z ⟶ I` with
`ε(h ⊠ 1_X) = ε(g⟨1_Z, h⟩ ⊠ 1_X)`. It is a hypothesis, not a Lean axiom, and
this development does not prove that a Turing morphism in a `P`-recursion
category satisfies it.

`parameterizedRecursion` derives the manuscript's lemma from that hypothesis
together with the Turing property: for every `Φ : (Z ⊠ I) ⊠ X ⟶ Y` there is a
total `h : Z ⟶ I` with `ε(h ⊠ 1_X) = Φ(⟨1_Z, h⟩ ⊠ 1_X)`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace ApproximationDatum

variable {X Y : C} (𝒜 : ApproximationDatum X Y)

/-- `q` is a uniform index morphism for `𝒜`: it is total and `α = ε(q ⊠ 1_X)`. -/
def IsUniformIndex (q : 𝒜.A ⟶ 𝒜.I) : Prop :=
  RestrictionCategory.isTotal q ∧ evalAt 𝒜.ev q = 𝒜.approx

/-- The Turing property of `ε` supplies a uniform index morphism. -/
theorem exists_uniformIndex
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev) :
    ∃ q : 𝒜.A ⟶ 𝒜.I, 𝒜.IsUniformIndex q := by
  obtain ⟨q, hq, hqe⟩ := hTuring 𝒜.A 𝒜.approx
  exact ⟨q, hq, hqe⟩

end ApproximationDatum

/-- The parameterized fixed-point theorem of Di Paola–Heller for `ε`: every
total `g : Z ⊠ I ⟶ I` admits a total `h : Z ⟶ I` with
`ε(h ⊠ 1_X) = ε(g⟨1_Z, h⟩ ⊠ 1_X)`.

This is a hypothesis. The present development does not prove that a Turing
morphism in a `P`-recursion category satisfies it. -/
def HasImportedParameterizedRecursion {I X Y : C} (ε : nearProd I X ⟶ Y) :
    Prop :=
  ∀ {Z : C} (g : nearProd Z I ⟶ I), RestrictionCategory.isTotal g →
    ∃ h : Z ⟶ I, RestrictionCategory.isTotal h ∧
      evalAt ε h = evalAt ε (partialPairing (𝟙 Z) h ≫ g)

/-- Parameterized recursion: for every `Φ : (Z ⊠ I) ⊠ X ⟶ Y` there is a total
`h : Z ⟶ I` with `ε(h ⊠ 1_X) = Φ(⟨1_Z, h⟩ ⊠ 1_X)`. -/
theorem parameterizedRecursion {I X Y : C} {ε : nearProd I X ⟶ Y}
    (hImported : HasImportedParameterizedRecursion ε)
    (hTuring : RecursionCategory.IsTuringMorphism ε)
    {Z : C} (Φ : nearProd (nearProd Z I) X ⟶ Y) :
    ∃ h : Z ⟶ I, RestrictionCategory.isTotal h ∧
      evalAt ε h = evalAt Φ (partialPairing (𝟙 Z) h) := by
  obtain ⟨g, hg, hgΦ⟩ := hTuring (nearProd Z I) Φ
  obtain ⟨h, hh, hfix⟩ := hImported g hg
  refine ⟨h, hh, ?_⟩
  rw [hfix, ← hgΦ]
  dsimp only [evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id]

end CategoryTheory
