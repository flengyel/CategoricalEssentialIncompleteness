/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro.Approximation
public import RiceShapiro.ExtensionFamilies
public import RiceShapiro.Selection
public import RiceShapiro.Decisions
public import RiceShapiro.CaseLaws
public import RiceShapiro.ParameterizedRecursion
public import RiceShapiro.UpwardClosure
public import RiceShapiro.WitnessExistence
public import RiceShapiro.GeneratedRepresentation
public import RiceShapiro.LocalConnectedness

/-!
# Countable extension families and the Rice–Shapiro theorem

Root module for the manuscript-specific development, sitting above `PCats`,
which formalizes Appendix A. `PCats` is the categorical library and takes no
manuscript-specific notion; everything defined here is stated against its
classes and adds no parallel definitions.

* `RiceShapiro.Approximation` — approximation data, generated domains,
  extensional domains, extension spans
* `RiceShapiro.Selection` — extension-witness and stage-indexed selection data
* `RiceShapiro.Decisions` — joins of domains, complemented domains, decisions,
  the case-distinction morphism and its branch equations
* `RiceShapiro.ExtensionFamilies` — generated domains admit extension spans,
  the converse comparison, countable extension families and the positive
  representation theorem
* `RiceShapiro.CaseLaws` — the reindexing calculus and the case-distinction
  laws
* `RiceShapiro.ParameterizedRecursion` — uniform index morphisms and the
  deduction of the manuscript's parameterized-recursion lemma from the
  imported Di Paola–Heller fixed-point principle, which is represented by an
  explicit hypothesis and is not proved here
* `RiceShapiro.UpwardClosure` — extensionality under restriction, dense upward
  closure, and upward closure under route (ii)
* `RiceShapiro.WitnessExistence` — existence of selected extension witnesses
  and the pointwise Rice–Shapiro equivalence
* `RiceShapiro.GeneratedRepresentation` — representation on total index
  families and equality with the generated domain
* `RiceShapiro.LocalConnectedness` — connected domains, local connectedness,
  the partial-monomorphism test, and uniqueness of decisions

Next: the categorical equivalence corollary and the classical
recursion-category instance.
The construction of the syntactic category `S_T` and the Appendix B
formalization requires arithmetic syntax and computability and will be kept
under a separate root.
-/

@[expose] public section
