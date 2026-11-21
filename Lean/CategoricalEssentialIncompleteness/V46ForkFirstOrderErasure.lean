/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryPropositionalErasure
public import CategoricalEssentialIncompleteness.V46ForkCategoricalSyntax

/-! # Natural first-order erasure to the propositional fork object -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkFirstOrderErasure
open ForkDerivation.Diagram

/-- The coefficient diagram is the original four-coordinate universal fork. -/
def labels : Object := realization.obj ForkDerivation.variableObject

def atom : labels ⟶ sentences := realization.map ForkDerivation.atom
def negation : sentences ⟶ sentences := realization.map ForkDerivation.negation

/-- The zero quadruple and its two zero-pair images, in the old scalar coding. -/
def zeroArrow : (⊤_ EffectiveFork.Total).obj ⟶ EffectiveFork.V :=
  EffectiveFork.computedMap (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (.const 0) (.const 0) (.const 0)
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (fun _ _ _ => (EffectiveFork.mem_V_left 0 0).mpr rfl)
    (fun _ _ _ => (EffectiveFork.mem_V_right 0 0).mpr rfl)

theorem zeroArrow_total : isTotal zeroArrow := EffectiveFork.computedMap_total _ _ _ _ _ _ _ _ _ _ _

def zeroPoint : ⊤_ Object ⟶ labels :=
  inv (terminalComparison realization) ≫ realization.map ⟨zeroArrow, zeroArrow_total⟩

def distinguishedAtom : ⊤_ Object ⟶ sentences := zeroPoint ≫ atom

/-- Exactly the proposition p_* ⇒ p_* used in the proof. -/
def truth : ⊤_ Object ⟶ sentences :=
  prod.lift distinguishedAtom distinguishedAtom ≫ implication

abbrev firstOrder := ForkCategoricalSyntax.categoricalSyntax labels
abbrev formulas := firstOrder.algebra.a.2

/-- A morphism of fork diagrams; naturality is part of its construction. -/
def erase : formulas ⟶ sentences :=
  NullaryPropositionalErasure.erase firstOrder atom negation implication truth

@[reassoc] theorem equality : firstOrder.equalityConstructor ≫ erase =
    terminal.from _ ≫ truth := NullaryPropositionalErasure.equality _ _ _ _ _

@[reassoc] theorem atom_law : NullaryInterpretation.atomFormula firstOrder ≫ erase = atom :=
  NullaryPropositionalErasure.atom_law _ _ _ _ _

@[reassoc] theorem negation_law : firstOrder.negationConstructor ≫ erase = erase ≫ negation :=
  NullaryPropositionalErasure.negation _ _ _ _ _

@[reassoc] theorem implication_law : firstOrder.implicationConstructor ≫ erase =
    prod.map erase erase ≫ implication := NullaryPropositionalErasure.implication _ _ _ _ _

@[reassoc] theorem quantifier : firstOrder.quantifierConstructor ≫ erase = prod.snd ≫ erase :=
  NullaryPropositionalErasure.quantifier _ _ _ _ _

theorem naturality {j k : WalkingSpan} (f : j ⟶ k) :
    formulas.map f ≫ erase.app k = erase.app j ≫ sentences.map f := erase.naturality f

theorem unique (m : formulas ⟶ sentences)
    (he : firstOrder.equalityConstructor ≫ m = terminal.from _ ≫ truth)
    (ha : NullaryInterpretation.atomFormula firstOrder ≫ m = atom)
    (hn : firstOrder.negationConstructor ≫ m = m ≫ negation)
    (hi : firstOrder.implicationConstructor ≫ m = prod.map m m ≫ implication)
    (hq : firstOrder.quantifierConstructor ≫ m = prod.snd ≫ m) : m = erase :=
  NullaryPropositionalErasure.unique _ _ _ _ _ m he ha hn hi hq

end CategoricalEssentialIncompleteness.V46.ForkFirstOrderErasure
