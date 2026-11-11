/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutInseparabilitySourceSplit


/-! # Statement checks in `V46MillerCutInseparabilitySourceSplitChecks` -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.SourceSplit
attribute [instance 2000] Uniform.nativeRestriction

example (a : Point) : RangeFunctor (Uniform.PointObject a)
    (SplitObject (Uniform.PointObject a)) := I a
example (a : Point) : (I a).toFunctor.Full := inferInstance
example (a : Point) : (I a).toFunctor.Faithful := inferInstance

example (a : Point) : (I a).toFunctor.map (𝟙 (Uniform.N (Uniform.Family.ofPoint a)))≠0 :=
  I_nonzero a

example (a : Point) (c : Idem ((I a).toFunctor.obj (Uniform.N (Uniform.Family.ofPoint a)))) :
    (I a).mapIdem (recoverIdem a c)=c := include_recovered a c

example (a : Point)
    (c d : Idem ((I a).toFunctor.obj (Uniform.N (Uniform.Family.ofPoint a))))
    (h : Complementary c d) :
    Complementary (SplitObject.baseIdem c) (SplitObject.baseIdem d) :=
  recover_complementary a h

example (a : Point) (c d : Idem (N a)) :
    support a (c⊓d)=support a c∩support a d := support_inf a c d

example (a : Point) (c d : Idem (N a)) :
    support a (c⊔d)=support a c∪support a d := support_sup a c d

example (a : Point) : support a (⊥ : Idem (N a))=∅ := support_bot a
example (a : Point) : support a (⊤ : Idem (N a))=Set.univ := support_top a

example (a : Point) :
    Uniform.support (SplitObject.baseIdem (lowerIdem a))={n | (a n : ℝ)<1/2} :=
  lowerIdem_support a

example (a : Point) :
    Uniform.support (SplitObject.baseIdem (upperIdem a))={n | 1/2<(a n : ℝ)} :=
  upperIdem_support a

example (a : Point) (ha : IsMiller a) :
    Inseparable
      ((I a).mapIdem (CutDigits.lowerIdem a) : Idem ((I a).toFunctor.obj (Uniform.N (Uniform.Family.ofPoint a))))
      ((I a).mapIdem (CutDigits.upperIdem a)) := printed_cut_inseparability a ha

example (a : Point) (ha : IsMiller a) : ¬∃ c d : Idem (N a),
    Complementary c d ∧ lowerIdem a≤c ∧ upperIdem a≤d :=
  (printed_cut_inseparability a ha).no_separator

example (a : Point) : Inseparable
    ((I a).mapIdem (CutInseparability.diagonal0 a))
    ((I a).mapIdem (CutInseparability.diagonal1 a)) := source_diagonal_inseparable a

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.SourceSplit
