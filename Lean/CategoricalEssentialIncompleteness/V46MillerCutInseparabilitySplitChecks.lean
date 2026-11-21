/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutInseparabilitySplit


/-! # Cut subobjects in the restriction splitting -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks

example (p : Bits) : Category (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : RestrictionCategory (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : Ranges (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : Splits (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : RestrictionCoproducts (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : BinaryJoins (SplitObject (Uniform.RelativeObject p)) := inferInstance
example (p : Bits) : JoinInverse (SplitObject (Uniform.RelativeObject p)) := inferInstance

example (p : Bits) : RangeFunctor (Uniform.RelativeObject p) (SplitObject (Uniform.RelativeObject p)) := I p
example (p : Bits) : (I p).toFunctor.Faithful := inferInstance
example (p : Bits) : (I p).toFunctor.Full := inferInstance
example (p : Bits) {X Y : Uniform.RelativeObject p} (f : X ⟶ Y) :
    ((I p).toFunctor.map f).hom = f := I_value p f
example (p : Bits) : (I p).toFunctor.map (𝟙 (Uniform.N (Uniform.Family.singleton p))) ≠ 0 := I_nonzero p

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks
