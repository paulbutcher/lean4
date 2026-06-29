/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.DSimp

/-!
TODO
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize


/--
TODO
-/
public def zetaPass : Pass where
  name := `zetaPass
  run' := do
    let cfg ← PreProcessM.getConfig
    let config := {
      maxSteps := cfg.maxSteps
    }
    let methods := {
      pre := Sym.DSimp.zeta >> Sym.DSimp.zetaDeltaAll
    }

    let goal ← PreProcessM.getGoal
    goal.withContext do
      PreProcessM.mapHyps fun hyp => do
        let newType ← Sym.dsimp hyp.type methods config
        return { hyp with type := newType }

end Normalize
end Lean.Meta.Tactic.BVDecide
