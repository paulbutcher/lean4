/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Tactic.BVDecide.Normalize.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.DSimp

/-!
This module contains the implementation of the rewriting pass in the fixpoint pipeline, applying
rules from the `bv_normalize` simp set.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Responsible for applying the Bitwuzla style rewrite rules.
-/
public def rewriteRulesPass : Pass where
  name := `rewriteRules
  run' := do
    let bvThms ← bvNormalizeExt.getTheorems
    let cfg ← PreProcessM.getConfig
    let config := {
      maxSteps := cfg.maxSteps
    }
    let dsimpMethods := {
      post := Sym.DSimp.evalGround >> rewriteDsimproc
    }
    let discharger := Sym.Simp.mkDischargerFromSimproc Sym.Simp.evalGround
    let simpMethods := {
      post := Sym.Simp.evalGround >> Normalize.rewriteSimproc >> bvThms.rewrite (d := discharger)
    }

    let goal ← PreProcessM.getGoal
    goal.withContext do
      PreProcessM.mapHyps fun hyp => do
        let newType ← Sym.dsimp hyp.type dsimpMethods { config with }
        let hyp := { hyp with type := newType }
        let res ← Sym.simp hyp.type simpMethods config
        hyp.applySimpResult res

end Normalize
end Lean.Meta.Tactic.BVDecide
