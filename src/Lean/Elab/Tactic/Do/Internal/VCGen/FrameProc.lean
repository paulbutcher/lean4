/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Meta.Sym.SymM

/-!
The metadata a frame inference procedure operates on: the `wp` application metadata `WPInfo`, the
lattice `LatticeSplit` decomposing a frame operator, and the `FrameProc` bundling an inference
procedure with its operator. `@[frameproc]` registration lives in `FrameProcAttr`.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.Do.Internal

/--
Common metadata for a goal whose right-hand side is a weakest-precondition application
`pre ⊑ wp Prog Value Pred EPred instAL instEAL instWP prog post epost s₁ ... sₙ`.
-/
public structure VCGen.WPInfo where
  /-- The `wp` function head, separated from its explicit core arguments. -/
  head : Expr
  /-- The ordered core arguments of the `wp` application:
  `#[Prog, Value, Pred, EPred, instAL, instEAL, instWP, prog, post, epost]`. -/
  args : Array Expr
  /-- Extra arguments applied after `wp … prog post epost`, usually concrete state arguments. -/
  excessArgs : Array Expr

namespace VCGen.WPInfo

/-- Program type argument of `wp` (e.g. `m α` or a non-monadic program type). -/
public def Prog (info : WPInfo) : Expr := info.args[0]!
/-- The monad of an `m α`-shaped program type, obtained by dropping the value type `α`. For a
non-monadic program type the type itself is returned. -/
public def M (info : WPInfo) : Expr :=
  if info.args[0]!.isApp then info.args[0]!.appFn! else info.args[0]!
/-- Result/value type argument of `wp`. -/
public def Value (info : WPInfo) : Expr := info.args[1]!
/-- Predicate/lattice type argument of `wp`. -/
public def Pred (info : WPInfo) : Expr := info.args[2]!
/-- Exception postcondition type argument of `wp`. -/
public def EPred (info : WPInfo) : Expr := info.args[3]!
/-- `WP` instance argument of `wp`. -/
public def instWP (info : WPInfo) : Expr := info.args[6]!
/-- Program expression classified by VCGen. -/
public def prog (info : WPInfo) : Expr := info.args[7]!
/-- Postcondition argument of `wp`. -/
public def post (info : WPInfo) : Expr := info.args[8]!

end VCGen.WPInfo

/-- A frame inference procedure: given the resource type `R` of the applicable frame operator
`op : R → Pred → Pred`, the goal's precondition, the `wp` metadata of a spec-ready program, and the
spec's precondition instantiated at the call site (the RHS of the spec's precondition VC `pre ⊑ ·`),
optionally produce a frame `F : R` to peel off. `none` leaves the spec to apply directly. -/
public abbrev VCGen.FrameInferenceProc :=
  Expr → Expr → VCGen.WPInfo → Expr → SymM (Option Expr)

/-- A decomposition of a lattice operator on the RHS of an entailment `pre ⊑ op … s⃗`. A custom frame
operator supplies its own split through its `@[frameproc]`, found by `splitLatticeOp?` via the
`FrameProcs.byOp` index.

How the excess (state) arguments `s⃗` are handled follows the shape of the split:

- `applyEq := some _`, `introThm := some _`: distribute `op … s⃗` pointwise through the state
  arguments via the `_apply` equation, then apply `introThm`. Used by `⊓`/`⇨`/`⌜·⌝`/`⊤`.
- `applyEq := some _`, `introThm := none` (an unfolding split): rewrite `op … s⃗` through its
  unfolding `_apply` equation and leave the result for a subsequent split. Used by `costConj`.
- `applyEq := none`: point-frame the state arguments, gating the precondition to `⌜·⃗ = s⃗⌝ ⊓ pre`,
  then apply `introThm` at the function level. Used by `PreservesSup.upperAdjoint`. -/
public structure VCGen.LatticeSplit where
  /-- The `⊑`-form introduction rule decomposing `pre ⊑ op`: it concludes `_ ⊑ op` with the operand
  subgoals as premises. `none` for an unfolding split, whose `applyEq` fully rewrites the operator. -/
  introThm : Option Name := none
  /-- The pointwise `_apply` equation distributing the operator through function application, or
  `none` to point-frame the state arguments. -/
  applyEq : Option Name := none
  /-- Rebuild the operator from its fixed parameters `params`, its operands `as`, and the optional
  lattice carrier type. Unused when `applyEq` is `none` and there are no operands. -/
  mkOperator : Array Expr → Array Expr → Option Expr → MetaM Expr := fun _ _ _ =>
    throwError "LatticeSplit.mkOperator is unavailable for a direct split (applyEq := none)"
  /-- The number of leading arguments before the operands: the carrier type, the lattice instance,
  and any fixed parameters. `2` for the typeclass operators `⊓`/`⇨`/`⌜·⌝`/`⊤`/`upperAdjoint` (carrier
  and instance); `0` for a monomorphic operator with no such prefix. -/
  numParams : Nat := 0
  /-- The number of explicit operands the operator takes after its carrier type, instance, and
  parameters: `2` for `⊓`/`⇨`/`upperAdjoint`, `1` for `⌜·⌝`, `0` for `⊤`. -/
  numOperands : Nat := 0
  /-- The number of leading state arguments the operator itself indexes, over which `applyEq`
  distributes; `none` distributes over every state argument. A pointwise operator (`⊓`/`⇨`/`⌜·⌝`/`⊤`)
  indexes them all (`none`); an operator over a nested lattice (e.g. `costConj` on `Nat → L`) indexes
  only its own, leaving the rest on the residual for a subsequent split. -/
  applyArity : Option Nat := none

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure VCGen.FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Head constant of the frame operator. Keys the procedure in the `byOp` index, consulted by
  `splitLatticeOp?` to decompose a frame residual `op F R`. -/
  op : Name
  /-- Builds the frame operator (head constant `op`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPInfo → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  resourceTy : VCGen.WPInfo → MetaM Expr
  /-- The lattice split decomposing the frame operator `op F R` on the RHS of an entailment.
  Consulted for a residual whose head is not a built-in `latticeSplits` operator. -/
  split : VCGen.LatticeSplit
  /-- The frame inference metaprogram, or `none` for an operator framed only through an explicit
  `frames` clause. -/
  proc : Option VCGen.FrameInferenceProc

/-- The registered frame inference procedures, indexed two ways into the same database: `byProg` by
the program monad's head constant (selected per node in `solve`), and `byOp` by the frame operator's
head constant (consulted by `splitLatticeOp?` to decompose a frame residual). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}
  byOp : Std.HashMap Name VCGen.FrameProc := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp
    byOp := s.byOp.insert fp.op fp }

end Lean.Elab.Tactic.Do.Internal
