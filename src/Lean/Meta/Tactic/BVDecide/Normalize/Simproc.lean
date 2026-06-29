/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize
public import Lean.Meta.Tactic.BVDecide.Attr
import Init.Omega
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.LitValues
public import Lean.Meta.Sym.DSimp.DSimpM

section

/-!
This module contains implementations of simprocs used in the `bv_normalize` simp set.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

open Std.Tactic.BVDecide.Normalize

def mkDecideProofWith (p : Expr) (inst : Expr) : Expr :=
  let decP := mkApp2 (mkConst ``Decidable.decide) p inst
  let boolTy := mkConst ``Bool
  let decEqTrue := mkApp3 (mkConst ``Eq [1]) boolTy decP (mkConst ``Bool.true)
  let h := mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true)
  let h := mkExpectedPropHint h decEqTrue
  mkApp3 (mkConst ``of_decide_eq_true) p inst h

@[inline]
def mkLit [ToExpr α] (a : α) : Sym.SymM Expr :=
  Sym.share <| toExpr a

namespace BitVec

def mkComplement (e : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instComplement) wExpr
  Sym.share <| mkApp3 (mkConst ``Complement.complement [0]) ty inst e

def mkNeg (e : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instNeg) wExpr
  Sym.share <| mkApp3 (mkConst ``Neg.neg [0]) ty inst e

def mkOr (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHOrOfOrOp [0]) ty (mkApp (mkConst ``BitVec.instOrOp) wExpr)
  Sym.share <| mkApp6 (mkConst ``HOr.hOr [0, 0, 0]) ty ty ty inst lhs rhs

def mkAnd (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHAndOfAndOp [0]) ty (mkApp (mkConst ``BitVec.instAndOp) wExpr)
  Sym.share <| mkApp6 (mkConst ``HAnd.hAnd [0, 0, 0]) ty ty ty inst lhs rhs

def mkXor (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHXorOfXorOp [0]) ty (mkApp (mkConst ``BitVec.instXorOp) wExpr)
  Sym.share <| mkApp6 (mkConst ``HXor.hXor [0, 0, 0]) ty ty ty inst lhs rhs

def mkAdd (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHAdd [0]) ty (mkApp (mkConst ``BitVec.instAdd) wExpr)
  Sym.share <| mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) ty ty ty inst lhs rhs

def mkSub (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHSub [0]) ty (mkApp (mkConst ``BitVec.instSub) wExpr)
  Sym.share <| mkApp6 (mkConst ``HSub.hSub [0, 0, 0]) ty ty ty inst lhs rhs

def mkMul (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp2 (mkConst ``instHMul [0]) ty (mkApp (mkConst ``BitVec.instMul) wExpr)
  Sym.share <| mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) ty ty ty inst lhs rhs

def mkAppend (lhs rhs : Expr) (wlExpr wrExpr wResExpr : Expr) : Sym.SymM Expr :=
  let lty := mkApp (mkConst ``BitVec) wlExpr
  let rty := mkApp (mkConst ``BitVec) wrExpr
  let resty := mkApp (mkConst ``BitVec) wResExpr
  let inst := mkApp2 (mkConst ``BitVec.instHAppendHAddNat) wlExpr wrExpr
  Sym.share <| mkApp6 (mkConst ``HAppend.hAppend [0, 0, 0]) lty rty resty inst lhs rhs

def mkNatShiftRight (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instHShiftRightNat) wExpr
  Sym.share <| mkApp6 (mkConst ``HShiftRight.hShiftRight [0, 0, 0]) ty (mkConst ``Nat) ty inst lhs rhs

def mkNatShiftLeft (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let inst := mkApp (mkConst ``BitVec.instHShiftLeftNat) wExpr
  Sym.share <| mkApp6 (mkConst ``HShiftLeft.hShiftLeft [0, 0, 0]) ty (mkConst ``Nat) ty inst lhs rhs

def mkBEq (lhs rhs : Expr) (wExpr : Expr) : Sym.SymM Expr :=
  let ty := mkApp (mkConst ``BitVec) wExpr
  let instDec := mkApp (mkConst ``instDecidableEqBitVec) wExpr
  let inst := mkApp2 (mkConst ``instBEqOfDecidableEq [0]) ty instDec
  Sym.share <| mkApp4 (mkConst ``BEq.beq [0]) ty inst lhs rhs

end BitVec

namespace Bool

def mkNot (e : Expr) : Sym.SymM Expr :=
  Sym.share <| mkApp (mkConst ``Bool.not) e

def mkAnd (lhs rhs : Expr) : Sym.SymM Expr :=
  Sym.share <| mkApp2 (mkConst ``Bool.and) lhs rhs

end Bool

namespace Nat

def mkDecideProofEq (lhs rhs : Expr) : Expr :=
  let p := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) lhs rhs
  let inst := mkApp2 (mkConst ``instDecidableEqNat) lhs rhs
  mkDecideProofWith p inst

def mkDecideProofLt (lhs rhs : Expr) : Expr :=
  let p := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) lhs rhs
  let inst := mkApp2 (mkConst ``Nat.decLt) lhs rhs
  mkDecideProofWith p inst

def mkDecideProofLe (lhs rhs : Expr) : Expr :=
  let p := mkApp4 (mkConst ``LE.le [0]) (mkConst ``Nat) (mkConst ``instLENat) lhs rhs
  let inst := mkApp2 (mkConst ``Nat.decLe) lhs rhs
  mkDecideProofWith p inst

def mkPow (lhs rhs : Expr) : Sym.SymM Expr :=
  let ty := mkConst ``Nat
  let instPow := mkApp2 (mkConst ``instPowNat [0]) ty (mkConst ``instNatPowNat)
  let inst := mkApp3 (mkConst ``instHPow [0, 0]) ty ty instPow
  Sym.share <| mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) ty ty ty inst lhs rhs

def mkAdd (lhs rhs : Expr) : Sym.SymM Expr :=
  let ty := mkConst ``Nat
  let inst := mkApp2 (mkConst ``instHAdd [0]) ty (mkConst ``instAddNat)
  Sym.share <| mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) ty ty ty inst lhs rhs

end Nat

section SimpleUnifiers

def bvAnd (ty lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := ty | return .rfl
  if lhs == rhs then
    return .step lhs (mkApp2 (mkConst ``BitVec.and_self) wExpr lhs)
  else
    let some w ← getNatValue? wExpr | return .rfl
    let notAnd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Complement.complement _ _ lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.and_contra') wExpr rhs
      return some <| .step (← mkLit 0#w) proof

    let andNot : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Complement.complement _ _ rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.and_contra) wExpr lhs
      return some <| .step (← mkLit 0#w) proof

    let onesAnd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w', lhsValue⟩ ← getBitVecValue? lhs | return none
      if lhsValue != -1#w' then return none
      let proof :=
        mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ones_and) wExpr rhs
      return some <| .step rhs proof

    let andOnes : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w', rhsValue⟩ ← getBitVecValue? rhs | return none
      if rhsValue != -1#w' then return none
      let proof :=
        mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.and_ones) wExpr lhs
      return some <| .step lhs proof

    if let some step ← notAnd then return step
    if let some step ← andNot then return step
    if let some step ← onesAnd then return step
    if let some step ← andOnes then return step
    return .rfl

def bvAdd (ty lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := ty | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  if lhs == rhs then
    let expr ← BitVec.mkMul lhs (← mkLit 2#w) wExpr
    return .step expr (mkApp2 (mkConst ``BitVec.add_same) wExpr lhs)
  else
    let notAdd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Complement.complement _ _ lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.not_add) wExpr rhs
      return some <| .step (← mkLit (-1#w)) proof

    let addNot : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Complement.complement _ _ rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp2 (mkConst ``BitVec.add_not) wExpr lhs
      return some <| .step (← mkLit (-1#w)) proof

    let addNeg : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      let some ⟨w', rrhsVal⟩ ← getBitVecValue? rrhs | return none
      if rrhsVal != 1#w' then return none
      let_expr Complement.complement _ _ rlhs := rlhs | return none
      if rlhs != lhs then return none
      let proof := mkApp2 (mkConst ``BitVec.add_neg) wExpr lhs
      return some <| .step (← mkLit 0#w) proof

    let negAdd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      let some ⟨w', lrhsVal⟩ ← getBitVecValue? lrhs | return none
      if lrhsVal != 1#w' then return none
      let_expr Complement.complement _ _ llhs := llhs | return none
      if llhs != rhs then return none
      let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.neg_add) wExpr rhs
      return some <| .step (← mkLit 0#w) proof

    let addNegMul : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w', rhsVal⟩ ← getBitVecValue? rhs | return none
      if rhsVal != 1#w' then return none
      let_expr Complement.complement _ _ lhs := lhs | return none
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      if llhs.isAppOf ``HMul.hMul then
        let_expr HMul.hMul _ _ _ _ lllhs llrhs := llhs | return none
        if lllhs == lrhs then
          let newRhs ← BitVec.mkComplement llrhs wExpr
          let expr ← BitVec.mkMul lllhs newRhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul'') wExpr lllhs llrhs
          return some <| .step expr proof
        else if llrhs == lrhs then
          let newLhs ← BitVec.mkComplement lllhs wExpr
          let expr ← BitVec.mkMul newLhs llrhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul''') wExpr llrhs lllhs
          return some <| .step expr proof
        else
          return none
      else if lrhs.isAppOf ``HMul.hMul then
        let_expr HMul.hMul _ _ _ _ lrlhs lrrhs := lrhs | return none
        if llhs == lrlhs then
          let newRhs ← BitVec.mkComplement lrrhs wExpr
          let expr ← BitVec.mkMul lrlhs newRhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul) wExpr lrlhs lrrhs
          return some <| .step expr proof
        else if llhs == lrrhs then
          let newLhs ← BitVec.mkComplement lrlhs wExpr
          let expr ← BitVec.mkMul newLhs lrrhs wExpr
          let proof := mkApp3 (mkConst ``BitVec.add_neg_mul') wExpr lrrhs lrlhs
          return some <| .step expr proof
        else
          return none
      else
        return none

    let addShiftLeft : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HShiftLeft.hShiftLeft _ _ _ _ rlhs rrhs := rhs | return none
      if lhs != rrhs then return none
      let expr ← BitVec.mkOr lhs rhs wExpr
      let proof := mkApp3 (mkConst ``BitVec.add_shiftLeft_eq_or_shiftLeft) wExpr lhs rlhs
      return some <| .step expr proof

    let shiftLeftAdd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HShiftLeft.hShiftLeft _ _ _ _ llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let expr ← BitVec.mkOr lhs rhs wExpr
      let proof := mkApp3 (mkConst ``BitVec.shiftLeft_add_eq_shiftLeft_or) wExpr rhs llhs
      return some <| .step expr proof

    if let some step ← notAdd then return step
    if let some step ← addNot then return step
    if let some step ← addNeg then return step
    if let some step ← negAdd then return step
    if let some step ← addNegMul then return step
    if let some step ← addShiftLeft then return step
    if let some step ← shiftLeftAdd then return step
    return .rfl

def bvShiftRight (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  if lhs == rhs then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ushiftRight_self) wExpr lhs
    return .step (← mkLit 0#w) proof
  else
    let_expr BitVec.ofNat nExpr kExpr := rhs | return .rfl
    let some n ← getNatValue? nExpr | return .rfl
    if w != n then return .rfl
    let some k ← getNatValue? kExpr | return .rfl
    let expr ← BitVec.mkNatShiftRight lhs (← mkLit (k % 2 ^ w)) wExpr
    let proof := mkApp3 (mkConst ``BitVec.ushiftRight_ofNat_eq) wExpr lhs kExpr
    return .step expr proof

def extractLsb' (wExpr startExpr lenExpr targetExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  match_expr targetExpr with
  | HAnd.hAnd _ _ _ _ lhs rhs =>
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr ← BitVec.mkAnd lhs' rhs' lenExpr
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_and) wExpr lhs rhs startExpr lenExpr
    return .step expr proof
  | HXor.hXor _ _ _ _ lhs rhs =>
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr ← BitVec.mkXor lhs' rhs' lenExpr
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_xor) wExpr lhs rhs startExpr lenExpr
    return .step expr proof
  | HAdd.hAdd _ _ _ _ lhs rhs =>
    let some start ← getNatValue? startExpr | return .rfl
    let some len ← getNatValue? lenExpr | return .rfl
    let some width ← getNatValue? wExpr | return .rfl
    if !(start == 0 && len ≤ width) then return .rfl
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr ← BitVec.mkAdd lhs' rhs' lenExpr
    let proof :=
      mkApp5
        (mkConst ``BitVec.extractLsb'_add)
        wExpr
        lenExpr
        lhs
        rhs
        (Nat.mkDecideProofLe lenExpr wExpr)
    return .step expr proof
  | HMul.hMul _ _ _ _ lhs rhs =>
    let some start ← getNatValue? startExpr | return .rfl
    let some len ← getNatValue? lenExpr | return .rfl
    let some width ← getNatValue? wExpr | return .rfl
    if !(start == 0 && len ≤ width) then return .rfl
    let lhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr lhs
    let rhs' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr rhs
    let expr ← BitVec.mkMul lhs' rhs' lenExpr
    let proof :=
      mkApp5
        (mkConst ``BitVec.extractLsb'_mul)
        wExpr
        lenExpr
        lhs
        rhs
        (Nat.mkDecideProofLe lenExpr wExpr)
    return .step expr proof
  | HAppend.hAppend lhsTypeExpr rhsTypeExpr _ _ lhs rhs =>
    let_expr BitVec lhsWidthExpr := lhsTypeExpr | return .rfl
    let_expr BitVec rhsWidthExpr := rhsTypeExpr | return .rfl
    let some start ← getNatValue? startExpr | return .rfl
    let some len ← getNatValue? lenExpr | return .rfl
    let some rhsWidth ← getNatValue? rhsWidthExpr | return .rfl
    if start + len ≤ rhsWidth then
      let expr := mkApp4 (mkConst ``BitVec.extractLsb') rhsWidthExpr startExpr lenExpr rhs
      let proof :=
        mkApp7
          (mkConst ``BitVec.extractLsb'_append_eq_of_add_le)
          lhsWidthExpr
          rhsWidthExpr
          lhs
          rhs
          startExpr
          lenExpr
          (Nat.mkDecideProofLe (← mkLit (start + len)) rhsWidthExpr)
      return .step (← Sym.share expr) proof
    else if rhsWidth ≤ start then
      let expr := mkApp4 (mkConst ``BitVec.extractLsb') lhsWidthExpr (← mkLit (start - rhsWidth)) lenExpr lhs
      let proof :=
        mkApp7
          (mkConst ``BitVec.extractLsb'_append_eq_of_le)
          lhsWidthExpr
          rhsWidthExpr
          lhs
          rhs
          startExpr
          lenExpr
          (Nat.mkDecideProofLe rhsWidthExpr startExpr)
      return .step (← Sym.share expr) proof
    else
      -- extract is not limited to side
      return .rfl
  | Complement.complement _ _ inner =>
    let some initialWidthVal ← getNatValue? wExpr | return .rfl
    let some startVal ← getNatValue? startExpr | return .rfl
    let some lenVal ← getNatValue? lenExpr | return .rfl
    if !(startVal + lenVal) < initialWidthVal then return .rfl
    let newInner := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr inner
    let expr ← BitVec.mkComplement newInner lenExpr
    let lt := Nat.mkDecideProofLt (← Nat.mkAdd startExpr lenExpr) wExpr
    let proof := mkApp5 (mkConst ``BitVec.extractLsb'_not_of_lt) wExpr inner startExpr lenExpr lt
    return .step expr proof
  | cond _ discr thenExpr elseExpr =>
    let thenExpr' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr thenExpr
    let elseExpr' := mkApp4 (mkConst ``BitVec.extractLsb') wExpr startExpr lenExpr elseExpr
    let newTy := mkApp (mkConst ``BitVec) lenExpr
    let expr := mkApp4 (mkConst ``cond [1]) newTy discr thenExpr' elseExpr'
    let proof :=
      mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.extractLsb'_if)
        wExpr
        discr
        thenExpr
        elseExpr
        startExpr
        lenExpr
    return .step (← Sym.share expr) proof
  | _ =>
    let some w ← getNatValue? wExpr | return .rfl
    let some start ← getNatValue? startExpr | return .rfl
    let some len ← getNatValue? lenExpr | return .rfl
    if start != 0 then return .rfl
    if len != w then return .rfl
    let proof := mkApp2 (mkConst ``BitVec.extractLsb'_eq_self) wExpr targetExpr
    return .step targetExpr proof

def bvShiftLeft (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  let_expr BitVec.ofNat nExpr kExpr := rhs | return .rfl
  let some n ← getNatValue? nExpr | return .rfl
  if w != n then return .rfl
  let some k ← getNatValue? kExpr | return .rfl
  let expr ← BitVec.mkNatShiftLeft lhs (← mkLit (k % 2 ^ w)) wExpr
  let proof := mkApp3 (mkConst ``BitVec.shiftLeft_ofNat_eq) wExpr lhs kExpr
  return .step expr proof

def bvSshiftRight' (nExpr mExpr lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some n ← getNatValue? nExpr | return .rfl
  let some m ← getNatValue? mExpr | return .rfl
  if n != m then return .rfl
  let_expr BitVec.ofNat wExpr kExpr := rhs | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  if n != w then return .rfl
  let some k ← getNatValue? kExpr | return .rfl
  let expr := mkApp3 (mkConst ``BitVec.sshiftRight) wExpr lhs (← mkLit (k % 2 ^ w))
  let proof := mkApp3 (mkConst ``BitVec.sshiftRight'_ofNat_eq_sshiftRight) wExpr lhs kExpr
  return .step (← Sym.share expr) proof

def boolAnd (lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  if lhs == rhs then
    return .step lhs (mkApp (mkConst ``Bool.and_self) lhs)
  else
    let andFalse : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.false := rhs | return none
      let proof := mkApp (mkConst ``Bool.and_false) lhs
      return some <| .step (← mkLit false) proof

    let falseAnd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.false := lhs | return none
      let proof := mkApp (mkConst ``Bool.false_and) rhs
      return some <| .step (← mkLit false) proof

    let andTrue : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.true := rhs | return none
      let proof := mkApp (mkConst ``Bool.and_true) lhs
      return some <| .step lhs proof

    let trueAnd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.true := lhs | return none
      let proof := mkApp (mkConst ``Bool.true_and) rhs
      return some <| .step rhs proof

    let andNotSelf : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.not rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.and_not_self) lhs
      return some <| .step (← mkLit false) proof

    let notAndSelf : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.not lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.not_and_self) lhs
      return some <| .step (← mkLit false) proof

    let andSelfLeft : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.and rlhs rrhs := rhs | return none
      if lhs != rlhs then return none
      let expr ← Bool.mkAnd lhs rrhs
      let proof := mkApp2 (mkConst ``Bool.and_self_left) lhs rrhs
      return some <| .step expr proof

    let andSelfRight : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.and llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let expr ← Bool.mkAnd llhs rhs
      let proof := mkApp2 (mkConst ``Bool.and_self_right) llhs rhs
      return some <| .step expr proof

    if let some step ← falseAnd then return step
    if let some step ← andFalse then return step
    if let some step ← andTrue then return step
    if let some step ← trueAnd then return step
    if let some step ← andNotSelf then return step
    if let some step ← notAndSelf then return step
    if let some step ← andSelfLeft then return step
    if let some step ← andSelfRight then return step
    return .rfl

def bvBeq (wExpr lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  if lhs == rhs then
    let proof :=
      mkApp2
        (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.beq_self_eq_true)
        wExpr
        lhs
    return .step (← mkLit true) proof
  else
    let some w ← getNatValue? wExpr | return .rfl
    let addInj : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      if lrhs == rrhs then
        let expr ← BitVec.mkBEq llhs rlhs wExpr
        let proof :=
          mkApp4 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_left_inj)
            wExpr
            llhs
            rlhs
            lrhs
        return some <| .step expr proof
      else if lrhs == rlhs then
        let expr ← BitVec.mkBEq llhs rrhs wExpr
        let proof :=
          mkApp4 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_left_inj')
            wExpr
            llhs
            rrhs
            lrhs
        return some <| .step expr proof
      else if llhs == rlhs then
        let expr ← BitVec.mkBEq lrhs rrhs wExpr
        let proof :=
          mkApp4 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_right_inj)
            wExpr
            lrhs
            rrhs
            llhs
        return some <| .step expr proof
      else if llhs == rrhs then
        let expr ← BitVec.mkBEq lrhs rlhs wExpr
        let proof :=
          mkApp4 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_right_inj')
            wExpr
            lrhs
            rlhs
            llhs
        return some <| .step expr proof
      else
        return none

    let notEqComm : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return none
      let_expr Complement.complement _ _ innerLhs := lhs | return none
      let expr ← BitVec.mkBEq innerLhs (← mkLit (~~~rhsVal)) (← mkLit w)
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm)
          (← mkLit w)
          innerLhs
          rhs
      return some <| .step expr proof

    let notEqComm' : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return none
      let_expr Complement.complement _ _ innerRhs := rhs | return none
      let expr ← BitVec.mkBEq innerRhs (← mkLit (~~~lhsVal)) (← mkLit w)
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.not_eq_comm')
          (← mkLit w)
          lhs
          innerRhs
      return some <| .step expr proof

    let andEqAllOnes : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return none
      if -1#w != rhsVal then return none
      let_expr HAnd.hAnd _ _ _ _ llhs lrhs := lhs | return none
      let newLhs ← BitVec.mkBEq llhs rhs (← mkLit w)
      let newRhs ← BitVec.mkBEq lrhs rhs (← mkLit w)
      let expr ← Bool.mkAnd newLhs newRhs
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.and_eq_allOnes)
          (← mkLit w)
          llhs
          lrhs
      return some <| .step expr proof

    let allOnesEqAnd : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return none
      if -1#w != lhsVal then return none
      let_expr HAnd.hAnd _ _ _ _ rlhs rrhs := rhs | return none
      let newLhs ← BitVec.mkBEq rlhs lhs (← mkLit w)
      let newRhs ← BitVec.mkBEq rrhs lhs (← mkLit w)
      let expr ← Bool.mkAnd newLhs newRhs
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.allOnes_eq_and)
          (← mkLit w)
          rlhs
          rrhs
      return some <| .step expr proof

    let addConstBeqConst : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      let some ⟨_, lrhsVal⟩ ← getBitVecValue? lrhs | return none
      let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return none
      let wExpr ← mkLit w
      let expr ← BitVec.mkBEq llhs (← BitVec.mkSub rhs lrhs wExpr) wExpr
      let proof :=
        mkApp4 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.add_const_beq_const)
          wExpr
          (← mkLit lrhsVal.toNat)
          (← mkLit rhsVal.toNat)
          llhs
      return some <| .step expr proof

    let constAddBeqConst : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      let some ⟨_, llhsVal⟩ ← getBitVecValue? llhs | return none
      let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return none
      let wExpr ← mkLit w
      let expr ← BitVec.mkBEq lrhs (← BitVec.mkSub rhs llhs wExpr) wExpr
      let proof :=
        mkApp4 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.const_add_beq_const)
          wExpr
          (← mkLit llhsVal.toNat)
          lrhs
          (← mkLit rhsVal.toNat)
      return some <| .step expr proof

    let constBeqAddConstBeq : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      let some ⟨_, rrhsVal⟩ ← getBitVecValue? rrhs | return none
      let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return none
      let wExpr ← mkLit w
      let expr ← BitVec.mkBEq rlhs (← BitVec.mkSub lhs rrhs wExpr) wExpr
      let proof :=
        mkApp4 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.const_beq_add_const_beq)
          wExpr
          (← mkLit lhsVal.toNat)
          rlhs
          (← mkLit rrhsVal.toNat)
      return some <| .step expr proof

    let constBeqConstAddBeq : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      let some ⟨_, rlhsVal⟩ ← getBitVecValue? rlhs | return none
      let some ⟨w, lhsVal⟩ ← getBitVecValue? lhs | return none
      let wExpr ← mkLit w
      let expr ← BitVec.mkBEq rrhs (← BitVec.mkSub lhs rlhs wExpr) wExpr
      let proof :=
        mkApp4 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.const_beq_const_add_beq)
          wExpr
          (← mkLit lhsVal.toNat)
          (← mkLit rlhsVal.toNat)
          rrhs
      return some <| .step expr proof

    let addLeftEqSelf : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      if lrhs != rhs then return none
      let expr ← BitVec.mkBEq llhs (← mkLit 0#w) wExpr
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_left_eq_self)
          (← mkLit w)
          llhs
          lrhs
      return some <| .step expr proof

    let addRightEqSelf : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ llhs lrhs := lhs | return none
      if llhs != rhs then return none
      let expr ← BitVec.mkBEq lrhs (← mkLit 0#w) wExpr
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.add_right_eq_self)
          (← mkLit w)
          llhs
          lrhs
      return some <| .step expr proof

    let selfEqAddRight : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      if rlhs != lhs then return none
      let expr ← BitVec.mkBEq rrhs (← mkLit 0#w) wExpr
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.self_eq_add_right)
          (← mkLit w)
          rlhs
          rrhs
      return some <| .step expr proof

    let selfEqAddLeft : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr HAdd.hAdd _ _ _ _ rlhs rrhs := rhs | return none
      if rrhs != lhs then return none
      let expr ← BitVec.mkBEq rlhs (← mkLit 0#w) wExpr
      let proof :=
        mkApp3 (mkConst ``Std.Tactic.BVDecide.Frontend.Normalize.BitVec.self_eq_add_left)
          (← mkLit w)
          rrhs
          rlhs
      return some <| .step expr proof

    if let some step ← addInj then return step
    if let some step ← notEqComm then return step
    if let some step ← notEqComm' then return step
    if let some step ← andEqAllOnes then return step
    if let some step ← allOnesEqAnd then return step
    if let some step ← addConstBeqConst then return step
    if let some step ← constAddBeqConst then return step
    if let some step ← constBeqAddConstBeq then return step
    if let some step ← constBeqConstAddBeq then return step
    if let some step ← addLeftEqSelf then return step
    if let some step ← addRightEqSelf then return step
    if let some step ← selfEqAddRight then return step
    if let some step ← selfEqAddLeft then return step
    return .rfl

def boolBeq (lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  if lhs == rhs then
    let proof := mkApp (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.beq_self_eq_true) lhs
    return .step (← mkLit true) proof
  else
    let notSelf : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.not rhs := rhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.beq_not_self) lhs
      return some <| .step (← mkLit false) proof

    let selfNot : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr Bool.not lhs := lhs | return none
      if lhs != rhs then return none
      let proof := mkApp (mkConst ``Bool.not_beq_self) lhs
      return some <| .step (← mkLit false) proof

    let selfLeft : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr BEq.beq _ _ rlhs rrhs := rhs | return none
      if lhs != rlhs then return none
      let proof := mkApp2 (mkConst ``Bool.beq_self_left) lhs rrhs
      return some <| .step rrhs proof

    let selfRight : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr BEq.beq _ _ llhs lrhs := lhs | return none
      if rhs != lrhs then return none
      let proof := mkApp2 (mkConst ``Bool.beq_self_right) llhs rhs
      return some <| .step llhs proof

    if let some step ← notSelf then return step
    if let some step ← selfNot then return step
    if let some step ← selfLeft then return step
    if let some step ← selfRight then return step
    return .rfl

def bvCast (nExpr mExpr hExpr targetExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some n ← getNatValue? nExpr | return .rfl
  let some m ← getNatValue? mExpr | return .rfl
  if n != m then return .rfl
  let proof := mkApp3 (mkConst ``BitVec.cast_eq) nExpr hExpr targetExpr
  return .step targetExpr proof

def boolOr (lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let newLhs ← Bool.mkNot lhs
  let newRhs ← Bool.mkNot rhs
  let expr ← Bool.mkNot (← Bool.mkAnd newLhs newRhs)
  let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.or_elim) lhs rhs
  return .step expr proof

def bvOr (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let newLhs ← BitVec.mkComplement lhs wExpr
  let newRhs ← BitVec.mkComplement rhs wExpr
  let expr ← BitVec.mkComplement (← BitVec.mkAnd newLhs newRhs wExpr) wExpr
  let proof := mkApp3 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.or_elim) wExpr lhs rhs
  return .step expr proof

def bvSub (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let newRhs ← BitVec.mkNeg rhs wExpr
  let expr ← BitVec.mkAdd lhs newRhs wExpr
  let proof := mkApp3 (mkConst ``BitVec.sub_eq_add_neg) wExpr lhs rhs
  return .step expr proof

def ult (wExpr lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  if lhs == rhs then
    let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.lt_irrefl) wExpr lhs
    return .step (← mkLit false) proof (done := true)
  else
    let maxUlt : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, lhsValue⟩ ← getBitVecValue? lhs | return none
      if lhsValue == -1#w then
        let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.max_ult') (← mkLit w) rhs
        return some <| .step (← mkLit Bool.false) proof
      else
        return none

    let lt_allOnes : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let some ⟨w, rhs⟩ ← getBitVecValue? rhs | return none
      if rhs != -1#w then return none
      let expr ← Bool.mkNot (← BitVec.mkBEq lhs (← mkLit (-1#w)) wExpr)
      let proof := mkApp2 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.ult_max') wExpr lhs
      return some <| .step expr proof

    if let some step ← maxUlt then return step
    if let some step ← lt_allOnes then return step
    return .rfl

def condSimplify (e α c thenExpr elseExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let [lvl] := e.getAppFn.constLevels! | return .rfl
  if thenExpr == elseExpr then
    let proof := mkApp3 (mkConst ``Bool.cond_self [lvl]) α c thenExpr
    return .step thenExpr proof
  else
    let iteThenIte : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 tThenExpr tElseExpr := thenExpr | return none
      if c != c2 then return none
      let expr := mkApp4 (mkConst ``cond [lvl]) α c tThenExpr elseExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_then_ite [lvl])
          α
          c
          tThenExpr
          tElseExpr
          elseExpr
      return some <| .step (← Sym.share expr) proof

    let iteElseIte : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 eThenExpr eElseExpr := elseExpr | return none
      if c != c2 then return none
      let expr := mkApp4 (mkConst ``cond [lvl]) α c thenExpr eElseExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_else_ite [lvl])
          α
          c
          thenExpr
          eThenExpr
          eElseExpr
      return some <| .step (← Sym.share expr) proof

    let iteThenIte' : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 tThenExpr tElseExpr := thenExpr | return none
      if tThenExpr != elseExpr then return none
      let expr := mkApp4 (mkConst ``cond [lvl]) α (← Bool.mkAnd c (← Bool.mkNot c2)) tElseExpr elseExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_then_ite' [lvl])
          α
          c
          c2
          tThenExpr
          tElseExpr
      return some <| .step (← Sym.share expr) proof

    let iteElseIte' : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 eThenExpr eElseExpr := elseExpr | return none
      if thenExpr != eThenExpr then return none
      let expr :=
        mkApp4 (mkConst ``cond [lvl])
          α
          (← Bool.mkAnd (← Bool.mkNot c) (← Bool.mkNot c2))
          eElseExpr
          thenExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_else_ite' [lvl])
          α
          c
          c2
          thenExpr
          eElseExpr
      return some <| .step (← Sym.share expr) proof

    let iteThenIte'' : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 tThenExpr tElseExpr := thenExpr | return none
      if tElseExpr != elseExpr then return none
      let expr :=
        mkApp4 (mkConst ``cond [lvl]) α (← Bool.mkAnd c c2) tThenExpr elseExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_then_ite'' [lvl])
          α
          c
          c2
          tElseExpr
          tThenExpr
      return some <| .step (← Sym.share expr) proof

    let iteElseIte'' : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
      let_expr cond _ c2 eThenExpr eElseExpr := elseExpr | return none
      if thenExpr != eElseExpr then return none
      let expr :=
        mkApp4 (mkConst ``cond [lvl])
          α
          (← Bool.mkAnd (← Bool.mkNot c) c2)
          eThenExpr
          thenExpr
      let proof :=
        mkApp5 (mkConst ``Std.Tactic.BVDecide.Normalize.Bool.ite_else_ite'' [lvl])
          α
          c
          c2
          thenExpr
          eThenExpr
      return some <| .step (← Sym.share expr) proof

    if let some step ← iteThenIte then return step
    if let some step ← iteElseIte then return step
    if let some step ← iteThenIte' then return step
    if let some step ← iteElseIte' then return step
    if let some step ← iteThenIte'' then return step
    if let some step ← iteElseIte'' then return step
    return .rfl

end SimpleUnifiers

def boolEqToBeq (lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  match_expr rhs with
  | Bool.true => return .rfl
  | _ =>
    let beqApp := ← mkAppM ``BEq.beq #[lhs, rhs]
    let expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) beqApp (← mkLit true)
    let proof := mkApp2 (mkConst ``Bool.eq_to_beq) lhs rhs
    return .step (← Sym.share expr) proof

-- A specialised version of BitVec.neg_eq_not_add so it doesn't trigger on -constant
def bvNeg (α val : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  match ← getBitVecValue? val with
  | some _ => return .rfl
  | none =>
    let proof := mkApp2 (mkConst ``BitVec.neg_eq_not_add) (← mkLit w) val
    let expr ← BitVec.mkAdd (← BitVec.mkComplement val wExpr) (← mkLit 1#w) wExpr
    return .step expr proof

/-- Return a number `k` such that `2^k = n`. -/
def Nat.log2Exact (n : Nat) : Option Nat := do
  guard <| n ≠ 0
  let k := n.log2
  guard <| Nat.pow 2 k == n
  return k

def bvUdiv (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec _ := α | return .rfl
  let some ⟨w, rhsVal⟩ ← getBitVecValue? rhs | return .rfl
  let n := rhsVal.toNat
  -- BitVec.ofNat w n, where n =def= 2^k
  let some k := Nat.log2Exact n | return .rfl
  -- check that k < w.
  if k ≥ w then return .rfl
  let wExpr ← mkLit w
  let kExpr ← mkLit k
  let nExpr ← mkLit n
  let rhs ← BitVec.mkNatShiftRight lhs kExpr wExpr
  -- 2^k = n
  let hk := Nat.mkDecideProofEq (← Nat.mkPow (← mkLit 2) kExpr) nExpr
  -- k < w
  let hlt := Nat.mkDecideProofLt kExpr wExpr
  let proof := mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.udiv_ofNat_eq_of_lt)
    wExpr lhs nExpr kExpr hk hlt
  return .step rhs proof

def isTwoPow (x : BitVec w) : Option Nat :=
  if x == 0#w then
    none
  else
    go x 0
where
  go {w : Nat} (x : BitVec w) (counter : Nat) : Option Nat :=
    if counter < w then
      let attempt := 1#w <<< counter
      if attempt == x then
        some counter
      else
        go x (counter + 1)
    else
      none

def bvMul (α lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wExpr := α | return .rfl
  let onesMul : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some ⟨w', lhsVal⟩ ← getBitVecValue? lhs | return none
    if lhsVal != -1#w' then return none
    let expr ← BitVec.mkNeg rhs wExpr
    let proof := mkApp2 (mkConst ``BitVec.ones_mul) wExpr rhs
    return some <| .step expr proof

  let mulOnes : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some ⟨w', rhsVal⟩ ← getBitVecValue? rhs | return none
    if rhsVal != -1#w' then return none
    let expr ← BitVec.mkNeg lhs wExpr
    let proof := mkApp2 (mkConst ``BitVec.mul_ones) wExpr lhs
    return some <| .step expr proof

  let twoPowMul : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some ⟨_, lhsVal⟩ ← getBitVecValue? lhs | return none
    let some pow := isTwoPow lhsVal | return none
    let powExpr ← mkLit pow
    let expr ← BitVec.mkNatShiftLeft rhs powExpr wExpr
    let proof := mkApp3 (mkConst ``BitVec.twoPow_mul_eq_shiftLeft) wExpr rhs powExpr
    return some <| .step expr proof

  let mulTwoPow : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some ⟨_, rhsVal⟩ ← getBitVecValue? rhs | return none
    let some pow := isTwoPow rhsVal | return none
    let powExpr ← mkLit pow
    let expr ← BitVec.mkNatShiftLeft lhs powExpr wExpr
    let proof := mkApp3 (mkConst ``BitVec.mul_twoPow_eq_shiftLeft) wExpr lhs powExpr
    return some <| .step expr proof

  if let some step ← onesMul then return step
  if let some step ← mulOnes then return step
  if let some step ← twoPowMul then return step
  if let some step ← mulTwoPow then return step
  return .rfl

def bvShiftRightNat (α lhsExpr rhsExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some rhs ← getNatValue? rhsExpr | return .rfl
  let_expr BitVec wExpr := α | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  if rhs < w then
    let zero ← mkLit 0#rhs
    let newLen := w - rhs
    let newLenExpr ← mkLit newLen
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rhsExpr newLenExpr lhsExpr
    let concat ← BitVec.mkAppend zero extract (← mkLit rhs) newLenExpr (← mkLit (newLen + rhs))
    let expr := mkApp4 (mkConst ``BitVec.cast) wExpr wExpr (← mkEqRefl wExpr) concat
    let h := Nat.mkDecideProofLt rhsExpr wExpr
    let proof := mkApp4 (mkConst ``BitVec.ushiftRight_eq_extractLsb'_of_lt) wExpr lhsExpr rhsExpr h
    return .step (← Sym.share expr) proof
  else
    let expr ← mkLit 0#w
    let h := Nat.mkDecideProofLe wExpr rhsExpr
    let proof := mkApp4 (mkConst ``BitVec.ushiftRight_eq_zero) wExpr lhsExpr rhsExpr h
    return .step expr proof (done := true)

def bvShiftLeftNat (α lhsExpr rhsExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some rhs ← getNatValue? rhsExpr | return .rfl
  let_expr BitVec wExpr := α | return .rfl
  let some w ← getNatValue? wExpr | return .rfl
  if rhs < w then
    let zero ← mkLit 0#rhs
    let newLen := w - rhs
    let newLenExpr ← mkLit newLen
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr (← mkLit 0) newLenExpr lhsExpr
    let concat ← BitVec.mkAppend extract zero newLenExpr (← mkLit rhs) (← mkLit (newLen + rhs))
    let expr := mkApp4 (mkConst ``BitVec.cast) wExpr wExpr (← mkEqRefl wExpr) concat
    let h := Nat.mkDecideProofLt rhsExpr wExpr
    let proof := mkApp4 (mkConst ``BitVec.shiftLeft_eq_concat_of_lt) wExpr lhsExpr rhsExpr h
    return .step (← Sym.share expr) proof
  else
    let expr ← mkLit 0#w
    let h := Nat.mkDecideProofLe wExpr rhsExpr
    let proof := mkApp4 (mkConst ``BitVec.shiftLeft_eq_zero) wExpr lhsExpr rhsExpr h
    return .step expr proof (done := true)

def bvAppend (α β lhs rhs : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let_expr BitVec wlhs := α | return .rfl
  let_expr BitVec wrhs := β | return .rfl

  let concatExtract : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let_expr BitVec.extractLsb' wExpr lstartExpr llenExpr lhsVal := lhs | return none
    let some lstart ← getNatValue? lstartExpr | return none
    let some llen ← getNatValue? llenExpr | return none
    let_expr BitVec.extractLsb' _ rstartExpr rlenExpr rhsVal := rhs | return none
    let some rstart ← getNatValue? rstartExpr | return none
    let some rlen ← getNatValue? rlenExpr | return none
    if lhsVal != rhsVal then return none
    if lstart != rstart + rlen then return none
    let newLenExpr ← mkLit (llen + rlen)
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rstartExpr newLenExpr lhsVal
    let expr :=
      mkApp4 (mkConst ``BitVec.cast) newLenExpr newLenExpr (← mkEqRefl newLenExpr) extract
    let proof :=
      mkApp7
        (mkConst ``BitVec.extractLsb'_append_extractLsb'_eq_extractLsb')
        wExpr
        lstartExpr
        rstartExpr
        rlenExpr
        llenExpr
        lhsVal
        (← mkEqRefl lstartExpr)
    return some <| .step (← Sym.share expr) proof

  let concatNotExtract : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let_expr Complement.complement _ _ lhs := lhs | return none
    let_expr Complement.complement _ _ rhs := rhs | return none
    let_expr BitVec.extractLsb' wExpr lstartExpr llenExpr lhsVal := lhs | return none
    let some lstart ← getNatValue? lstartExpr | return none
    let some llen ← getNatValue? llenExpr | return none
    let_expr BitVec.extractLsb' _ rstartExpr rlenExpr rhsVal := rhs | return none
    let some rstart ← getNatValue? rstartExpr | return none
    let some rlen ← getNatValue? rlenExpr | return none
    if lhsVal != rhsVal then return none
    if lstart != rstart + rlen then return none
    let newLenExpr ← mkLit (llen + rlen)
    let extract := mkApp4 (mkConst ``BitVec.extractLsb') wExpr rstartExpr newLenExpr lhsVal
    let notExpr ← BitVec.mkComplement extract newLenExpr
    let expr :=
      mkApp4 (mkConst ``BitVec.cast) newLenExpr newLenExpr (← mkEqRefl newLenExpr) notExpr
    let proof :=
      mkApp7
        (mkConst ``BitVec.not_extractLsb'_append_not_extractLsb'_eq_not_extractLsb')
        wExpr
        lstartExpr
        rstartExpr
        rlenExpr
        llenExpr
        lhsVal
        (← mkEqRefl lstartExpr)
    return some <| .step (← Sym.share expr) proof

  let appendConstLeft : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let_expr BitVec.ofNat _ a := lhs | return none
    let_expr HAppend.hAppend rlhsTy rrhsTy _ _ rlhs rrhs := rhs | return none
    let_expr BitVec w2Expr := rlhsTy | return none
    let_expr BitVec w3Expr := rrhsTy | return none
    let_expr BitVec.ofNat _ b := rlhs | return none
    let some w1 ← getNatValue? wlhs | return none
    let some w2 ← getNatValue? w2Expr | return none
    let some w3 ← getNatValue? w3Expr | return none
    let w1w2 ← mkLit (w1 + w2)
    let inner1 ← BitVec.mkAppend lhs rlhs wlhs w2Expr w1w2
    let resWidth ← mkLit (w1 + w2 + w3)
    let inner2 ← BitVec.mkAppend inner1 rrhs w1w2 w3Expr resWidth
    let h := mkApp3 (mkConst ``Nat.add_assoc) wlhs w2Expr w3Expr
    let expr := mkApp4 (mkConst ``BitVec.cast) resWidth resWidth h inner2
    let proof :=
      mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.append_const_left)
        w3Expr wlhs a w2Expr b rrhs
    return some <| .step (← Sym.share expr) proof

  let appendConstRight : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let_expr BitVec.ofNat _ c := rhs | return none
    let_expr HAppend.hAppend llhsTy lrhsTy _ _ llhs lrhs := lhs | return none
    let_expr BitVec w1Expr := llhsTy | return none
    let_expr BitVec w2Expr := lrhsTy | return none
    let_expr BitVec.ofNat _ b := lrhs | return none
    let some w1 ← getNatValue? w1Expr | return none
    let some w2 ← getNatValue? w2Expr | return none
    let some w3 ← getNatValue? wrhs | return none
    let w2w3 ← mkLit (w2 + w3)
    let inner1 ← BitVec.mkAppend lrhs rhs w2Expr wrhs w2w3
    let resWidth ← mkLit (w1 + w2 + w3)
    let inner2 ← BitVec.mkAppend llhs inner1 w1Expr w2w3 resWidth
    let h :=
      mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) resWidth resWidth
        (mkApp3 (mkConst ``Nat.add_assoc) w1Expr w2Expr wrhs)
    let expr := mkApp4 (mkConst ``BitVec.cast) resWidth resWidth h inner2
    let proof :=
      mkApp6 (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.append_const_right)
        w1Expr w2Expr b wrhs c llhs
    return some <| .step (← Sym.share expr) proof

  let appendZeroWidth : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some 0 ← getNatValue? wrhs | return none
    let proof := mkApp3 (mkConst ``BitVec.append_zero_width) wlhs lhs rhs
    return some <| .step lhs proof

  let zeroWidthAppend : Sym.Simp.SimpM (Option Sym.Simp.Result) := do
    let some 0 ← getNatValue? wlhs | return none
    let some _ ← getNatValue? wrhs | return none
    let expr := mkApp4 (mkConst ``BitVec.cast) wrhs wrhs (← mkEqRefl wrhs) rhs
    let proof := mkApp3 (mkConst ``BitVec.zero_width_append) wrhs lhs rhs
    return some <| .step (← Sym.share expr) proof

  if let some step ← concatExtract then return step
  if let some step ← concatNotExtract then return step
  if let some step ← appendConstLeft then return step
  if let some step ← appendConstRight then return step
  if let some step ← appendZeroWidth then return step
  if let some step ← zeroWidthAppend then return step
  return .rfl

def setWidth (oldWidthExpr newWidthExpr targetExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some oldWidth ← getNatValue? oldWidthExpr | return .rfl
  let some newWidth ← getNatValue? newWidthExpr | return .rfl
  if newWidth ≤ oldWidth then
    let expr :=
      mkApp4
        (mkConst ``BitVec.extractLsb')
        oldWidthExpr
        (← mkLit 0)
        newWidthExpr
        targetExpr
    let proof :=
      mkApp4
        (mkConst ``BitVec.setWidth_eq_extractLsb')
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe newWidthExpr oldWidthExpr)
    return .step (← Sym.share expr) proof
  else
    let finalWidth := newWidth - oldWidth
    let lhs ← mkLit 0#finalWidth
    let concat ← BitVec.mkAppend
      lhs
      targetExpr
      (← mkLit finalWidth)
      oldWidthExpr
      (← mkLit (finalWidth + oldWidth))
    let expr :=
      mkApp4
        (mkConst ``BitVec.cast)
        newWidthExpr
        newWidthExpr
        (← mkEqRefl newWidthExpr)
        concat
    let proof :=
      mkApp4
        (mkConst ``BitVec.setWidth_eq_append)
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe oldWidthExpr newWidthExpr)
    return .step (← Sym.share expr) proof

def signExtend (oldWidthExpr newWidthExpr targetExpr : Expr) : Sym.Simp.SimpM (Sym.Simp.Result) := do
  let some oldWidth ← getNatValue? oldWidthExpr | return .rfl
  let some newWidth ← getNatValue? newWidthExpr | return .rfl
  if newWidth ≤ oldWidth then
    let expr :=
      mkApp4
        (mkConst ``BitVec.extractLsb')
        oldWidthExpr
        (← mkLit 0)
        newWidthExpr
        targetExpr
    let proof :=
      mkApp4
        (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim')
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe newWidthExpr oldWidthExpr)
    return .step (← Sym.share expr) proof
  else
    let msb := mkApp2 (mkConst ``BitVec.msb) oldWidthExpr targetExpr
    let finalWidth := newWidth - oldWidth
    let finalWidthExpr ← mkLit finalWidth
    let lhs := mkApp4
        (mkConst ``cond [1])
        (mkApp (mkConst ``BitVec) finalWidthExpr)
        msb
        (← mkLit (-1#finalWidth))
        (← mkLit (0#finalWidth))
    let concat ← BitVec.mkAppend
      lhs
      targetExpr
      finalWidthExpr
      oldWidthExpr
      (← mkLit (finalWidth + oldWidth))
    let expr :=
      mkApp4
        (mkConst ``BitVec.cast)
        newWidthExpr
        newWidthExpr
        (← mkEqRefl newWidthExpr)
        concat
    let proof :=
      mkApp4
        (mkConst ``Std.Tactic.BVDecide.Normalize.BitVec.signExtend_elim)
        oldWidthExpr
        targetExpr
        newWidthExpr
        (Nat.mkDecideProofLe oldWidthExpr newWidthExpr)
    return .step (← Sym.share expr) proof

public def rewriteSimproc : Sym.Simp.Simproc := fun e => do
  match_expr e with
  | BEq.beq α _ lhs rhs =>
    match_expr α with
    | Bool => boolBeq lhs rhs
    | BitVec wExpr => bvBeq wExpr lhs rhs
    | _ => return .rfl
  | HAnd.hAnd α _ _ _ lhs rhs => bvAnd α lhs rhs
  | HAdd.hAdd α _ _ _ lhs rhs => bvAdd α lhs rhs
  | HSub.hSub α _ _ _ lhs rhs => bvSub α lhs rhs
  | HOr.hOr α _ _ _ lhs rhs => bvOr α lhs rhs
  | Neg.neg α _ val => bvNeg α val
  | HShiftRight.hShiftRight α β _ _ lhs rhs =>
    match_expr β with
    | BitVec _ => bvShiftRight α lhs rhs
    | Nat => bvShiftRightNat α lhs rhs
    | _ => return .rfl
  | HShiftLeft.hShiftLeft α β _ _ lhs rhs =>
    match_expr β with
    | BitVec _ => bvShiftLeft α lhs rhs
    | Nat => bvShiftLeftNat α lhs rhs
    | _ => return .rfl
  | HMul.hMul α _ _ _ lhs rhs => bvMul α lhs rhs
  | HDiv.hDiv α _ _  _ lhs rhs => bvUdiv α lhs rhs
  | HAppend.hAppend α β _ _ lhs rhs => bvAppend α β lhs rhs
  | BitVec.sshiftRight' nExpr mExpr lhs rhs => bvSshiftRight' nExpr mExpr lhs rhs
  | BitVec.extractLsb' wExpr startExpr lenExpr targetExpr =>
    extractLsb' wExpr startExpr lenExpr targetExpr
  | BitVec.cast nExpr mExpr hExpr targetExpr => bvCast nExpr mExpr hExpr targetExpr
  | BitVec.ult wExpr lhs rhs => ult wExpr lhs rhs
  | BitVec.signExtend oldWidthExpr newWidthExpr targetExpr =>
    signExtend oldWidthExpr newWidthExpr targetExpr
  | BitVec.setWidth oldWidthExpr newWidthExpr targetExpr =>
    setWidth oldWidthExpr newWidthExpr targetExpr
  | Bool.and lhs rhs => boolAnd lhs rhs
  | Bool.or lhs rhs => boolOr lhs rhs
  | cond α c thenExpr elseExpr => condSimplify e α c thenExpr elseExpr
  | Eq α lhs rhs =>
    match_expr α with
    | Bool => boolEqToBeq lhs rhs
    | _ => return .rfl
  | _ => return .rfl

public def rewriteDsimproc : Sym.DSimp.DSimproc := fun e => do
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    let some ⟨_, bv⟩ := Sym.getBitVecValue? e | return .rfl
    return .step <| ← Sym.share <| toExpr bv
  | _ => return .rfl

end Normalize
end Lean.Meta.Tactic.BVDecide
