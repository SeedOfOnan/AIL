-- AIL.Core.Types
-- AIL type system.
--
-- Every computation (proc) is a morphism: params → rets.
-- Status register bits are first-class Ty.bool in rets.
-- TargetConfig isolates target-specific numeric limits from Core types.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store

namespace AIL

-- ---------------------------------------------------------------------------
-- Target configuration
-- ---------------------------------------------------------------------------

structure TargetConfig where
  maxCallDepth : Nat
deriving Repr

-- ---------------------------------------------------------------------------
-- Type algebra
-- ---------------------------------------------------------------------------

inductive Ty : Type where
  | data   (space : AddrSpace) (width : Width)        : Ty
  | periph (space : AddrSpace) (sem   : AccessSemantics) : Ty
  | bool   : Ty
  | unit   : Ty
  /-- A callable proc.
      params, rets: typed formal inputs and outputs (may include Ty.bool for flags).
      maxBodyDepth: max additional call stack frames consumed transitively. -/
  | proc (params : List Ty) (rets : List Ty) (maxBodyDepth : Nat) : Ty
deriving Repr, BEq

/-- Map FormalKind to Ty. -/
def formalTy : FormalKind → Ty
  | .data space width => Ty.data space width
  | .bool             => Ty.bool
  | .unit             => Ty.unit

-- ---------------------------------------------------------------------------
-- Type environment
-- ---------------------------------------------------------------------------

abbrev TyEnv := Hash → Option Ty

private def resolveAll (env : TyEnv) (hs : Array Hash) : Option (List Ty) :=
  hs.toList.mapM env

-- ---------------------------------------------------------------------------
-- Proc body well-typedness
-- Defined before HasType because HasType.proc_ok references it.
-- ProcBodyOk does NOT reference HasType (only TyEnv).
-- ---------------------------------------------------------------------------

/-- ProcBodyOk cfg env body paramTys retTys maxD:
    body type-checks under cfg and env with the given interface and depth. -/
inductive ProcBodyOk (cfg : TargetConfig) (env : TyEnv) :
    ProcBody → List Ty → List Ty → Nat → Prop where

  /-- atomic: reads and writes must resolve in env.
      TODO: reads ⊆ params, writes ⊆ rets (full interface check).
      TODO: status flag outputs verified against target op descriptor. -/
  | atomic_ok
      (ref : OpRef) (reads writes : Array Hash)
      (readTys writeTys : List Ty)
      (hreads  : resolveAll env reads  = some readTys)
      (hwrites : resolveAll env writes = some writeTys) :
      ProcBodyOk cfg env
        (ProcBody.atomic ref reads writes)
        readTys writeTys 0

  /-- seq: all steps must resolve to proc types.
      maxBodyDepth is the maximum proc depth across steps.
      TODO: SSA wiring — shared formals connect steps explicitly.
      TODO: paramTys/retTys derived from outer proc interface. -/
  | seq_ok
      (steps   : Array Hash)
      (stepTys : List Ty)
      (paramTys retTys : List Ty)
      (maxD    : Nat)
      (hsteps  : steps.toList.mapM env = some stepTys)
      (hmaxD   : maxD = stepTys.foldl (fun acc t => match t with
                    | Ty.proc _ _ d => Nat.max acc d | _ => acc) 0) :
      ProcBodyOk cfg env (ProcBody.seq steps) paramTys retTys maxD

  /-- cond: test produces exactly one bool, branches have matching types. -/
  | cond_ok
      (test thenB elseB : Hash)
      (paramTys retTys : List Ty) (d : Nat)
      (htest  : env test  = some (Ty.proc [] [Ty.bool] 0))
      (hthenB : env thenB = some (Ty.proc paramTys retTys d))
      (helseB : env elseB = some (Ty.proc paramTys retTys d)) :
      ProcBodyOk cfg env
        (ProcBody.cond test thenB elseB) paramTys retTys d

  /-- loop: params[0] is the bound (any data type); body is a proc. -/
  | loop_ok
      (body : Hash)
      (space : AddrSpace) (w : Width)
      (paramTys retTys : List Ty) (d : Nat)
      (hbound : paramTys.head? = some (Ty.data space w))
      (hbody  : env body = some (Ty.proc paramTys retTys d)) :
      ProcBodyOk cfg env (ProcBody.loop body) paramTys retTys d

  /-- call: args type-match callee params; retBinds type-match callee rets.
      Stack safety: callDepth + 1 + callee.maxBodyDepth ≤ maxCallDepth. -/
  | call_ok
      (callee : Hash) (args retBinds : Array Hash) (callDepth : UInt8)
      (paramTys retTys : List Ty) (d : Nat)
      (hcallee   : env callee    = some (Ty.proc paramTys retTys d))
      (hargs     : resolveAll env args     = some paramTys)
      (hretBinds : resolveAll env retBinds = some retTys)
      (hdepth    : callDepth.toNat + 1 + d ≤ cfg.maxCallDepth) :
      ProcBodyOk cfg env
        (ProcBody.call callee args retBinds callDepth)
        paramTys retTys
        (callDepth.toNat + 1 + d)

  /-- intrinsic: reads and writes must resolve. -/
  | intrinsic_ok
      (instructions : Array String)
      (reads writes  : Array Hash) (obligations : Array String)
      (readTys writeTys : List Ty)
      (hreads  : resolveAll env reads  = some readTys)
      (hwrites : resolveAll env writes = some writeTys) :
      ProcBodyOk cfg env
        (ProcBody.intrinsic instructions reads writes obligations)
        readTys writeTys 0

-- ---------------------------------------------------------------------------
-- Well-typedness relation
-- ---------------------------------------------------------------------------

inductive HasType (cfg : TargetConfig) (env : TyEnv) : Node → Ty → Prop where

  | data_ok (space : AddrSpace) (w : Width) (addr : UInt32) (label : String) :
      HasType cfg env (Node.data space w addr label) (Ty.data space w)

  | periph_ok (space : AddrSpace) (addr : UInt32) (sem : AccessSemantics) (label : String) :
      HasType cfg env (Node.peripheral space addr sem label) (Ty.periph space sem)

  | formal_ok (uid : UInt64) (kind : FormalKind) :
      HasType cfg env (Node.formal uid kind) (formalTy kind)

  | proc_ok
      (params rets : Array Hash) (body : ProcBody) (label : String)
      (paramTys retTys : List Ty) (maxD : Nat)
      (hparams : resolveAll env params = some paramTys)
      (hrets   : resolveAll env rets   = some retTys)
      (hbody   : ProcBodyOk cfg env body paramTys retTys maxD) :
      HasType cfg env
        (Node.proc params rets body label)
        (Ty.proc paramTys retTys maxD)

-- ---------------------------------------------------------------------------
-- Computable type inference
--
-- inferBodyDepth is defined first (uses env only, does not call inferTy).
-- inferTy is defined after (calls inferBodyDepth).
-- ---------------------------------------------------------------------------

def inferBodyDepth (cfg : TargetConfig) (env : TyEnv) (b : ProcBody) : Option Nat :=
  match b with

  | ProcBody.atomic _ reads writes => do
      let _ ← resolveAll env reads
      let _ ← resolveAll env writes
      some 0

  | ProcBody.seq steps => do
      let stepTys ← steps.toList.mapM env
      let maxD := stepTys.foldl (fun acc t => match t with
        | Ty.proc _ _ d => Nat.max acc d | _ => acc) 0
      some maxD

  | ProcBody.cond test thenB elseB => do
      guard (env test == some (Ty.proc [] [Ty.bool] 0))
      match ← env thenB, ← env elseB with
      | Ty.proc ps r d, Ty.proc ps' r' d' =>
          guard (ps == ps' && r == r' && d == d')
          some d
      | _, _ => none

  | ProcBody.loop body => do
      match ← env body with
      | Ty.proc _ _ d => some d
      | _             => none

  | ProcBody.call callee args retBinds callDepth => do
      match ← env callee with
      | Ty.proc paramTys retTys d =>
          let argTys     ← resolveAll env args
          let retBindTys ← resolveAll env retBinds
          guard (argTys == paramTys)
          guard (retBindTys == retTys)
          let total := callDepth.toNat + 1 + d
          if total ≤ cfg.maxCallDepth then some total else none
      | _ => none

  | ProcBody.intrinsic _ reads writes _ => do
      let _ ← resolveAll env reads
      let _ ← resolveAll env writes
      some 0

def inferTy (cfg : TargetConfig) (env : TyEnv) (n : Node) : Option Ty :=
  match n with
  | Node.data space w _ _      => some (Ty.data space w)
  | Node.peripheral space _ sem _ => some (Ty.periph space sem)
  | Node.formal _ kind         => some (formalTy kind)
  | Node.proc params rets body _ => do
      let paramTys ← resolveAll env params
      let retTys   ← resolveAll env rets
      let maxD     ← inferBodyDepth cfg env body
      some (Ty.proc paramTys retTys maxD)

-- ---------------------------------------------------------------------------
-- Soundness / completeness (sorry'd — mutual inductive makes proofs non-trivial)
-- ---------------------------------------------------------------------------

theorem inferTy_sound (cfg : TargetConfig) (env : TyEnv) (n : Node) (t : Ty)
    (h : inferTy cfg env n = some t) : HasType cfg env n t := by
  sorry  -- TODO: prove by cases on n

theorem inferTy_complete (cfg : TargetConfig) (env : TyEnv) (n : Node) (t : Ty)
    (h : HasType cfg env n t) : inferTy cfg env n = some t := by
  sorry  -- TODO: prove

-- ---------------------------------------------------------------------------
-- Store-wide type checking
-- ---------------------------------------------------------------------------

def checkStore (cfg : TargetConfig) (s : Store) : Except (TyEnv × Hash) TyEnv :=
  let arr : Array (Hash × Node) := s
  Array.foldlM (fun env (pair : Hash × Node) =>
    let (h, n) := pair
    match inferTy cfg env n with
    | none   => throw (env, h)
    | some t => pure (fun h' => if h' == h then some t else env h')
  ) (fun _ => none) arr

end AIL
