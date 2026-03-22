-- AIL.Core.Types
-- AIL type system.
--
-- Every computation (proc) is a morphism: params → rets.
-- Status register bits are first-class Ty.bool in rets.
-- TargetConfig isolates target-specific numeric limits from Core types.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store
import AIL.Core.Diagnostic

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
  | data   (space : AddrSpace) (width : Width)           : Ty
  | periph (space : AddrSpace) (sem   : AccessSemantics) : Ty
  | bool   : Ty
  | unit   : Ty
  /-- A statically-allocated fixed-size array.
      elemWidth: element size. count: number of elements.
      Accessed via AbstractOp.indexLoad / indexStore (PIC18: FSR indirect). -/
  | array (elemWidth : Width) (count : UInt32) : Ty
  /-- never: the bottom type. A proc returning Never does not return.
      The compiler must not emit code after a call to such a proc.
      Satisfies any return type context (bottom of the subtype lattice).
      Used for: entry(reset) implicit return, user-defined panic. -/
  | never  : Ty
  /-- A callable proc.
      params, rets: typed formal inputs and outputs (may include Ty.bool for flags).
      maxBodyDepth: max additional call stack frames consumed transitively.
      If rets = [Ty.never], the proc does not return. -/
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

  /-- forever: body must resolve to a proc type. No exit condition. -/
  | forever_ok
      (body : Hash)
      (paramTys retTys : List Ty) (d : Nat)
      (hbody : env body = some (Ty.proc paramTys retTys d)) :
      ProcBodyOk cfg env (ProcBody.forever body) paramTys retTys d

  /-- whileLoop: cond must be proc [] [Bool] 0; body must be a proc. -/
  | whileLoop_ok
      (cond body : Hash)
      (paramTys retTys : List Ty) (d : Nat)
      (hcond : env cond = some (Ty.proc [] [Ty.bool] 0))
      (hbody : env body = some (Ty.proc paramTys retTys d)) :
      ProcBodyOk cfg env (ProcBody.whileLoop cond body) paramTys retTys d

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
      (reads writes  : Array Hash) (obligations : Array String) (fsrUse : Array UInt8)
      (readTys writeTys : List Ty)
      (hreads  : resolveAll env reads  = some readTys)
      (hwrites : resolveAll env writes = some writeTys) :
      ProcBodyOk cfg env
        (ProcBody.intrinsic instructions reads writes obligations fsrUse)
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

  | staticArray_ok (space : AddrSpace) (w : Width) (addr : UInt32)
                   (count : UInt32) (label : String) :
      HasType cfg env (Node.staticArray space w addr count label) (Ty.array w count)

  | bitField_ok (register : Hash) (bitPos : UInt8) (label : String) :
      HasType cfg env (Node.bitField register bitPos label) Ty.bool

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

  | ProcBody.forever body => do
      match ← env body with
      | Ty.proc _ _ d => some d
      | _             => none

  | ProcBody.whileLoop cond body => do
      guard (env cond == some (Ty.proc [] [Ty.bool] 0))
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

  | ProcBody.intrinsic _ reads writes _ _ => do
      let _ ← resolveAll env reads
      let _ ← resolveAll env writes
      some 0

def inferTy (cfg : TargetConfig) (env : TyEnv) (n : Node) : Option Ty :=
  match n with
  | Node.data space w _ _              => some (Ty.data space w)
  | Node.peripheral space _ sem _      => some (Ty.periph space sem)
  | Node.formal _ kind                 => some (formalTy kind)
  | Node.staticArray _ w _ count _     => some (Ty.array w count)
  | Node.bitField _ _ _                => some Ty.bool
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

/-- Extract the label of a node in the store.  Returns "(unknown)" if the hash
    is absent or the node has no label field (e.g. formal nodes use uid). -/
private def nodeLabel (s : Store) (h : Hash) : String :=
  match s.lookup h with
  | none => "(unknown)"
  | some node => match node with
      | Node.data _ _ _ lbl          => lbl
      | Node.peripheral _ _ _ lbl    => lbl
      | Node.formal uid _            => s!"formal_{uid}"
      | Node.staticArray _ _ _ _ lbl => lbl
      | Node.bitField _ _ lbl        => lbl
      | Node.proc _ _ _ lbl          => lbl

/-- Type-check all nodes in the store.
    Returns the completed TyEnv on success, or a Diagnostic on the first
    node that fails type inference (R5.3 — no cascade errors). -/
def checkStore (cfg : TargetConfig) (s : Store) : Except Diagnostic TyEnv :=
  let arr : Array (Hash × Node) := s
  Array.foldlM (fun env (pair : Hash × Node) =>
    let (h, n) := pair
    match inferTy cfg env n with
    | none   => throw { kind := .TypeCheckFailure, severity := .error,
                        nodeHash := h,
                        message := s!"type inference failed for node '{nodeLabel s h}'",
                        fix := none }
    | some t => pure (fun h' => if h' == h then some t else env h')
  ) (fun _ => none) arr

-- ---------------------------------------------------------------------------
-- read_clears warning pass
--
-- Scans the store for atomic .load operations on peripherals with
-- sideEffectOnRead = true (i.e. read_clears registers) where the result
-- is not explicitly acknowledged.
--
-- The agent suppresses the warning by using AbstractOp.loadDiscard instead
-- of AbstractOp.load — the Store-level equivalent of `_ = RCREG`.
--
-- Returns one warning string per offending node (hash + label).
-- Does not fail: warnings are informational, not errors.
-- ---------------------------------------------------------------------------

/-- Return a Diagnostic for each node that reads a read_clears peripheral
    via AbstractOp.load without explicit discard acknowledgement.
    Nodes using AbstractOp.loadDiscard are silently accepted.
    Each diagnostic includes a UseLoadDiscard fix suggestion (R5.5). -/
def readClearsWarnings (s : Store) : Array Diagnostic :=
  (s : Array (Hash × Node)).foldl (fun acc (pair : Hash × Node) =>
    let (h, n) := pair
    match n with
    | Node.proc _ _ (ProcBody.atomic (.abstract .load) reads _) label =>
        let offenders := reads.filterMap fun rh =>
          match s.lookup rh with
          | some (Node.peripheral _ _ sem lbl) =>
              if sem.sideEffectOnRead then some lbl else none
          | _ => none
        if offenders.isEmpty then acc
        else
          let regs := String.intercalate ", " offenders.toList
          acc.push { kind := .ReadClearsUnacked, severity := .warning,
                     nodeHash := h,
                     message := s!"node '{label}' reads read_clears register(s) [{regs}] via .load — use .loadDiscard to acknowledge intentional discard",
                     fix := some (.useLoadDiscard h) }
    | _ => acc
  ) #[]

end AIL
