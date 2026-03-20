-- AIL.Core.AST
-- Node definitions for the content-addressed store.
--
-- DESIGN (revised from original):
-- Every computation is a morphism: it takes typed inputs (params) and produces
-- typed outputs (rets). This unifies single instructions, sequences, and
-- functions — they differ only in granularity (ProcBody variant), not in
-- semantic category.
--
-- Status register bits are first-class Ty.bool-kinded formals in rets, not
-- implicit side effects. Agents have direct access to carry, zero, overflow,
-- and negative flags as typed data — information that high-level languages
-- discard entirely.
--
-- NODE TAXONOMY:
--   Locations  : data, peripheral, formal   (typed values, not computations)
--   Computation: proc                       (the single computation node type)
--
-- All computations share the same interface:
--   params : Array Hash   -- formal inputs  (data/bool/unit formals)
--   rets   : Array Hash   -- formal outputs (data/bool/unit formals)
--   body   : ProcBody     -- what the proc computes
--
-- Wiring between procs in a seq is by hash identity (SSA-style):
-- if formal h appears in step[i].rets and step[j].params, they are connected.

import AIL.Core.HashPrim

namespace AIL

-- ---------------------------------------------------------------------------
-- Supporting types
-- ---------------------------------------------------------------------------

/-- Address space. PIC18 is Harvard: data and program memory are separate.
    An address without its space is ambiguous and must not exist in the AST. -/
inductive AddrSpace where
  | data    -- RAM (Access RAM, General Purpose Registers)
  | program -- Flash (read via TBLRD on PIC18)
  | sfr     -- Special Function Registers (peripheral control)
deriving Repr, BEq, DecidableEq

/-- Bit width of a data value or memory location. -/
inductive Width where
  | w8 | w16 | w32
deriving Repr, BEq, DecidableEq

/-- Peripheral access semantics. -/
structure AccessSemantics where
  readable          : Bool
  writable          : Bool
  sideEffectOnRead  : Bool
  sideEffectOnWrite : Bool
  accessWidth       : Width
deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Formal kinds
--
-- Ty lives in Types.lean, which imports AST.lean. To avoid a circular
-- dependency, formals carry FormalKind — a simpler classification that
-- Types.lean maps to Ty.
-- ---------------------------------------------------------------------------

/-- The kind of a formal parameter or return value.
    Formals with kind = data will be bound to data/peripheral nodes at call sites.
    Formals with kind = bool carry status register outputs (C, Z, OV, N, DC, ...). -/
inductive FormalKind where
  | data (space : AddrSpace) (width : Width)  -- binds to a data or peripheral node
  | bool                                       -- a status flag or boolean condition
  | unit                                       -- a computation producing no value
deriving Repr, BEq, DecidableEq

-- ---------------------------------------------------------------------------
-- Abstract operations
-- Core abstract operations. Tier-neutral: no PIC18-specific instruction names.
-- The emitter maps these to target instructions and declares which status
-- formals each produces (target-specific).
-- ---------------------------------------------------------------------------

inductive AbstractOp where
  | add | sub | mul
  | and | or | xor | not
  | shiftL | shiftR
  | testBit
  | load | store
  | compare
deriving Repr, BEq, DecidableEq

/-- Operation reference: abstract core op or a user-defined intrinsic (by hash). -/
inductive OpRef where
  | abstract  : AbstractOp → OpRef
  | intrinsic : Hash → OpRef   -- hash of a proc node with ProcBody.intrinsic body
deriving Repr

-- ---------------------------------------------------------------------------
-- Proc body
--
-- ProcBody specifies WHAT a proc computes. The proc node wraps it with the
-- typed params/rets interface. Every ProcBody variant is a computation;
-- the containing proc declares the full input/output signature.
-- ---------------------------------------------------------------------------

/-- The computation body of a proc node. -/
inductive ProcBody where

  /-- atomic: a single abstract operation.
      reads  are hashes of formal/data/peripheral nodes this op reads.
      writes are hashes of formal/data/peripheral nodes this op writes.
      reads ⊆ containing proc's params (plus accessible concrete nodes).
      writes ⊆ containing proc's rets (plus accessible concrete nodes).
      Status flag formals produced by this op appear in the proc's rets. -/
  | atomic
      (ref    : OpRef)
      (reads  : Array Hash)
      (writes : Array Hash)

  /-- seq: sequential composition.
      Each step is a hash of a proc node. Steps are ordered: side effects
      must not be reordered. Wiring between steps is by shared formal hash:
      if formal h appears in step[i].rets and step[j].params (j > i),
      step[i]'s output on h flows into step[j]'s input on h. -/
  | seq
      (steps : Array Hash)

  /-- cond: conditional execution.
      test  is a hash of a proc whose rets[0] is a bool formal (the condition).
      thenB is a hash of a proc executed when the condition is true.
      elseB is a hash of a proc executed when the condition is false.
      thenB and elseB must have matching params and rets types. -/
  | cond
      (test  : Hash)
      (thenB : Hash)
      (elseB : Hash)

  /-- loop: bounded iteration.
      The containing proc's params[0] must be a data formal (the loop bound).
      The bound is decremented each iteration; the loop exits when it reaches 0.
      body is a hash of a proc executed each iteration.
      TODO: termination witness — a proof that the bound strictly decreases. -/
  | loop
      (body : Hash)

  /-- call: invoke a proc at this call site, with explicit argument binding.
      callee   is a hash of a proc node.
      args[i]  is the hash of the actual node bound to callee.params[i].
               May be a data/peripheral node or one of the calling proc's own formals.
      retBinds[i] is the hash of the node where callee.rets[i] is written.
               May be a data/peripheral node or one of the calling proc's own rets.
      callDepth is the hardware call stack depth at this call site.
      Stack safety invariant: callDepth + 1 + callee.maxBodyDepth ≤ cfg.maxCallDepth.
      Specialization: the emitter substitutes args/retBinds for callee's formals,
      producing a specialized subroutine for each distinct (callee, args, retBinds)
      tuple. Identical tuples share the same specialization via content-addressing. -/
  | call
      (callee    : Hash)
      (args      : Array Hash)
      (retBinds  : Array Hash)
      (callDepth : UInt8)

  /-- intrinsic: target-specific inline assembly.
      instructions are the target instruction strings (strings for now;
                   will migrate to typed Insn nodes once the emitter stabilises).
      reads  are hashes of formal/data/peripheral nodes this intrinsic reads.
      writes are hashes of formal/data/peripheral nodes this intrinsic writes.
      obligations are agent-asserted correctness strings. -/
  | intrinsic
      (instructions : Array String)
      (reads        : Array Hash)
      (writes       : Array Hash)
      (obligations  : Array String)

deriving Repr

-- ---------------------------------------------------------------------------
-- Nodes
-- ---------------------------------------------------------------------------

/-- An AIL node.

    Every node is either a location (data, peripheral, formal) or a
    computation (proc). Locations carry typed values at fixed or abstract
    addresses. Computations are morphisms: params → rets.

    Content-addressing: each node is identified by the hash of its canonical
    byte encoding (see Hash.lean). Labels are excluded from identity so
    renaming a node produces no new hash. -/
inductive Node where

  /-- data: a concrete memory location.
      addrSpace and width are part of identity; label is metadata only. -/
  | data
      (addrSpace : AddrSpace)
      (width     : Width)
      (address   : UInt32)
      (label     : String)   -- excluded from identity

  /-- peripheral: a memory-mapped hardware register.
      Full access semantics are part of identity; label is metadata only. -/
  | peripheral
      (addrSpace : AddrSpace)
      (address   : UInt32)
      (semantics : AccessSemantics)
      (label     : String)   -- excluded from identity

  /-- formal: a typed placeholder.
      uid is part of identity — two formals with the same kind but different
      uids are distinct nodes with distinct hashes. Agents generate fresh uids.
      Formals appear in proc params/rets and in atomic op reads/writes.
      At a call site (ProcBody.call), each formal in the callee is substituted
      with an actual node (args[i] for params, retBinds[i] for rets). -/
  | formal
      (uid  : UInt64)
      (kind : FormalKind)

  /-- proc: a parameterized computation — the single computation node type.
      params  are hashes of formal nodes (typed inputs).
      rets    are hashes of formal nodes (typed outputs, including status formals).
      body    specifies what the proc computes (see ProcBody).
      label   is agent-assigned metadata; excluded from identity.

      Well-typedness obligations (enforced by Types.lean):
      - All params hashes must refer to formal nodes in the store.
      - All rets hashes must refer to formal nodes in the store.
      - The body must type-check under an environment containing the formals.
      - For ProcBody.call: args and retBinds must type-match callee's params/rets.
      - For ProcBody.loop: params[0] must be a data-kinded formal (the bound). -/
  | proc
      (params : Array Hash)
      (rets   : Array Hash)
      (body   : ProcBody)
      (label  : String)      -- excluded from identity

deriving Repr

end AIL
