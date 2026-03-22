-- AIL.Analysis.WREGCheck
-- Static WREG use/define conflict checker (AIL#22).
--
-- BACKGROUND:
--   PIC18 has a single 8-bit accumulator (WREG) that is an implicit operand
--   for most ALU instructions. In the abstract op model, WREG threading is
--   explicit only when a proc declares FormalKind.reg .wreg in its params/rets
--   (AIL#21). For ops that use WREG implicitly, the checker verifies that no
--   seq step clobbers a live WREG value before it is consumed.
--
-- WREG EFFECT CLASSIFICATION:
--   Each AbstractOp has one of four effects on WREG:
--     defines           — op writes WREG (e.g. MOVF f,W; MOVLW k; FSR+INDF read)
--     consumes          — op reads WREG as input (e.g. MOVWF f; ADDWF f,F)
--     consumesAndDefines — op reads WREG as input and writes WREG as output
--                         (e.g. ADDLW k; XORLW k; ANDLW k; also indexStore
--                          which clobbers WREG during index computation)
--     none              — op does not touch WREG
--                         (e.g. bit-field ops: BSF/BCF/BTFSS operate on f directly)
--
-- CHECKING RULE (seq bodies only):
--   Walk the steps of a ProcBody.seq. Maintain a boolean `wregLive` (true after
--   a `defines` or `consumesAndDefines` step). A WREGClobber diagnostic is emitted
--   when a `defines` or `consumesAndDefines` step is encountered while `wregLive`
--   is already true — the previous WREG value was never consumed.
--
-- SCOPE:
--   Only ProcBody.seq is checked. ProcBody.atomic is a single op — no conflict
--   possible. Nested seq bodies are checked recursively via the store.
--   Other body forms (cond, loop, forever, whileLoop, call, intrinsic) are
--   skipped: their WREG discipline is enforced at call boundaries or is
--   target-specific (intrinsic).
--
-- TIER: Tier 1 (PIC18-specific semantics). Lives in AIL.Analysis, not Core.

import AIL.Core.AST
import AIL.Core.Store
import AIL.Core.Diagnostic

namespace AIL.WREGCheck

open AIL

-- ---------------------------------------------------------------------------
-- WREG effect classification
-- ---------------------------------------------------------------------------

/-- The effect of an AbstractOp on WREG. -/
inductive WREGEffect where
  /-- Op writes WREG; any previous WREG value is replaced. -/
  | defines
  /-- Op reads WREG as an input operand; WREG is not modified. -/
  | consumes
  /-- Op reads WREG as input and writes WREG as output. -/
  | consumesAndDefines
  /-- Op does not touch WREG. -/
  | none
deriving Repr, BEq, DecidableEq

/-- Classify the WREG effect of an AbstractOp.
    Conservative for ops where the destination (W or F) is not encoded in
    the abstract op — those ops are classified as consumesAndDefines. -/
def wregEffect : AbstractOp → WREGEffect
  -- Ops that load a value into WREG (defines WREG, does not consume it)
  | .load        => .defines
  | .loadDiscard => .defines
  | .movImm _    => .defines
  | .indexLoad   => .defines   -- net effect: WREG ← array[index]
  -- Ops that read WREG as an input (consume WREG, do not redefine it)
  | .store       => .consumes
  | .add         => .consumes  -- ADDWF f,F: f ← WREG + f; WREG unchanged
  | .sub         => .consumes  -- SUBWF f,F: f ← f - WREG; WREG unchanged
  | .mul         => .consumes
  | .and         => .consumes  -- ANDWF f,F: f ← WREG & f; WREG unchanged
  | .or          => .consumes  -- IORWF f,F: f ← WREG | f; WREG unchanged
  | .xor         => .consumes  -- XORWF f,F: f ← WREG ^ f; WREG unchanged
  | .compare     => .consumes  -- CPFSEQ/SUBWF (compare): reads WREG
  -- Ops that read WREG and write WREG (consume and redefine)
  | .addImm _    => .consumesAndDefines  -- ADDLW k: WREG ← WREG + k
  | .xorImm _    => .consumesAndDefines  -- XORLW k: WREG ← WREG ^ k
  | .andImm _    => .consumesAndDefines  -- ANDLW k: WREG ← WREG & k
  | .indexStore  => .consumesAndDefines  -- clobbers WREG during index arith
  -- Ops that do not involve WREG
  | .testBit     => .none  -- BTFSS/BTFSC: tests a bit in f; no WREG access
  | .setBit      => .none  -- BSF: sets a bit in f
  | .clearBit    => .none  -- BCF: clears a bit in f
  | .not         => .none  -- COMF f,F: complements f in place
  | .shiftL      => .none  -- RLCF f,F: rotates f in place
  | .shiftR      => .none  -- RRCF f,F: rotates f in place

-- ---------------------------------------------------------------------------
-- Checker
-- ---------------------------------------------------------------------------

/-- True if the WREGEffect defines (or redefines) WREG. -/
private def isDefining : WREGEffect → Bool
  | .defines | .consumesAndDefines => true
  | .consumes | .none              => false

/-- True if the WREGEffect consumes WREG. -/
private def isConsuming : WREGEffect → Bool
  | .consumes | .consumesAndDefines => true
  | .defines  | .none               => false

/-- Classify the WREG effect of a ProcBody.atomic step.
    Returns .none for non-abstract ops (intrinsics manage WREG themselves). -/
private def atomicEffect : ProcBody → WREGEffect
  | .atomic (.abstract op) _ _ => wregEffect op
  | _                          => .none

/-- Check a single ProcBody.seq for WREG clobber conflicts.
    Returns one Diagnostic per clobbered-before-consumed occurrence.
    Recursive: seq steps that are themselves seq procs are checked too. -/
partial def checkWREGSeq (store : Store) (seqHash : Hash) : Array Diagnostic :=
  match store.lookup seqHash with
  | none => #[]
  | some node =>
  match node with
  | .proc _ _ (.seq steps) _ =>
      -- Walk steps; track whether WREG is live (defined but not yet consumed).
      let (diags, _) := steps.foldl (fun (acc : Array Diagnostic × Bool) stepHash =>
        let (diags, wregLive) := acc
        -- Recurse into nested seq procs.
        let nested := checkWREGSeq store stepHash
        let diags  := diags ++ nested
        -- Classify this step's WREG effect.
        let eff := match store.lookup stepHash with
          | some (.proc _ _ body _) => atomicEffect body
          | _                       => .none
        -- A clobber occurs when WREG is live and this step redefines it
        -- without first consuming it.
        let clobber := wregLive && isDefining eff && !isConsuming eff
        let diags := if clobber then
          diags.push {
            kind     := .WREGClobber,
            severity := .warning,
            nodeHash := stepHash,
            message  := s!"WREG clobbered: step defines WREG while a previous definition is still live (unconsumed)",
            fix      := none }
        else diags
        -- Update liveness: WREG is live after a define; not live after consume.
        let wregLive' :=
          if isConsuming eff then false
          else if isDefining eff then true
          else wregLive
        (diags, wregLive')
      ) (#[], false)
      diags
  | .proc _ _ (.atomic _ _ _) _ =>
      -- Atomic procs have a single op — no seq to check.
      #[]
  | _ => #[]

end AIL.WREGCheck
