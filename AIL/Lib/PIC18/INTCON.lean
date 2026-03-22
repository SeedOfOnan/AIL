-- AIL.Lib.PIC18.INTCON
-- PIC18 INTCON register and critical-section node builders.
--
-- INTCON (SFR 0xFF2, Access Bank) — Interrupt Control register.
--   Bit 7: GIE  — Global Interrupt Enable.  0 = all maskable interrupts disabled.
--   Bit 6: PEIE — Peripheral Interrupt Enable.  1 = peripheral interrupts enabled.
--
-- Critical section pattern (user-definable from existing primitives):
--   seq [h_disable_ints, body, h_enable_ints]
--
-- This is consistent with the AIL design principle: the language primitive set
-- is exactly what requires compiler knowledge of the hardware. A critical section
-- is expressible entirely from existing clearBit / setBit AbstractOps on a
-- peripheral bitField node — no new language primitive is needed.
--
-- Usage:
--   def myBuild : StoreM ... := do
--     let ic ← makeINTCON 0xFF2   -- PIC18 classic / Q71 INTCON address
--     -- wrap body in critical section:
--     let h_crit ← StoreM.node (.proc #[] #[]
--       (.seq #[ic.h_disable_ints, bodyHash, ic.h_enable_ints]) "my_critical")
--
-- intconAddr must be the full SFR address (e.g. 0xFF2 for classic PIC18 / Q71).
--
-- Safety note: BCF INTCON,GIE is not atomic with respect to a concurrently
-- completing RETFIE. If an ISR is mid-execution when GIE is cleared, it will
-- still complete (RETFIE restores GIE from the stack). This is correct PIC18
-- behavior — the critical section protects the body from interruption, not from
-- an already-in-progress ISR frame.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store

namespace AIL

structure INTCONInstance where
  h_INTCON       : Hash   -- peripheral node: INTCON SFR
  h_GIE          : Hash   -- bitField node:   INTCON bit 7
  h_PEIE         : Hash   -- bitField node:   INTCON bit 6
  h_disable_ints : Hash   -- proc [] []: clearBit GIE → BCF INTCON, 7
  h_enable_ints  : Hash   -- proc [] []: setBit   GIE → BSF INTCON, 7
  -- nodes field removed: hashes go into the calling StoreM context (AIL#18)

/-- Build INTCON register nodes for a PIC18 target.
    intconAddr: full SFR address of INTCON (0xFF2 for classic PIC18 and Q71).
    All nodes are inserted into the caller's StoreM context automatically. -/
def makeINTCON (intconAddr : UInt32) : StoreM INTCONInstance := do
  let h_INTCON ← StoreM.node (.peripheral .sfr intconAddr
    { readable := true, writable := true,
      sideEffectOnRead := false, sideEffectOnWrite := false, accessWidth := .w8 }
    "INTCON")

  let h_GIE  ← StoreM.node (.bitField h_INTCON 7 "GIE")
  let h_PEIE ← StoreM.node (.bitField h_INTCON 6 "PEIE")

  -- disable_ints: BCF INTCON, 7 — clear GIE, masking all maskable interrupts.
  let h_disable_ints ← StoreM.node (.proc #[] #[]
    (.atomic (.abstract .clearBit) #[] #[h_GIE]) "disable_ints")

  -- enable_ints: BSF INTCON, 7 — set GIE, re-enabling maskable interrupts.
  let h_enable_ints ← StoreM.node (.proc #[] #[]
    (.atomic (.abstract .setBit) #[] #[h_GIE]) "enable_ints")

  return { h_INTCON, h_GIE, h_PEIE, h_disable_ints, h_enable_ints }

end AIL
