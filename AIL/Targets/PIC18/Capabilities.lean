-- AIL.Targets.PIC18.Capabilities
-- PIC18 backend capability record (AIL#17).
--
-- Co-located with Emitter.lean.  When you add or remove a match arm in
-- Emitter.lean, update this record to match.  The two files together form
-- the authoritative source of truth for what the PIC18 backend can compile.
--
-- TIER: Tier 1 only.  No Core module may import this file.

import AIL.Core.Capability

namespace AIL.PIC18

open AIL

/-- Capability record for the PIC18 backend.
    Derived from the match arms in AIL.Targets.PIC18.Emitter.
    Update this declaration whenever Emitter.lean changes. -/
def pic18Capabilities : CapabilityRecord where
  target := "pic18"

  procBodyForms := #[
    "atomic",
    "seq",
    "cond",
    "loop",
    "forever",
    "whileLoop",
    "call",
    "intrinsic"
  ]

  abstractOps := #[
    "add", "sub", "mul",
    "and", "or", "xor", "not",
    "shiftL", "shiftR",
    "testBit", "setBit", "clearBit",
    "load", "loadDiscard", "store",
    "compare",
    "indexLoad", "indexStore",
    "xorImm", "addImm", "andImm", "movImm",
    "compareImm"
  ]

  nodeTypes := #[
    "data", "peripheral", "staticArray", "bitField", "formal", "proc"
  ]

  limitations := #[
    "bankedRAM: only Access Bank 0x00-0xFF; BSR register not managed",
    "boolConditionProtocol: skip-style; testBit/compare emit skip insns; flag-producing ops supported via emitFlagSkip (AIL#31); generalised bool proc not yet wired",
    "loopBoundDecrement: 8-bit only; 16/32-bit bounds need multi-byte decrement",
    "callSpecialisation: formals not substituted at call sites; shared memory convention only",
    "subroutineOrdering: callees emitted inline at call site, not scheduled after caller RETURN",
    "ivtHardwareSection: hardware IVT section not yet emitted (psect at IVTBASE / 0x0008 / 0x0018)"
  ]

end AIL.PIC18
