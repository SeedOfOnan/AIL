-- AIL.Lib.PIC18.RingBuf
-- Generic power-of-2 ring buffer for PIC18 (typed ISA node version).
--
-- makeRingBuf builds all Store nodes for a ring buffer:
--   head, tail  : UInt8 index counters
--   data        : staticArray of bytes (capacity must be a power of 2)
--   temp        : UInt8 scratch byte used by push to save WREG
--   is_full     : proc [] [Bool] — condition: (tail+1)&mask == head
--   push        : proc [] []    — writes WREG to buf[tail], advances tail
--
-- The push operation is expressed as ProcBody.seq of single-instruction ISA
-- nodes (AIL issue #9). Each step is individually hashed and stored, giving
-- typed, composable, hash-deduplicable single-instruction granularity.
--
-- Push instruction sequence:
--   movwf temp         ; save received byte before FSR0 clobbers WREG
--   lfsr  0, data      ; FSR0 = base address of buf
--   movf  tail, w      ; WREG = tail index
--   addwf FSR0L, f     ; FSR0L += tail  →  FSR0 points at buf[tail]
--   movf  temp, w      ; WREG = saved received byte (restore)
--   movwf INDF0        ; buf[tail] = received byte
--   incf  tail, f      ; tail++
--   movlw mask         ; WREG = capacity-1
--   andwf tail, f      ; tail &= mask  (mod capacity, wrap)
--
-- Callers invoke makeRingBuf inside a StoreM do-block (AIL#18):
--   def myBuild : StoreM ... := do
--     let rb ← makeRingBuf ...
--     -- rb.h_push, rb.h_head, etc. are now available
--
-- boolUid must be unique across all formals in the containing Store.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store
import AIL.Targets.PIC18.ISA

namespace AIL

open AIL.PIC18

structure RingBufInstance where
  h_head    : Hash
  h_tail    : Hash
  h_data    : Hash
  h_temp    : Hash
  h_is_full : Hash
  h_push    : Hash
  -- nodes field removed: all nodes go into the calling StoreM context (AIL#18)

/-- Build a ring buffer of `capacity` bytes.
    headAddr, tailAddr: addresses of the head and tail index bytes.
    dataAddr: base address of the buffer body (staticArray).
    tempAddr: address of a scratch byte (used by push to save WREG).
    capacity: number of elements; must be a power of 2.
    boolUid: unique UInt64 for the bool formal in is_full's rets.
    pfx: label prefix for all nodes (metadata only).
    All nodes are inserted into the caller's StoreM context automatically. -/
def makeRingBuf
    (headAddr tailAddr dataAddr tempAddr : UInt32)
    (capacity : UInt32) (boolUid : UInt64) (pfx : String)
    : StoreM RingBufInstance := do
  let mask := capacity - 1
  -- -------------------------------------------------------------------------
  -- Location nodes
  -- -------------------------------------------------------------------------
  let h_head ← StoreM.node (.data .data .w8 headAddr (pfx ++ "_head"))
  let h_tail ← StoreM.node (.data .data .w8 tailAddr (pfx ++ "_tail"))
  let h_data ← StoreM.node (.staticArray .data .w8 dataAddr capacity (pfx ++ "_data"))
  let h_temp ← StoreM.node (.data .data .w8 tempAddr (pfx ++ "_temp"))
  -- -------------------------------------------------------------------------
  -- Bool formal for is_full return
  -- -------------------------------------------------------------------------
  let h_bool ← StoreM.node (.formal boolUid .bool)
  -- -------------------------------------------------------------------------
  -- is_full: (tail+1) & mask == head  →  CPFSEQ skips when buffer is full.
  --
  -- Four typed atomic steps:
  --   1. MOVF tail, W   — load tail index into WREG  (AbstractOp.load)
  --   2. ADDLW 1        — WREG += 1                  (AbstractOp.addImm 1)
  --   3. ANDLW mask     — WREG &= mask               (AbstractOp.andImm mask)
  --   4. CPFSEQ head    — skip if head == WREG (full) (AbstractOp.compare)
  -- -------------------------------------------------------------------------
  let h_if_load_tail ← StoreM.node (.proc #[h_tail] #[]
    (.atomic (.abstract .load) #[h_tail] #[]) (pfx ++ "_if_load_tail"))
  let h_if_add1 ← StoreM.node (.proc #[] #[]
    (.atomic (.abstract (.addImm 1)) #[] #[]) (pfx ++ "_if_add1"))
  let h_if_and_mask ← StoreM.node (.proc #[] #[]
    (.atomic (.abstract (.andImm (UInt8.ofNat mask.toNat))) #[] #[])
    (pfx ++ s!"_if_and_{mask.toNat}"))
  let h_if_cmp_head ← StoreM.node (.proc #[h_head] #[h_bool]
    (.atomic (.abstract .compare) #[h_head] #[]) (pfx ++ "_if_cmp_head"))
  let h_is_full ← StoreM.node (.proc #[] #[h_bool]
    (.seq #[h_if_load_tail, h_if_add1, h_if_and_mask, h_if_cmp_head])
    (pfx ++ "_is_full"))
  -- -------------------------------------------------------------------------
  -- push: write WREG (received byte) to buf[tail], then advance tail.
  --
  -- Expressed as ProcBody.seq of single-instruction ISA nodes (AIL issue #9).
  -- Each step is a Node.proc #[] #[] (type Ty.proc [] [] 0).
  -- -------------------------------------------------------------------------
  -- Step 1: MOVWF temp — save received byte before FSR0 clobbers WREG
  let h_ps1 ← StoreM.node (nodeMovwf h_temp (pfx ++ "_push_s1_movwf_temp"))
  -- Step 2: LFSR 0, data — FSR0 = base address of buf
  let h_ps2 ← StoreM.node (nodeLfsr0 h_data (pfx ++ "_push_s2_lfsr0_data"))
  -- Step 3: MOVF tail, W — WREG = tail index
  let h_ps3 ← StoreM.node (nodeMovf_w h_tail (pfx ++ "_push_s3_movf_tail"))
  -- Step 4: ADDWF FSR0L, F — FSR0L += tail  →  FSR0 = &buf[tail]
  let h_ps4 ← StoreM.node (nodeAddwf_FSR0L (pfx ++ "_push_s4_addwf_fsr0l"))
  -- Step 5: MOVF temp, W — WREG = saved received byte (restore after FSR0 setup)
  let h_ps5 ← StoreM.node (nodeMovf_w h_temp (pfx ++ "_push_s5_movf_temp"))
  -- Step 6: MOVWF INDF0 — buf[tail] = received byte
  let h_ps6 ← StoreM.node (nodeMovwf_INDF0 (pfx ++ "_push_s6_movwf_indf0"))
  -- Step 7: INCF tail, F — tail++
  let h_ps7 ← StoreM.node (nodeIncf_f h_tail (pfx ++ "_push_s7_incf_tail"))
  -- Step 8: MOVLW mask — WREG = capacity - 1
  let h_ps8 ← StoreM.node (nodeMovlw (UInt8.ofNat mask.toNat) (pfx ++ "_push_s8_movlw_mask"))
  -- Step 9: ANDWF tail, F — tail &= mask  (wrap mod capacity)
  let h_ps9 ← StoreM.node (nodeAndwf_f h_tail (pfx ++ "_push_s9_andwf_tail"))
  -- push proc: seq of the nine steps above
  let h_push ← StoreM.node (.proc #[] #[]
    (.seq #[h_ps1, h_ps2, h_ps3, h_ps4, h_ps5, h_ps6, h_ps7, h_ps8, h_ps9])
    (pfx ++ "_push"))
  return { h_head, h_tail, h_data, h_temp, h_is_full, h_push }

end AIL
