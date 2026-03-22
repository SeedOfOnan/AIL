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
-- Callers merge RingBufInstance.nodes into their own Store:
--   let rb := makeRingBuf ...
--   let s := rb.nodes.foldl (fun acc (h, n) => Store.insert acc h n) myStore
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
  nodes     : Store

/-- Build a ring buffer of `capacity` bytes.
    headAddr, tailAddr: addresses of the head and tail index bytes.
    dataAddr: base address of the buffer body (staticArray).
    tempAddr: address of a scratch byte (used by push to save WREG).
    capacity: number of elements; must be a power of 2.
    boolUid: unique UInt64 for the bool formal in is_full's rets.
    pfx: label prefix for all nodes (metadata only). -/
def makeRingBuf
    (headAddr tailAddr dataAddr tempAddr : UInt32)
    (capacity : UInt32) (boolUid : UInt64) (pfx : String)
    : RingBufInstance :=
  let mask := capacity - 1
  -- -------------------------------------------------------------------------
  -- Location nodes
  -- -------------------------------------------------------------------------
  let n_head : Node := .data .data .w8 headAddr (pfx ++ "_head")
  let h_head := hashNode n_head
  let n_tail : Node := .data .data .w8 tailAddr (pfx ++ "_tail")
  let h_tail := hashNode n_tail
  let n_data : Node := .staticArray .data .w8 dataAddr capacity (pfx ++ "_data")
  let h_data := hashNode n_data
  let n_temp : Node := .data .data .w8 tempAddr (pfx ++ "_temp")
  let h_temp := hashNode n_temp
  -- -------------------------------------------------------------------------
  -- Bool formal for is_full return
  -- -------------------------------------------------------------------------
  let n_bool : Node := .formal boolUid .bool
  let h_bool := hashNode n_bool
  -- -------------------------------------------------------------------------
  -- is_full: (tail+1) & mask == head  →  CPFSEQ skips when buffer is full.
  --
  -- Four typed atomic steps:
  --   1. MOVF tail, W   — load tail index into WREG  (AbstractOp.load)
  --   2. ADDLW 1        — WREG += 1                  (AbstractOp.addImm 1)
  --   3. ANDLW mask     — WREG &= mask               (AbstractOp.andImm mask)
  --   4. CPFSEQ head    — skip if head == WREG (full) (AbstractOp.compare)
  -- -------------------------------------------------------------------------
  let n_if_load_tail : Node := .proc #[h_tail] #[]
    (.atomic (.abstract .load) #[h_tail] #[]) (pfx ++ "_if_load_tail")
  let h_if_load_tail := hashNode n_if_load_tail
  let n_if_add1 : Node := .proc #[] #[]
    (.atomic (.abstract (.addImm 1)) #[] #[]) (pfx ++ "_if_add1")
  let h_if_add1 := hashNode n_if_add1
  let n_if_and_mask : Node := .proc #[] #[]
    (.atomic (.abstract (.andImm (UInt8.ofNat mask.toNat))) #[] #[]) (pfx ++ s!"_if_and_{mask.toNat}")
  let h_if_and_mask := hashNode n_if_and_mask
  let n_if_cmp_head : Node := .proc #[h_head] #[h_bool]
    (.atomic (.abstract .compare) #[h_head] #[]) (pfx ++ "_if_cmp_head")
  let h_if_cmp_head := hashNode n_if_cmp_head
  let n_is_full : Node := .proc #[] #[h_bool]
    (.seq #[h_if_load_tail, h_if_add1, h_if_and_mask, h_if_cmp_head])
    (pfx ++ "_is_full")
  let h_is_full := hashNode n_is_full
  -- -------------------------------------------------------------------------
  -- push: write WREG (received byte) to buf[tail], then advance tail.
  --
  -- Expressed as ProcBody.seq of single-instruction ISA nodes (AIL issue #9).
  -- Each step is a Node.proc #[] #[] (type Ty.proc [] [] 0).
  -- -------------------------------------------------------------------------
  -- Step 1: MOVWF temp — save received byte before FSR0 clobbers WREG
  let n_ps1 := nodeMovwf h_temp (pfx ++ "_push_s1_movwf_temp")
  let h_ps1 := hashNode n_ps1
  -- Step 2: LFSR 0, data — FSR0 = base address of buf
  let n_ps2 := nodeLfsr0 h_data (pfx ++ "_push_s2_lfsr0_data")
  let h_ps2 := hashNode n_ps2
  -- Step 3: MOVF tail, W — WREG = tail index
  let n_ps3 := nodeMovf_w h_tail (pfx ++ "_push_s3_movf_tail")
  let h_ps3 := hashNode n_ps3
  -- Step 4: ADDWF FSR0L, F — FSR0L += tail  →  FSR0 = &buf[tail]
  let n_ps4 := nodeAddwf_FSR0L (pfx ++ "_push_s4_addwf_fsr0l")
  let h_ps4 := hashNode n_ps4
  -- Step 5: MOVF temp, W — WREG = saved received byte (restore after FSR0 setup)
  let n_ps5 := nodeMovf_w h_temp (pfx ++ "_push_s5_movf_temp")
  let h_ps5 := hashNode n_ps5
  -- Step 6: MOVWF INDF0 — buf[tail] = received byte
  let n_ps6 := nodeMovwf_INDF0 (pfx ++ "_push_s6_movwf_indf0")
  let h_ps6 := hashNode n_ps6
  -- Step 7: INCF tail, F — tail++
  let n_ps7 := nodeIncf_f h_tail (pfx ++ "_push_s7_incf_tail")
  let h_ps7 := hashNode n_ps7
  -- Step 8: MOVLW mask — WREG = capacity - 1
  let n_ps8 := nodeMovlw (UInt8.ofNat mask.toNat) (pfx ++ "_push_s8_movlw_mask")
  let h_ps8 := hashNode n_ps8
  -- Step 9: ANDWF tail, F — tail &= mask  (wrap mod capacity)
  let n_ps9 := nodeAndwf_f h_tail (pfx ++ "_push_s9_andwf_tail")
  let h_ps9 := hashNode n_ps9
  -- push proc: seq of the nine steps above
  let n_push : Node := .proc #[] #[]
    (.seq #[h_ps1, h_ps2, h_ps3, h_ps4, h_ps5, h_ps6, h_ps7, h_ps8, h_ps9])
    (pfx ++ "_push")
  let h_push := hashNode n_push
  -- -------------------------------------------------------------------------
  -- Build Store
  -- -------------------------------------------------------------------------
  let nodes := Store.insert Store.empty h_head         n_head
  let nodes := Store.insert nodes       h_tail         n_tail
  let nodes := Store.insert nodes       h_data         n_data
  let nodes := Store.insert nodes       h_temp         n_temp
  let nodes := Store.insert nodes       h_bool         n_bool
  let nodes := Store.insert nodes       h_if_load_tail n_if_load_tail
  let nodes := Store.insert nodes       h_if_add1      n_if_add1
  let nodes := Store.insert nodes       h_if_and_mask  n_if_and_mask
  let nodes := Store.insert nodes       h_if_cmp_head  n_if_cmp_head
  let nodes := Store.insert nodes       h_is_full      n_is_full
  let nodes := Store.insert nodes       h_ps1          n_ps1
  let nodes := Store.insert nodes       h_ps2          n_ps2
  let nodes := Store.insert nodes       h_ps3          n_ps3
  let nodes := Store.insert nodes       h_ps4          n_ps4
  let nodes := Store.insert nodes       h_ps5          n_ps5
  let nodes := Store.insert nodes       h_ps6          n_ps6
  let nodes := Store.insert nodes       h_ps7          n_ps7
  let nodes := Store.insert nodes       h_ps8          n_ps8
  let nodes := Store.insert nodes       h_ps9          n_ps9
  let nodes := Store.insert nodes       h_push         n_push
  { h_head, h_tail, h_data, h_temp, h_is_full, h_push, nodes }

end AIL
