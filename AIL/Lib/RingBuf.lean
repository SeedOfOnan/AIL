-- AIL.Lib.RingBuf
-- Generic power-of-2 ring buffer for PIC18.
--
-- makeRingBuf builds all Store nodes for a ring buffer:
--   head, tail  : UInt8 index counters
--   data        : staticArray of bytes (capacity must be a power of 2)
--   temp        : UInt8 scratch byte used by push to save WREG
--   is_full     : proc [] [Bool] — condition: (tail+1)&mask == head
--   push        : proc [] []    — writes WREG to buf[tail], advances tail
--
-- The push intrinsic saves WREG to temp before the FSR0-indirect write,
-- working around the WREG-clobbering issue in AbstractOp.indexStore.
--
-- Callers merge RingBufInstance.nodes into their own Store:
--   let rb := makeRingBuf ...
--   let s := rb.nodes.foldl (fun acc (h, n) => Store.insert acc h n) myStore
--
-- boolUid must be unique across all formals in the containing Store.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store

namespace AIL

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
  -- Intrinsic because addlw and andlw (literal-operand ops) are not yet
  -- abstract ops.  Symbol names use hashLabel so they match emitted EQUs.
  -- -------------------------------------------------------------------------
  let n_is_full : Node := .proc #[] #[h_bool]
    (.intrinsic
      #[s!"    movf    {hashLabel h_tail}, w, c",
        "    addlw   1",
        s!"    andlw   {mask.toNat}",
        s!"    cpfseq  {hashLabel h_head}, c"]
      #[h_head, h_tail] #[]
      #["condition: (tail+1)&mask == head (buffer full)"])
    (pfx ++ "_is_full")
  let h_is_full := hashNode n_is_full
  -- -------------------------------------------------------------------------
  -- push: write WREG (received byte) to buf[tail], then advance tail.
  --
  -- Step-by-step:
  --   movwf temp         ; save received byte before FSR clobbers WREG
  --   lfsr  0, data      ; FSR0 = base address of buf
  --   movf  tail, w      ; WREG = tail index
  --   addwf FSR0L, f     ; FSR0L += tail  →  FSR0 points at buf[tail]
  --   movf  temp, w      ; WREG = saved received byte (restore)
  --   movwf INDF0        ; buf[tail] = received byte
  --   incf  tail, f      ; tail++
  --   movlw mask         ; WREG = capacity-1
  --   andwf tail, f      ; tail &= mask  (mod capacity, wrap)
  -- -------------------------------------------------------------------------
  let n_push : Node := .proc #[] #[]
    (.intrinsic
      #[s!"    movwf   {hashLabel h_temp}, c",
        s!"    lfsr    0, {hashLabel h_data}",
        s!"    movf    {hashLabel h_tail}, w, c",
        "    addwf   FSR0L, f, c",
        s!"    movf    {hashLabel h_temp}, w, c",
        "    movwf   INDF0, c",
        s!"    incf    {hashLabel h_tail}, f, c",
        s!"    movlw   {mask.toNat}",
        s!"    andwf   {hashLabel h_tail}, f, c"]
      #[h_data, h_tail, h_temp] #[h_tail, h_temp]
      #["push WREG to buf[tail]; advance tail mod capacity"])
    (pfx ++ "_push")
  let h_push := hashNode n_push
  -- -------------------------------------------------------------------------
  -- Build Store
  -- -------------------------------------------------------------------------
  let nodes := Store.insert Store.empty h_head    n_head
  let nodes := Store.insert nodes       h_tail    n_tail
  let nodes := Store.insert nodes       h_data    n_data
  let nodes := Store.insert nodes       h_temp    n_temp
  let nodes := Store.insert nodes       h_bool    n_bool
  let nodes := Store.insert nodes       h_is_full n_is_full
  let nodes := Store.insert nodes       h_push    n_push
  { h_head, h_tail, h_data, h_temp, h_is_full, h_push, nodes }

end AIL
