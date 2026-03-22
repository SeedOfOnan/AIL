-- TestRunner.lean
-- Example programs for AIL / PIC18.
--
-- Each example builds a store by hand, runs checkStore, runs compile, and
-- prints the resulting assembly. Failures are reported in-line rather than
-- aborting, so all examples run regardless of individual outcomes.
--
-- Usage: lake exe ailtest
--
-- These examples serve as both regression tests and design probes — a failing
-- example that should succeed is a bug; a failing example that reveals a real
-- gap in the spec is a useful discovery.

import AIL
import AIL.Targets.PIC18.Emitter
import AIL.Targets.PIC18.Capabilities

open AIL AIL.PIC18

-- ---------------------------------------------------------------------------
-- Test harness
-- ---------------------------------------------------------------------------

structure Example where
  name  : String
  store : Store
  ivt   : Array IVTEntry

def runExample (ex : Example) : IO Unit := do
  IO.println s!"=== {ex.name} ==="
  match checkStore targetConfig ex.store with
  | .error diag =>
      IO.println   "  checkStore: FAIL"
      IO.println s!"  {diag.toJson}"
  | .ok tyEnv =>
      IO.println   "  checkStore: PASS"
      let warns := readClearsWarnings ex.store
      for w in warns do
        IO.println s!"  {w.toJson}"
      match compile ex.store tyEnv ex.ivt with
      | .error msg =>
          IO.println s!"  compile:    FAIL  ({msg})"
      | .ok lines =>
          IO.println   "  compile:    PASS"
          for line in lines do
            IO.println s!"  {line}"

-- ---------------------------------------------------------------------------
-- Ex01: Copy byte
--
-- src at 0x20 → dst at 0x21.
-- seq [load_src, store_dst]
-- Expected PIC18 output:
--   movf  src, w, c
--   movwf dst, c
-- ---------------------------------------------------------------------------

def ex01_copy : Example :=
  let n_src  : Node := .data .data .w8 0x20 "src"
  let h_src  := hashNode n_src
  let n_dst  : Node := .data .data .w8 0x21 "dst"
  let h_dst  := hashNode n_dst
  let n_load : Node := .proc #[h_src] #[] (.atomic (.abstract .load) #[h_src] #[]) "load_src"
  let h_load := hashNode n_load
  let n_stor : Node := .proc #[] #[h_dst] (.atomic (.abstract .store) #[] #[h_dst]) "store_dst"
  let h_stor := hashNode n_stor
  let n_reset : Node := .proc #[] #[] (.seq #[h_load, h_stor]) "reset"
  let h_reset := hashNode n_reset
  let s := Store.insert Store.empty h_src   n_src
  let s := Store.insert s           h_dst   n_dst
  let s := Store.insert s           h_load  n_load
  let s := Store.insert s           h_stor  n_stor
  let s := Store.insert s           h_reset n_reset
  { name := "Ex01: Copy byte  (src→dst)", store := s, ivt := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex02: Add in-place
--
-- a at 0x20, b at 0x21.  b = a + b.
-- seq [load_a, add_b]
-- PIC18 idiom: MOVF a, W loads a; ADDWF b, F adds WREG to b in-place.
-- The WREG intermediate is implicit (seq_ok wiring is a TODO).
-- Expected PIC18 output:
--   movf  a, w, c
--   addwf b, f, c
-- ---------------------------------------------------------------------------

def ex02_add : Example :=
  let n_a    : Node := .data .data .w8 0x20 "a"
  let h_a    := hashNode n_a
  let n_b    : Node := .data .data .w8 0x21 "b"
  let h_b    := hashNode n_b
  let n_load : Node := .proc #[h_a] #[] (.atomic (.abstract .load) #[h_a] #[]) "load_a"
  let h_load := hashNode n_load
  let n_add  : Node := .proc #[h_b] #[] (.atomic (.abstract .add) #[h_b] #[]) "add_to_b"
  let h_add  := hashNode n_add
  let n_reset : Node := .proc #[] #[] (.seq #[h_load, h_add]) "reset"
  let h_reset := hashNode n_reset
  let s := Store.insert Store.empty h_a     n_a
  let s := Store.insert s           h_b     n_b
  let s := Store.insert s           h_load  n_load
  let s := Store.insert s           h_add   n_add
  let s := Store.insert s           h_reset n_reset
  { name := "Ex02: Add in-place  (b = a + b)", store := s, ivt := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex03: Conditional copy
--
-- a at 0x20, b at 0x21, result at 0x22.
-- if a == b: result = a   else: result = b
--
-- PIC18 strategy: load b into WREG, then CPFSEQ a (skip if a == WREG).
-- The skip-style condition protocol: test proc ends with a skip instruction;
-- the emitter puts GOTO else immediately after it (skipped when true).
--
-- Demonstrates: cond body, bool formal in rets, shared node (n_load_b reused
-- in both the test seq and the else branch — same hash, one EQU declaration).
--
-- Expected PIC18 output:
--   movf   b, w, c      ; load b into WREG
--   cpfseq a, c         ; skip if a == WREG (a == b)
--   goto   _else_N      ; not skipped when a != b
--   movf   a, w, c      ; then: load a
--   movwf  result, c    ;        store to result
--   goto   _end_N
-- _else_N:
--   movf   b, w, c      ; else: load b
--   movwf  result, c    ;        store to result
-- _end_N:
-- ---------------------------------------------------------------------------

def ex03_cond : Example :=
  let n_a      : Node := .data .data .w8 0x20 "a"
  let h_a      := hashNode n_a
  let n_b      : Node := .data .data .w8 0x21 "b"
  let h_b      := hashNode n_b
  let n_result : Node := .data .data .w8 0x22 "result"
  let h_result := hashNode n_result
  -- Bool formal: the output of the compare proc
  let n_bool   : Node := .formal 1 .bool
  let h_bool   := hashNode n_bool
  -- load_a: movf a, w  (used in then-branch)
  let n_load_a : Node := .proc #[h_a] #[] (.atomic (.abstract .load) #[h_a] #[]) "load_a"
  let h_load_a := hashNode n_load_a
  -- load_b: movf b, w  (reused in test-seq and else-branch — same hash)
  let n_load_b : Node := .proc #[h_b] #[] (.atomic (.abstract .load) #[h_b] #[]) "load_b"
  let h_load_b := hashNode n_load_b
  -- store_result: movwf result  (shared by both branches)
  let n_stor_r : Node := .proc #[] #[h_result] (.atomic (.abstract .store) #[] #[h_result]) "store_result"
  let h_stor_r := hashNode n_stor_r
  -- cmp_a: cpfseq a, c  — produces bool output (a == WREG?)
  -- WREG must already hold b, which the test-seq ensures.
  let n_cmp_a  : Node := .proc #[] #[h_bool] (.atomic (.abstract .compare) #[h_a] #[]) "cmp_a"
  let h_cmp_a  := hashNode n_cmp_a
  -- test: seq [load_b, cmp_a] — loads b into WREG then compares with a
  -- rets=[h_bool] so type = proc [] [Ty.bool] 0, satisfying cond's test constraint
  let n_test   : Node := .proc #[] #[h_bool] (.seq #[h_load_b, h_cmp_a]) "test_a_eq_b"
  let h_test   := hashNode n_test
  -- then: result = a
  let n_then   : Node := .proc #[] #[] (.seq #[h_load_a, h_stor_r]) "then_copy_a"
  let h_then   := hashNode n_then
  -- else: result = b  (h_load_b is the SAME node reused — content-addressed dedup)
  let n_else   : Node := .proc #[] #[] (.seq #[h_load_b, h_stor_r]) "else_copy_b"
  let h_else   := hashNode n_else
  let n_cond   : Node := .proc #[] #[] (.cond h_test h_then h_else) "if_a_eq_b"
  let h_cond   := hashNode n_cond
  let n_reset  : Node := .proc #[] #[] (.seq #[h_cond]) "reset"
  let h_reset  := hashNode n_reset
  let s := Store.insert Store.empty h_a      n_a
  let s := Store.insert s           h_b      n_b
  let s := Store.insert s           h_result n_result
  let s := Store.insert s           h_bool   n_bool
  let s := Store.insert s           h_load_a n_load_a
  let s := Store.insert s           h_load_b n_load_b
  let s := Store.insert s           h_stor_r n_stor_r
  let s := Store.insert s           h_cmp_a  n_cmp_a
  let s := Store.insert s           h_test   n_test
  let s := Store.insert s           h_then   n_then
  let s := Store.insert s           h_else   n_else
  let s := Store.insert s           h_cond   n_cond
  let s := Store.insert s           h_reset  n_reset
  { name := "Ex03: Conditional copy  (if a==b: result=a else result=b)",
    store := s, ivt := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex04: Counted loop
--
-- count at 0x20 (pre-initialized to N by test harness).
-- Loop N times, decrementing count each iteration. Body is a no-op.
-- Demonstrates: ProcBody.loop with params[0] as the bound.
--
-- NOTE: loop_ok requires the body proc to have the same paramTys as the
-- containing loop proc (paramTys = [Ty.data .data .w8]).  inferBodyDepth for
-- loop does NOT enforce this (it only checks the body resolves to a proc type),
-- so type inference passes here even though the propositional rule would not.
-- This gap is covered by the sorry'd soundness theorem.
--
-- Expected PIC18 output:
-- _loop_N:
--   decfsz  count, f, c    ; decrement count; skip bra if zero
--   bra     _loop_N
-- ---------------------------------------------------------------------------

def ex04_loop : Example :=
  let n_count : Node := .data .data .w8 0x20 "count"
  let h_count := hashNode n_count
  -- Empty body (no-op each iteration)
  let n_body  : Node := .proc #[] #[] (.seq #[]) "loop_body"
  let h_body  := hashNode n_body
  -- Loop proc: params[0] = count (the bound)
  let n_loop  : Node := .proc #[h_count] #[] (.loop h_body) "count_down"
  let h_loop  := hashNode n_loop
  let n_reset : Node := .proc #[] #[] (.seq #[h_loop]) "reset"
  let h_reset := hashNode n_reset
  let s := Store.insert Store.empty h_count n_count
  let s := Store.insert s           h_body  n_body
  let s := Store.insert s           h_loop  n_loop
  let s := Store.insert s           h_reset n_reset
  { name := "Ex04: Counted loop  (decrement count to zero)",
    store := s, ivt := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex05: Two IVT entries
--
-- vec 0 (reset):     copy src → dst
-- vec 1 (timer ISR): copy isr_count → isr_out
--
-- Demonstrates: multi-entry IVT; each ISR body is an ordinary proc.
-- The two entry procs are independent (no shared callees in this example).
-- ---------------------------------------------------------------------------

def ex05_two_vec : Example :=
  -- vec 0 nodes
  let n_src     : Node := .data .data .w8 0x20 "src"
  let h_src     := hashNode n_src
  let n_dst     : Node := .data .data .w8 0x21 "dst"
  let h_dst     := hashNode n_dst
  -- vec 1 nodes
  let n_icnt    : Node := .data .data .w8 0x22 "isr_count"
  let h_icnt    := hashNode n_icnt
  let n_iout    : Node := .data .data .w8 0x23 "isr_out"
  let h_iout    := hashNode n_iout
  -- Procs (note: load and store procs for different data nodes have different
  -- hashes even though the body shape is the same, because the data node hashes
  -- embedded in reads/writes differ)
  let n_ld_src  : Node := .proc #[h_src]  #[] (.atomic (.abstract .load) #[h_src] #[]) "load_src"
  let h_ld_src  := hashNode n_ld_src
  let n_st_dst  : Node := .proc #[] #[h_dst]  (.atomic (.abstract .store) #[] #[h_dst]) "store_dst"
  let h_st_dst  := hashNode n_st_dst
  let n_ld_cnt  : Node := .proc #[h_icnt] #[] (.atomic (.abstract .load) #[h_icnt] #[]) "load_cnt"
  let h_ld_cnt  := hashNode n_ld_cnt
  let n_st_out  : Node := .proc #[] #[h_iout] (.atomic (.abstract .store) #[] #[h_iout]) "store_out"
  let h_st_out  := hashNode n_st_out
  let n_reset   : Node := .proc #[] #[] (.seq #[h_ld_src, h_st_dst]) "reset"
  let h_reset   := hashNode n_reset
  let n_timer   : Node := .proc #[] #[] (.seq #[h_ld_cnt, h_st_out]) "timer_isr"
  let h_timer   := hashNode n_timer
  let s := Store.insert Store.empty h_src    n_src
  let s := Store.insert s           h_dst    n_dst
  let s := Store.insert s           h_icnt   n_icnt
  let s := Store.insert s           h_iout   n_iout
  let s := Store.insert s           h_ld_src n_ld_src
  let s := Store.insert s           h_st_dst n_st_dst
  let s := Store.insert s           h_ld_cnt n_ld_cnt
  let s := Store.insert s           h_st_out n_st_out
  let s := Store.insert s           h_reset  n_reset
  let s := Store.insert s           h_timer  n_timer
  { name := "Ex05: Two IVT entries  (reset + timer ISR)",
    store := s, ivt := #[(0, h_reset), (1, h_timer)] }

-- ---------------------------------------------------------------------------
-- Ex07: Indexed array copy
--
-- buf: 4-byte staticArray at 0x20.
-- idx: u8 index at 0x24.
-- dst: u8 destination at 0x25.
-- seq [indexLoad buf idx, store dst]  →  dst = buf[idx]
--
-- Demonstrates: Node.staticArray, AbstractOp.indexLoad, FSR0 indirect.
--
-- Expected PIC18 output:
--   lfsr    0, _n<buf>         ; FSR0 = buf base
--   movf    _n<idx>, w, c      ; WREG = idx
--   addwf   FSR0L, f, c        ; FSR0 += idx
--   movf    INDF0, w, c        ; WREG = buf[idx]
--   movwf   _n<dst>, c         ; dst = WREG
-- ---------------------------------------------------------------------------

def ex07_index_copy : Example :=
  let n_buf : Node := .staticArray .data .w8 0x20 4 "buf"
  let h_buf := hashNode n_buf
  let n_idx : Node := .data .data .w8 0x24 "idx"
  let h_idx := hashNode n_idx
  let n_dst : Node := .data .data .w8 0x25 "dst"
  let h_dst := hashNode n_dst
  let n_load : Node := .proc #[] #[]
    (.atomic (.abstract .indexLoad) #[h_buf, h_idx] #[]) "load_buf_idx"
  let h_load := hashNode n_load
  let n_stor : Node := .proc #[] #[h_dst]
    (.atomic (.abstract .store) #[] #[h_dst]) "store_dst"
  let h_stor := hashNode n_stor
  let n_reset : Node := .proc #[] #[] (.seq #[h_load, h_stor]) "reset"
  let h_reset := hashNode n_reset
  let s := Store.insert Store.empty h_buf   n_buf
  let s := Store.insert s           h_idx   n_idx
  let s := Store.insert s           h_dst   n_dst
  let s := Store.insert s           h_load  n_load
  let s := Store.insert s           h_stor  n_stor
  let s := Store.insert s           h_reset n_reset
  { name := "Ex07: Indexed array copy  (dst = buf[idx])", store := s,
    ivt  := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex06: UART receive interrupt handler (PIC18, high-priority ISR)
--
-- Demonstrates: Node.peripheral (SFR), Node.bitField, AbstractOp.testBit
-- (BTFSS), peripheral reads (MOVF), and cond nesting for guard-style
-- early exits.
--
-- The ring buffer operations (is_full, push) use ProcBody.intrinsic because
-- AIL#4 (fixed-size arrays) and AIL#5 (user-defined types) are not yet
-- implemented.  When those land, the intrinsics below should be replaced
-- with proper Store nodes.
--
-- Design decisions:
--   - Hardware OERR → panic (infinite loop)
--   - FERR         → discard byte (read RCREG to advance FIFO), retfie
--   - Ring buffer full → set rx_buf_overrun flag, retfie
--   - Push          → FSR0 indirect write to buf[tail], advance tail (& 0x1F)
--
-- vec 1 = high-priority ISR vector (0x0008 on classic PIC18).
-- Context save/restore emitted by caller (TODO: emitter ISR prologue/epilogue).
--
-- Expected PIC18 output (core logic; intrinsic bodies still emitted as
-- comment blocks until the typed-intrinsic TODO is resolved):
--   btfss  RCSTA, 1, c       ; skip if OERR set
--   goto   _else_0           ; OERR clear → skip to else
--   L_panic: bra L_panic     ; panic
--   ...
-- ---------------------------------------------------------------------------

def ex06_uart_rx : Example :=
  -- -------------------------------------------------------------------------
  -- Peripheral nodes
  -- -------------------------------------------------------------------------
  let sem_rcsta : AccessSemantics :=
    { readable := true, writable := true,
      sideEffectOnRead := false, sideEffectOnWrite := false, accessWidth := .w8 }
  let n_RCSTA : Node := .peripheral .sfr 0xFAB sem_rcsta "RCSTA"
  let h_RCSTA := hashNode n_RCSTA

  -- RCREG: read-only, reading clears the hardware FIFO slot (read_clears).
  let sem_rcreg : AccessSemantics :=
    { readable := true, writable := false,
      sideEffectOnRead := true, sideEffectOnWrite := false, accessWidth := .w8 }
  let n_RCREG : Node := .peripheral .sfr 0xFAE sem_rcreg "RCREG"
  let h_RCREG := hashNode n_RCREG

  -- -------------------------------------------------------------------------
  -- Bit field nodes
  -- -------------------------------------------------------------------------
  let n_OERR : Node := .bitField h_RCSTA 1 "OERR"
  let h_OERR := hashNode n_OERR
  let n_FERR : Node := .bitField h_RCSTA 2 "FERR"
  let h_FERR := hashNode n_FERR

  -- -------------------------------------------------------------------------
  -- Static RAM: ring buffer state
  -- -------------------------------------------------------------------------
  let n_rx_head    : Node := .data .data .w8 0x20 "rx_buf_head"
  let h_rx_head    := hashNode n_rx_head
  let n_rx_tail    : Node := .data .data .w8 0x21 "rx_buf_tail"
  let h_rx_tail    := hashNode n_rx_tail
  let n_rx_overrun : Node := .data .data .w8 0x22 "rx_buf_overrun"
  let h_rx_overrun := hashNode n_rx_overrun
  -- rx_buf_data: 32-byte ring buffer body at 0x23–0x42.
  let n_rx_data    : Node := .staticArray .data .w8 0x23 32 "rx_buf_data"
  let h_rx_data    := hashNode n_rx_data

  -- -------------------------------------------------------------------------
  -- Bool formals (one per distinct cond test)
  -- -------------------------------------------------------------------------
  let n_bool_0 : Node := .formal 0 .bool
  let h_bool_0 := hashNode n_bool_0
  let n_bool_1 : Node := .formal 1 .bool
  let h_bool_1 := hashNode n_bool_1
  let n_bool_2 : Node := .formal 2 .bool
  let h_bool_2 := hashNode n_bool_2

  -- -------------------------------------------------------------------------
  -- Leaf procs
  -- -------------------------------------------------------------------------

  -- nop: empty body — used as the else-branch of guard-style conds.
  let n_nop : Node := .proc #[] #[] (.seq #[]) "nop"
  let h_nop := hashNode n_nop

  -- panic: infinite loop.
  -- Typed proc [] [] (not proc [] [Never]) so it matches nop in cond branches.
  -- The Never semantics are implicit: bra L_panic never returns.
  let n_panic : Node := .proc #[] #[]
    (.intrinsic #["L_panic:", "    bra     L_panic"] #[] #[]
                #["halt: never returns"] #[]) "panic"
  let h_panic := hashNode n_panic

  -- early_retfie: return from ISR without continuing the handler body.
  -- Used after FERR discard and after ring-buffer-full detection.
  let n_early_retfie : Node := .proc #[] #[]
    (.intrinsic #["    retfie  0"] #[] #[]
                #["early ISR exit"] #[]) "early_retfie"
  let h_early_retfie := hashNode n_early_retfie

  -- discard_rcreg: MOVF RCREG, W — reads RCREG solely to advance the hardware
  -- FIFO on a FERR byte.  Uses .loadDiscard to suppress the read_clears warning.
  let n_discard_rcreg : Node := .proc #[] #[]
    (.atomic (.abstract .loadDiscard) #[h_RCREG] #[]) "discard_rcreg"
  let h_discard_rcreg := hashNode n_discard_rcreg

  -- read_rcreg: MOVF RCREG, W — reads the received byte into WREG for use
  -- in do_push.  Uses .load (not .loadDiscard); will warn until SSA wiring
  -- tracks WREG flow and can confirm the result is consumed.
  let n_read_rcreg : Node := .proc #[] #[]
    (.atomic (.abstract .load) #[h_RCREG] #[]) "read_rcreg"
  let h_read_rcreg := hashNode n_read_rcreg

  -- -------------------------------------------------------------------------
  -- Guard: if OERR { panic }
  -- -------------------------------------------------------------------------

  -- test_oerr: BTFSS RCSTA, 1 — skip if OERR set (condition = OERR is set).
  let n_test_oerr : Node := .proc #[] #[h_bool_0]
    (.atomic (.abstract .testBit) #[h_OERR] #[]) "test_oerr"
  let h_test_oerr := hashNode n_test_oerr

  -- if_oerr: if OERR { panic } else { nop }
  let n_if_oerr : Node := .proc #[] #[] (.cond h_test_oerr h_panic h_nop) "if_oerr"
  let h_if_oerr := hashNode n_if_oerr

  -- -------------------------------------------------------------------------
  -- Guard: if FERR { discard byte; retfie }
  -- -------------------------------------------------------------------------

  -- test_ferr: BTFSS RCSTA, 2 — skip if FERR set.
  let n_test_ferr : Node := .proc #[] #[h_bool_1]
    (.atomic (.abstract .testBit) #[h_FERR] #[]) "test_ferr"
  let h_test_ferr := hashNode n_test_ferr

  -- discard_and_retfie: discard the errored byte (advances FIFO), then retfie.
  let n_discard_and_retfie : Node := .proc #[] #[]
    (.seq #[h_discard_rcreg, h_early_retfie]) "discard_and_retfie"
  let h_discard_and_retfie := hashNode n_discard_and_retfie

  -- if_ferr: if FERR { discard + retfie } else { nop }
  let n_if_ferr : Node := .proc #[] #[]
    (.cond h_test_ferr h_discard_and_retfie h_nop) "if_ferr"
  let h_if_ferr := hashNode n_if_ferr

  -- -------------------------------------------------------------------------
  -- Ring buffer: is_full check and push
  -- TODO: replace intrinsics with proper Store nodes once AIL#4/#5 land.
  -- -------------------------------------------------------------------------

  -- test_is_full: (tail+1) & 0x1F == head → CPFSEQ skip if equal (full).
  -- Reads rx_buf_head and rx_buf_tail; produces a bool formal.
  -- Symbol names use hashLabel format so they match the emitter's EQU declarations.
  let n_test_is_full : Node := .proc #[] #[h_bool_2]
    (.intrinsic
      #[s!"    movf    {hashLabel h_rx_tail}, w, c",
        "    addlw   1",
        "    andlw   0x1f",
        s!"    cpfseq  {hashLabel h_rx_head}, c"]
      #[h_rx_head, h_rx_tail] #[]
      #["condition: (tail+1)&31 == head (buffer full)"] #[]) "test_is_full"
  let h_test_is_full := hashNode n_test_is_full

  -- set_overrun_and_retfie: set the overrun flag and exit ISR (drop the byte).
  let n_set_overrun : Node := .proc #[] #[]
    (.intrinsic
      #[s!"    setf    {hashLabel h_rx_overrun}, c",
        "    retfie  0"]
      #[] #[h_rx_overrun]
      #["set overrun flag; drop received byte; exit ISR"] #[]) "set_overrun"
  let h_set_overrun := hashNode n_set_overrun

  -- do_push: write WREG (received byte) to buf[tail] via indexStore, then
  -- advance tail mod 32 via intrinsic (incf + andlw not yet in abstract ops).
  -- indexStore emits: LFSR 0, rx_buf_data; MOVF tail, W; ADDWF FSR0L, F; MOVWF INDF0.
  -- NOTE: indexStore overwrites WREG with the index before the write — this is the
  -- known WREG limitation documented in the emitter TODO. The received byte is lost
  -- before MOVWF INDF0 executes. Resolves when SSA wiring tracks WREG explicitly.
  -- TODO: fix WREG clobbering in indexStore sequence.
  let n_push_store : Node := .proc #[] #[]
    (.atomic (.abstract .indexStore) #[h_rx_data, h_rx_tail] #[]) "push_store"
  let h_push_store := hashNode n_push_store
  let n_advance_tail : Node := .proc #[] #[]
    (.intrinsic
      #[s!"    incf    {hashLabel h_rx_tail}, f, c",
        "    movlw   0x1f",
        s!"    andwf   {hashLabel h_rx_tail}, f, c"]
      #[h_rx_tail] #[h_rx_tail]
      #["advance tail mod 32"] #[]) "advance_tail"
  let h_advance_tail := hashNode n_advance_tail
  let n_do_push : Node := .proc #[] #[]
    (.seq #[h_push_store, h_advance_tail]) "do_push"
  let h_do_push := hashNode n_do_push

  -- if_full: if full { set_overrun + retfie } else { push }
  let n_if_full : Node := .proc #[] #[]
    (.cond h_test_is_full h_set_overrun h_do_push) "if_full"
  let h_if_full := hashNode n_if_full

  -- -------------------------------------------------------------------------
  -- Top-level ISR body
  -- -------------------------------------------------------------------------
  let n_isr : Node := .proc #[] #[]
    (.seq #[h_if_oerr, h_if_ferr, h_read_rcreg, h_if_full]) "uart_rx_isr"
  let h_isr := hashNode n_isr

  -- -------------------------------------------------------------------------
  -- Store
  -- -------------------------------------------------------------------------
  let s := Store.insert Store.empty h_RCSTA             n_RCSTA
  let s := Store.insert s           h_RCREG             n_RCREG
  let s := Store.insert s           h_OERR              n_OERR
  let s := Store.insert s           h_FERR              n_FERR
  let s := Store.insert s           h_rx_head           n_rx_head
  let s := Store.insert s           h_rx_tail           n_rx_tail
  let s := Store.insert s           h_rx_overrun        n_rx_overrun
  let s := Store.insert s           h_rx_data           n_rx_data
  let s := Store.insert s           h_bool_0            n_bool_0
  let s := Store.insert s           h_bool_1            n_bool_1
  let s := Store.insert s           h_bool_2            n_bool_2
  let s := Store.insert s           h_nop               n_nop
  let s := Store.insert s           h_panic             n_panic
  let s := Store.insert s           h_early_retfie      n_early_retfie
  let s := Store.insert s           h_discard_rcreg     n_discard_rcreg
  let s := Store.insert s           h_read_rcreg        n_read_rcreg
  let s := Store.insert s           h_test_oerr         n_test_oerr
  let s := Store.insert s           h_if_oerr           n_if_oerr
  let s := Store.insert s           h_test_ferr         n_test_ferr
  let s := Store.insert s           h_discard_and_retfie n_discard_and_retfie
  let s := Store.insert s           h_if_ferr           n_if_ferr
  let s := Store.insert s           h_test_is_full      n_test_is_full
  let s := Store.insert s           h_set_overrun       n_set_overrun
  let s := Store.insert s           h_push_store        n_push_store
  let s := Store.insert s           h_advance_tail      n_advance_tail
  let s := Store.insert s           h_do_push           n_do_push
  let s := Store.insert s           h_if_full           n_if_full
  let s := Store.insert s           h_isr               n_isr
  { name  := "Ex06: UART receive ISR  (PIC18, high-priority vec 1)",
    store := s,
    ivt   := #[(1, h_isr)] }

-- ---------------------------------------------------------------------------
-- Ex08: makeRingBuf library exercise
--
-- Builds a 32-byte ring buffer via makeRingBuf, then constructs a minimal
-- ISR-style entry that: tests is_full, if full sets an overrun flag and
-- returns, else calls push.
--
-- headAddr=0x10, tailAddr=0x11, dataAddr=0x12–0x31, tempAddr=0x32.
-- overrunAddr=0x33.
-- boolUid=10 (arbitrary, must be unique in this store).
--
-- Expected: checkStore PASS, compile PASS, assembly includes push intrinsic
-- (movwf temp, lfsr 0, data, ..., andwf tail).
-- ---------------------------------------------------------------------------

def ex08_ringbuf : Example :=
  let build : StoreM Hash := do
    let rb ← makeRingBuf 0x10 0x11 0x12 0x32 32 10 "rb"
    let h_overrun     ← StoreM.node (.data .data .w8 0x33 "rb_overrun")
    let h_set_overrun ← StoreM.node (.proc #[] #[]
      (.intrinsic #[s!"    setf    {hashLabel h_overrun}, c"] #[] #[h_overrun]
                  #["mark buffer overrun"] #[]) "rb_set_overrun")
    let _h_nop        ← StoreM.node (.proc #[] #[] (.seq #[]) "nop")
    let h_if_full     ← StoreM.node (.proc #[] #[]
      (.cond rb.h_is_full h_set_overrun rb.h_push) "rb_if_full")
    StoreM.node (.proc #[] #[] (.seq #[h_if_full]) "rb_entry")
  let (h_entry, store) := StoreM.run build
  { name := "Ex08: makeRingBuf  (32-byte ring buffer library)", store,
    ivt  := #[(0, h_entry)] }

-- ---------------------------------------------------------------------------
-- Ex09: Main loop — getch from ring buffer into line buffer until '\n'
--
-- Surfaces design gaps by doing real work:
--
--   DESIGN GAP A — FSR0 resource conflict (AIL#13)
--     pop (main) and push (ISR) both use FSR0.  If the high-priority ISR
--     fires while main is between LFSR 0 and MOVF INDF0, FSR0 is clobbered.
--     Fix requires: (a) BCF/BSF INTCON.GIE critical section (AIL#14), or
--     (b) FSR resource annotation in the type system so the compiler can
--     detect conflicting uses at build time (AIL#13).
--
--   DESIGN GAP C — Literal-operand instructions (AIL#12)
--     '\n' detection uses xorlw 0x0A — no AbstractOp covers literal operands
--     (xorImm, addImm, andImm, etc.).  Workaround: ProcBody.intrinsic.
--     The rest of the newline test (load getch_result, btfss STATUS,Z) uses
--     typed abstract ops, so only the xorlw step is an intrinsic.
--
-- Memory map:
--   0x20        rx_head
--   0x21        rx_tail
--   0x22        rx_temp   (push scratch byte, allocated by makeRingBuf)
--   0x23–0x42   rx_data   (32-byte ring buffer body)
--   0x43        rx_overrun (set by ISR when ring buffer is full)
--   0x44        getch_result (staging byte for fetched character)
--   0x45        line_len
--   0x46–0x85   line_buf  (64-byte line accumulation buffer)
--
-- IVT: vec 0 = main (the forever loop).
-- The ISR (vec 1) is not included here — see Ex06 for the ISR design.
-- In a real program the two stores would be merged.
-- ---------------------------------------------------------------------------

def ex09_main_loop : Example :=
  let build : StoreM Hash := do
    -- -------------------------------------------------------------------------
    -- Ring buffer (shared between ISR push and main pop)
    -- -------------------------------------------------------------------------
    let rb ← makeRingBuf 0x20 0x21 0x23 0x22 32 100 "rx"
  
    -- -------------------------------------------------------------------------
    -- STATUS register and Z flag (needed for xorlw-based newline test)
    -- -------------------------------------------------------------------------
    let h_STATUS ← StoreM.node (.peripheral .sfr 0xFD8
      { readable := true, writable := true,
        sideEffectOnRead := false, sideEffectOnWrite := false, accessWidth := .w8 }
      "STATUS")
    -- Z flag: STATUS bit 2 (PIC18 STATUS register, DS40002329F §3.2.1)
    let h_Z ← StoreM.node (.bitField h_STATUS 2 "Z")
  
    -- -------------------------------------------------------------------------
    -- Application state nodes
    -- -------------------------------------------------------------------------
    let h_getch_result ← StoreM.node (.data .data .w8 0x44 "getch_result")
    let h_line_len     ← StoreM.node (.data .data .w8 0x45 "line_len")
    let h_line_buf     ← StoreM.node (.staticArray .data .w8 0x46 64 "line_buf")
  
    -- -------------------------------------------------------------------------
    -- Bool formals
    -- -------------------------------------------------------------------------
    -- uid 101: for is_empty rets
    -- uid 102: for test_is_newline rets (Z flag)
    let h_bool_empty ← StoreM.node (.formal 101 .bool)
    let h_bool_nl    ← StoreM.node (.formal 102 .bool)
  
    -- -------------------------------------------------------------------------
    -- is_empty: head == tail (buffer is empty)
    -- cpfseq: skip if f == WREG.  Load tail into WREG; cpfseq head skips when
    -- head == tail (empty).  In the cond skip-protocol: skip = condition TRUE =
    -- buffer IS empty (keep spinning in getch_spin).
    -- -------------------------------------------------------------------------
    let h_is_empty ← StoreM.node (.proc #[] #[h_bool_empty]
      (.intrinsic
        #[s!"    movf    {hashLabel rb.h_tail}, w, c",
          s!"    cpfseq  {hashLabel rb.h_head}, c"]
        #[rb.h_head, rb.h_tail] #[]
        #["condition: head == tail (buffer empty)"] #[])
      "rx_is_empty")
  
    -- -------------------------------------------------------------------------
    -- getch_spin: spin until non-empty — whileLoop(is_empty, nop).
    -- -------------------------------------------------------------------------
    let h_getch_nop  ← StoreM.node (.proc #[] #[] (.seq #[]) "getch_nop")
    let h_getch_spin ← StoreM.node (.proc #[] #[]
      (.whileLoop h_is_empty h_getch_nop) "getch_spin")
  
    -- -------------------------------------------------------------------------
    -- pop: read buf[head] → getch_result, advance head mod 32.
    --
    -- DESIGN GAP A: uses FSR0 — same FSR as ISR push (makeRingBuf).
    -- No critical section: if the high-priority ISR fires between the LFSR
    -- and the MOVF INDF0, FSR0 is clobbered and getch_result gets the wrong byte.
    -- Fix requires BCF INTCON,GIE (AIL#14) and/or FSR annotation (AIL#13).
    -- -------------------------------------------------------------------------
    let h_pop ← StoreM.node (.proc #[] #[h_getch_result]
      (.intrinsic
        #[s!"    lfsr    0, {hashLabel rb.h_data}",
          s!"    movf    {hashLabel rb.h_head}, w, c",
          "    addwf   FSR0L, f, c",
          "    movf    INDF0, w, c",
          s!"    movwf   {hashLabel h_getch_result}, c",
          s!"    incf    {hashLabel rb.h_head}, f, c",
          "    movlw   31",
          s!"    andwf   {hashLabel rb.h_head}, f, c"]
        #[rb.h_data, rb.h_head] #[rb.h_head, h_getch_result]
        #["pop buf[head] → getch_result; advance head mod 32",
          "DESIGN GAP A: uses FSR0 — conflicts with ISR push (AIL#13, AIL#14)"] #[0])
      "rx_pop")
    let h_getch ← StoreM.node (.proc #[] #[h_getch_result]
      (.seq #[h_getch_spin, h_pop]) "getch")
  
    -- -------------------------------------------------------------------------
    -- test_is_newline: getch_result == '\n' (0x0A)?
    --
    -- Three-step seq:
    --   1. load getch_result → WREG              (AbstractOp.load)
    --   2. xorlw 0x0A                            (intrinsic — DESIGN GAP C, AIL#12)
    --   3. btfss STATUS, Z                       (AbstractOp.testBit on n_Z)
    --
    -- After xorlw: if WREG was 0x0A, WREG = 0 and Z = 1.
    -- btfss STATUS,2 skips when Z=1 (condition TRUE = is newline).
    -- In the cond protocol: skip = condition TRUE = byte is '\n'.
    -- -------------------------------------------------------------------------
    let h_load_gc ← StoreM.node (.proc #[h_getch_result] #[]
      (.atomic (.abstract .load) #[h_getch_result] #[]) "load_getch_result")
    let h_xor_nl  ← StoreM.node (.proc #[] #[]
      (.atomic (.abstract (.xorImm 0x0a)) #[] #[]) "xor_newline")
    let h_test_z  ← StoreM.node (.proc #[] #[h_bool_nl]
      (.atomic (.abstract .testBit) #[h_Z] #[]) "test_Z_flag")
    let h_test_nl ← StoreM.node (.proc #[] #[h_bool_nl]
      (.seq #[h_load_gc, h_xor_nl, h_test_z]) "test_is_newline")
  
    -- -------------------------------------------------------------------------
    -- append_line: write getch_result to line_buf[line_len]; line_len++.
    -- Uses FSR1 (not FSR0) — demonstrates multi-FSR usage.
    -- FSR annotations (AIL#13) would declare FSR0 → getch/pop, FSR1 → append_line,
    -- making the non-conflict between these two explicit and checkable.
    -- -------------------------------------------------------------------------
    let h_append_line ← StoreM.node (.proc #[] #[]
      (.intrinsic
        #[s!"    lfsr    1, {hashLabel h_line_buf}",
          s!"    movf    {hashLabel h_line_len}, w, c",
          "    addwf   FSR1L, f, c",
          s!"    movf    {hashLabel h_getch_result}, w, c",
          "    movwf   INDF1, c",
          s!"    incf    {hashLabel h_line_len}, f, c"]
        #[h_line_buf, h_line_len, h_getch_result] #[h_line_len]
        #["line_buf[line_len] = getch_result; line_len++",
          "uses FSR1 (distinct from FSR0 used by pop/getch for ring buffer)"] #[1])
      "append_line")
  
    let h_process_line ← StoreM.node (.proc #[] #[]
      (.intrinsic #[s!"    clrf    {hashLabel h_line_len}, c"] #[] #[h_line_len]
                  #["stub: clear line buffer; TODO: implement line processing"] #[])
      "process_line")
  
    let h_if_nl     ← StoreM.node (.proc #[] #[]
      (.cond h_test_nl h_process_line h_append_line) "if_newline")
    let h_main_body ← StoreM.node (.proc #[] #[]
      (.seq #[h_getch, h_if_nl]) "main_body")
    StoreM.node (.proc #[] #[] (.forever h_main_body) "main")

  let (h_main, store) := StoreM.run build
  { name := "Ex09: Main loop  (getch ring-buf → line buffer until '\\n')",
    store, ivt := #[(0, h_main)] }

-- ---------------------------------------------------------------------------
-- Ex10: Critical section  (BCF INTCON.GIE / BSF INTCON.GIE)
--
-- Demonstrates makeINTCON library and the critical section pattern.
-- A byte copy (src → dst) is wrapped in disable_ints / enable_ints.
--
-- Expected PIC18 output:
--   bcf  INTCON, 7, c    ; GIE = 0
--   movf src, w, c
--   movwf dst, c
--   bsf  INTCON, 7, c    ; GIE = 1
-- ---------------------------------------------------------------------------

def ex10_critical : Example :=
  let build : StoreM Hash := do
    let ic    ← makeINTCON 0xFF2
    let h_src  ← StoreM.node (.data .data .w8 0x20 "src")
    let h_dst  ← StoreM.node (.data .data .w8 0x21 "dst")
    let h_load ← StoreM.node (.proc #[h_src] #[] (.atomic (.abstract .load)  #[h_src] #[]) "load_src")
    let h_stor ← StoreM.node (.proc #[] #[h_dst] (.atomic (.abstract .store) #[] #[h_dst]) "store_dst")
    let h_body ← StoreM.node (.proc #[] #[] (.seq #[h_load, h_stor]) "copy_body")
    let h_crit ← StoreM.node (.proc #[] #[]
      (.seq #[ic.h_disable_ints, h_body, ic.h_enable_ints]) "critical_copy")
    StoreM.node (.proc #[] #[] (.seq #[h_crit]) "reset")
  let (h_reset, store) := StoreM.run build
  { name := "Ex10: Critical section  (BCF/BSF INTCON.GIE around copy)",
    store, ivt := #[(0, h_reset)] }

-- ---------------------------------------------------------------------------
-- Ex11: StaticAlloc — compiler-assigned RAM addresses (AIL#19)
--
-- Declares 4 statics (head, tail, data[8], temp) for a ring buffer.
-- Allocates from 0x20; verifies assigned addresses and checks that
-- an over-budget allocation produces RamBudgetExceeded.
-- ---------------------------------------------------------------------------

def runStaticAllocTest : IO Unit := do
  IO.println "=== Ex11: StaticAlloc  (compiler-assigned RAM addresses) ==="
  let decls : Array StaticDecl := #[
    { name := "head", width := .w8, count := 1 },
    { name := "tail", width := .w8, count := 1 },
    { name := "data", width := .w8, count := 8 },
    { name := "temp", width := .w8, count := 1 },
  ]
  -- Successful allocation: 11 bytes from 0x20, budget 0x10 (16 bytes)
  match allocateStatics decls 0x20 0x10 with
  | .error e => IO.println s!"  FAIL (unexpected error): {e}"
  | .ok (m, next) =>
      IO.println s!"  allocateStatics: PASS  (next free addr = {next})"
      for line in m.renderMapFile do IO.println s!"  {line}"
  -- Budget exceeded: same 11 bytes but budget = 0x08 (8 bytes)
  match allocateStatics decls 0x20 0x08 with
  | .error e => IO.println s!"  RamBudgetExceeded: PASS  ({e})"
  | .ok _    => IO.println   "  RamBudgetExceeded: FAIL (expected error but got ok)"

-- ---------------------------------------------------------------------------
-- Ex12: FSR conflict checker  (AIL#13)
--
-- Builds a minimal two-store scenario:
--   ISR  (vec 1): one intrinsic using FSR0 (simulates ring-buffer push)
--   Main (vec 0): one intrinsic using FSR0 (simulates pop — conflict!)
--                 one intrinsic using FSR1 (append — no conflict)
--
-- Expected output:
--   FSR conflict check: 1 conflict(s) found
--   FSR0 conflict: ISR node ... ↔ main node ...      ← pop vs. push
--   FSR1 check: PASS  (no conflict)
-- ---------------------------------------------------------------------------

def runFSRCheckTest : IO Unit := do
  IO.println "=== Ex12: FSR conflict check  (AIL#13) ==="
  let (_, store) := StoreM.run <| do
    -- ISR side: intrinsic claiming FSR0 (ring-buffer push skeleton)
    let _h_isr_push ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    0, _buf", "    movwf   INDF0, c"] #[] #[]
                  #["push byte via FSR0"] #[0])
      "isr_push")
    -- Main side: intrinsic claiming FSR0 (pop — conflict with isr_push)
    let _h_main_pop ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    0, _buf", "    movf    INDF0, w, c"] #[] #[]
                  #["pop byte via FSR0"] #[0])
      "main_pop")
    -- Main side: intrinsic claiming FSR1 (append — no conflict)
    let _h_main_append ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    1, _line", "    movwf   INDF1, c"] #[] #[]
                  #["append byte via FSR1"] #[1])
      "main_append")
    -- ISR proc: just the push
    let h_isr_body ← StoreM.node (.proc #[] #[] (.seq #[_h_isr_push]) "isr")
    -- Main proc: seq of pop and append
    let h_main_body ← StoreM.node (.proc #[] #[] (.seq #[_h_main_pop, _h_main_append]) "main")
    -- Return (isr_root, main_root) as a pair via a dummy proc — not needed;
    -- we capture the store and look up both roots separately.
    -- For this test we embed both hashes as seq steps of a top node.
    StoreM.node (.proc #[] #[] (.seq #[h_isr_body, h_main_body]) "top")
  -- The ISR root and main root are the two procs inside "top".
  -- Re-run to get individual hashes for the checker.
  let ((h_isr_root, h_main_root), store2) := StoreM.run <| do
    let h_push ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    0, _buf", "    movwf   INDF0, c"] #[] #[]
                  #["push byte via FSR0"] #[0])
      "isr_push")
    let h_pop ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    0, _buf", "    movf    INDF0, w, c"] #[] #[]
                  #["pop byte via FSR0"] #[0])
      "main_pop")
    let h_append ← StoreM.node (.proc #[] #[]
      (.intrinsic #["    lfsr    1, _line", "    movwf   INDF1, c"] #[] #[]
                  #["append byte via FSR1"] #[1])
      "main_append")
    let h_isr   ← StoreM.node (.proc #[] #[] (.seq #[h_push])          "isr")
    let h_main  ← StoreM.node (.proc #[] #[] (.seq #[h_pop, h_append]) "main")
    pure (h_isr, h_main)
  let _ := store  -- suppress unused warning
  let conflicts := FSRCheck.check store2 #[h_isr_root] #[h_main_root]
  -- Expected: 1 conflict (FSR0 between push and pop); FSR1 is clean.
  let fsr0conflicts := conflicts.filter (·.fsr == 0)
  let fsr1conflicts := conflicts.filter (·.fsr == 1)
  IO.println s!"  FSR conflict check: {conflicts.size} conflict(s) found"
  for c in conflicts do
    IO.println s!"  {FSRCheck.renderConflict c}"
  let fsr0ok := fsr0conflicts.size == 1
  let fsr1ok := fsr1conflicts.isEmpty
  let pass := "PASS"; let fail := "FAIL"
  IO.println s!"  FSR0 conflict: {if fsr0ok then pass else fail}"
  IO.println s!"  FSR1 clean:    {if fsr1ok then pass else fail}"

-- ---------------------------------------------------------------------------
-- Ex13: Structured diagnostics  (AIL#16)
--
-- Demonstrates that checkStore emits a Diagnostic (JSON) on failure and
-- that readClearsWarnings emits structured records with fix suggestions.
--
-- Scenario A — TypeCheckFailure:
--   A proc whose reads array contains a hash absent from the store.
--   inferTy returns none → checkStore emits kind=TypeCheckFailure.
--
-- Scenario B — ReadClearsUnacked (already exercised by Ex06, now verified as
--   structured JSON):
--   A proc that reads a read_clears peripheral via .load.
--   readClearsWarnings emits kind=ReadClearsUnacked with a UseLoadDiscard fix.
--
-- Expected for A:  "kind":"TypeCheckFailure", "severity":"error"
-- Expected for B:  "kind":"ReadClearsUnacked", "severity":"warning",
--                  "fix":{"UseLoadDiscard":...}
-- ---------------------------------------------------------------------------

def runDiagnosticsTest : IO Unit := do
  IO.println "=== Ex13: Structured diagnostics  (AIL#16) ==="
  let pass := "PASS"; let fail := "FAIL"
  -- -------------------------------------------------------------------------
  -- Scenario A: TypeCheckFailure — proc references a hash not in the store
  -- -------------------------------------------------------------------------
  let phantom_h : Hash := 0xDEADBEEFCAFE0001  -- deliberately absent
  let (h_bad, s_bad) := StoreM.run <| do
    let h ← StoreM.node (.proc #[] #[]
      (.atomic (.abstract .load) #[phantom_h] #[]) "bad_load")
    pure h
  match checkStore targetConfig s_bad with
  | .error diag =>
      IO.println "  typecheck-fail diagnostic:"
      IO.println s!"  {diag.toJson}"
      let ok := diag.kind == DiagnosticKind.TypeCheckFailure
              && diag.severity == Severity.error
              && diag.nodeHash == h_bad
      IO.println s!"  TypeCheckFailure: {if ok then pass else fail}"
  | .ok _ =>
      IO.println s!"  TypeCheckFailure: {fail}  (expected error, got ok)"
  -- -------------------------------------------------------------------------
  -- Scenario B: ReadClearsUnacked — load on a read_clears peripheral
  -- -------------------------------------------------------------------------
  let (h_load_b, s_b) := StoreM.run <| do
    let h_reg ← StoreM.node (.peripheral .sfr 0x400
      { readable := true, writable := false,
        sideEffectOnRead := true, sideEffectOnWrite := false, accessWidth := .w8 }
      "RC_REG")
    let h ← StoreM.node (.proc #[] #[] (.atomic (.abstract .load) #[h_reg] #[]) "read_rc")
    pure h
  let warns_b := readClearsWarnings s_b
  match warns_b[0]? with
  | none =>
      IO.println s!"  ReadClearsUnacked: {fail}  (no warnings emitted)"
  | some diag =>
      IO.println "  read-clears diagnostic:"
      IO.println s!"  {diag.toJson}"
      let fixOk := match diag.fix with
        | some (FixSuggestion.useLoadDiscard h) => h == h_load_b
        | _ => false
      let ok := diag.kind == DiagnosticKind.ReadClearsUnacked
              && diag.severity == Severity.warning
              && diag.nodeHash == h_load_b
              && fixOk
      IO.println s!"  ReadClearsUnacked: {if ok then pass else fail}"

-- ---------------------------------------------------------------------------
-- Ex14: Capability record  (AIL#17)
--
-- Verifies that pic18Capabilities.toJson produces well-formed JSON with the
-- expected keys and at least one known entry in each array.
--
-- Checks:
--   1. JSON contains "schemaVersion"
--   2. JSON contains "target":"pic18"
--   3. procBodyForms includes "atomic" and "intrinsic"
--   4. abstractOps  includes "load" and "movImm"
--   5. nodeTypes    includes "proc"
--   6. limitations  is non-empty
-- ---------------------------------------------------------------------------

-- strHas: true iff `sub` appears in `s`.
-- Uses splitOn: a single-element result means no split occurred (sub absent).
private def strHas (s sub : String) : Bool :=
  match s.splitOn sub with
  | [_] => false
  | _   => true

def runCapabilityTest : IO Unit := do
  IO.println "=== Ex14: Capability record  (AIL#17) ==="
  let pass := "PASS"; let fail := "FAIL"
  let r   := pic18Capabilities
  let js  := r.toJson
  IO.println s!"  JSON: {js}"
  let chk1 : Bool := strHas js "\"schemaVersion\""
  let chk2 : Bool := strHas js "\"target\":\"pic18\""
  let chk3 : Bool := r.procBodyForms.any (· == "atomic")
                  && r.procBodyForms.any (· == "intrinsic")
  let chk4 : Bool := r.abstractOps.any (· == "load")
                  && r.abstractOps.any (· == "movImm")
  let chk5 : Bool := r.nodeTypes.any (· == "proc")
  let chk6 : Bool := !r.limitations.isEmpty
  IO.println s!"  schemaVersion key present        : {if chk1 then pass else fail}"
  IO.println s!"  target=pic18                     : {if chk2 then pass else fail}"
  IO.println s!"  procBodyForms (atomic,intrinsic) : {if chk3 then pass else fail}"
  IO.println s!"  abstractOps (load,movImm)        : {if chk4 then pass else fail}"
  IO.println s!"  nodeTypes (proc)                 : {if chk5 then pass else fail}"
  IO.println s!"  limitations non-empty            : {if chk6 then pass else fail}"

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

def main : IO Unit := do
  let examples := [ex01_copy, ex02_add, ex03_cond, ex04_loop, ex05_two_vec,
                   ex07_index_copy, ex06_uart_rx, ex08_ringbuf, ex09_main_loop,
                   ex10_critical]
  for ex in examples do
    runExample ex
    IO.println ""
  runStaticAllocTest
  IO.println ""
  runFSRCheckTest
  IO.println ""
  runDiagnosticsTest
  IO.println ""
  runCapabilityTest
  IO.println ""
