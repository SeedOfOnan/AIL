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
  | .error (_, h) =>
      IO.println s!"  checkStore: FAIL  (type error at hash {h})"
  | .ok tyEnv =>
      IO.println   "  checkStore: PASS"
      let warns := readClearsWarnings ex.store
      for w in warns do
        IO.println s!"  {w}"
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
  -- Represented by its base address node only; FSR indirect used in intrinsics.
  -- TODO: replace with Node.staticArray once AIL#4 is implemented.
  let n_rx_data    : Node := .data .data .w8 0x23 "rx_buf_data"
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
                #["halt: never returns"]) "panic"
  let h_panic := hashNode n_panic

  -- early_retfie: return from ISR without continuing the handler body.
  -- Used after FERR discard and after ring-buffer-full detection.
  let n_early_retfie : Node := .proc #[] #[]
    (.intrinsic #["    retfie  0"] #[] #[]
                #["early ISR exit"]) "early_retfie"
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
  let n_test_is_full : Node := .proc #[] #[h_bool_2]
    (.intrinsic
      #["    incf    _rx_tail, w, c",
        "    andlw   0x1f",
        "    cpfseq  _rx_head, c"]
      #[h_rx_head, h_rx_tail] #[]
      #["condition: (tail+1)&31 == head (buffer full)"]) "test_is_full"
  let h_test_is_full := hashNode n_test_is_full

  -- set_overrun_and_retfie: set the overrun flag and exit ISR (drop the byte).
  let n_set_overrun : Node := .proc #[] #[]
    (.intrinsic
      #["    setf    _rx_overrun, c",
        "    retfie  0"]
      #[] #[h_rx_overrun]
      #["set overrun flag; drop received byte; exit ISR"]) "set_overrun"
  let h_set_overrun := hashNode n_set_overrun

  -- do_push: write WREG (received byte) to buf[tail] via FSR0 indirect; advance tail.
  -- WREG must hold the received byte on entry (loaded by the preceding read_rcreg).
  let n_do_push : Node := .proc #[] #[]
    (.intrinsic
      #["    movlb   _rx_data >> 8",
        "    movlw   _rx_data & 0xff",
        "    addwf   _rx_tail, w, c",
        "    movwf   FSR0L, c",
        "    clrf    FSR0H, c",
        "    movwf   INDF0",
        "    incf    _rx_tail, f, c",
        "    movlw   0x1f",
        "    andwf   _rx_tail, f, c"]
      #[h_rx_tail, h_rx_data] #[h_rx_tail]
      #["push WREG to buf[tail]; advance tail mod 32"]) "do_push"
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
  let s := Store.insert s           h_do_push           n_do_push
  let s := Store.insert s           h_if_full           n_if_full
  let s := Store.insert s           h_isr               n_isr
  { name  := "Ex06: UART receive ISR  (PIC18, high-priority vec 1)",
    store := s,
    ivt   := #[(1, h_isr)] }

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

def main : IO Unit := do
  let examples := [ex01_copy, ex02_add, ex03_cond, ex04_loop, ex05_two_vec,
                   ex06_uart_rx]
  for ex in examples do
    runExample ex
    IO.println ""
