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
-- Entry point
-- ---------------------------------------------------------------------------

def main : IO Unit := do
  let examples := [ex01_copy, ex02_add, ex03_cond, ex04_loop, ex05_two_vec]
  for ex in examples do
    runExample ex
    IO.println ""
