-- ailc: AIL compiler entry point
-- Currently: emits PIC18 assembly for a hardcoded test store to stdout.
-- Usage: lake exe ailc > output.s
import AIL
import AIL.Targets.PIC18.Emitter

open AIL AIL.PIC18

-- ---------------------------------------------------------------------------
-- Test store: load/store chain using the morphism model.
--
-- Program:
--   src at 0x20 (pre-initialized to 0x37 by test harness)
--   dst at 0x21
--
--   load_src: atomic .load; params=[src] rets=[]
--     emits: MOVF src, W
--     type:  proc [Ty.data .data .w8] [] 0
--
--   store_dst: atomic .store; params=[] rets=[dst]
--     emits: MOVWF dst
--     type:  proc [] [Ty.data .data .w8] 0
--
--   reset: seq [load_src, store_dst]; params=[] rets=[]
--     type:  proc [] [] 0
--
-- IVT: [(0, h_reset)] — vector 0 is the reset entry (classic PIC18: 0x0000).
-- The C test wrapper calls _ail_vec0 (extern void ail_vec0(void)).
--
-- Observable: after execution, W == 0x37 and RAM[0x21] == 0x37.
-- ---------------------------------------------------------------------------

private def buildTestStore : Store × Array IVTEntry :=
  -- Data nodes (concrete memory locations with known addresses)
  let n_src   : Node := .data .data .w8 0x20 "src"
  let h_src   := hashNode n_src
  let n_dst   : Node := .data .data .w8 0x21 "dst"
  let h_dst   := hashNode n_dst
  -- load_src: reads src (params=[src]), produces nothing (rets=[])
  let n_load  : Node := .proc #[h_src] #[]
                          (.atomic (.abstract .load) #[h_src] #[])
                          "load_src"
  let h_load  := hashNode n_load
  -- store_dst: reads nothing (params=[]), writes dst (rets=[dst])
  let n_stor  : Node := .proc #[] #[h_dst]
                          (.atomic (.abstract .store) #[] #[h_dst])
                          "store_dst"
  let h_stor  := hashNode n_stor
  -- reset: seq [load_src, store_dst]; the reset entry proc (no params, no rets)
  let n_reset : Node := .proc #[] #[] (.seq #[h_load, h_stor]) "reset"
  let h_reset := hashNode n_reset
  -- Build store in dependency order (leaves first)
  let store   := Store.insert Store.empty h_src   n_src
  let store   := Store.insert store       h_dst   n_dst
  let store   := Store.insert store       h_load  n_load
  let store   := Store.insert store       h_stor  n_stor
  let store   := Store.insert store       h_reset n_reset
  -- IVT: vector 0 (reset) → h_reset
  let ivt     : Array IVTEntry := #[(0, h_reset)]
  (store, ivt)

def main : IO Unit := do
  let (store, ivt) := buildTestStore
  match checkStore targetConfig store with
  | .error (_, badHash) =>
      IO.eprintln s!"ailc: type error at hash {badHash}"
      IO.Process.exit 1
  | .ok tyEnv =>
  -- Report inferred types to stderr.
  IO.eprintln ";--- inferred types ---"
  for (h, _) in store do
    match tyEnv h with
    | some t => IO.eprintln s!"; {h} : {repr t}"
    | none   => IO.eprintln s!"; {h} : <no type>"
  IO.eprintln ";----------------------"
  match compile store tyEnv ivt with
  | .error msg =>
      IO.eprintln s!"ailc: emit error: {msg}"
      IO.Process.exit 1
  | .ok lines =>
      -- Code section header (XC8 PIC Assembler, PIC18).
      -- reloc=2: required for PIC18 — instructions must be word-aligned.
      -- class=CODE: places this psect in program memory.
      IO.println "    PSECT   ailCode,class=CODE,reloc=2"
      -- _ail_vec0 is the stable entry label for the reset proc.
      -- C test wrapper: extern void ail_vec0(void);
      IO.println "    global  _ail_vec0"
      for line in lines do
        IO.println line
