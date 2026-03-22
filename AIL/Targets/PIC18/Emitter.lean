-- AIL.Targets.PIC18.Emitter
-- PIC18 (8-bit Harvard) code emitter for AIL.
--
-- Walks the AIL content-addressed store from a root Hash and emits
-- XC8 PIC Assembler-compatible PIC18 assembly text.
--
-- TIER: Tier 1 only. No Core module may import this file.
-- See docs/TIERS.md for the separation discipline.
--
-- OUTPUT FORMAT: XC8 PIC Assembler-compatible assembly lines (Array String).
-- The caller joins with newlines and feeds to xc8-cc / xc8-as.
--
-- KNOWN LIMITATIONS / TODOs (each marked inline):
--   - Banked RAM access (BSR not managed; only Access Bank 0x00–0xFF supported)
--   - testBit bit-index must be a compile-time constant (dynamic not supported)
--   - Flag-producing ops supported in cond/whileLoop via emitFlagSkip (AIL#31)
--   - Interrupt handler context save/restore not yet emitted
--   - Loop bound decrement not yet a typed instruction (emitted as comment)
--   - NameTable not consulted for callee labels (uses hash-derived labels)
--   - Intrinsic instructions emitted as comments (pending typed Insn migration)
--   - No deduplication of shared subroutines beyond the visited-hash set
--   - Subroutine ordering bug: callees emitted inline, not scheduled after RETURN

import AIL.Core.Types
import AIL.Targets.PIC18.ISA

namespace AIL.PIC18

-- ---------------------------------------------------------------------------
-- PIC18 target configuration
-- ---------------------------------------------------------------------------

/-- TargetConfig for the PIC18F26/46/56Q71.
    The Q71 has a 127-level hardware call stack (STKPTR is 7 bits, range 0–127;
    the 128th push sets STKOVF). Source: DS40002329F §9.1.3.
    NOTE: Classic PIC18C devices (reference manual DS39500A) have only 31 levels.
    This config is Q71-specific. -/
def targetConfig : TargetConfig := { maxCallDepth := 127 }

-- ---------------------------------------------------------------------------
-- Emitter state and monad
-- ---------------------------------------------------------------------------

/-- Emitter state. Threaded through the emission pass via StateT. -/
structure EmitState where
  /-- Accumulated output instructions, in emission order. -/
  insns          : Array Insn   := #[]
  /-- Counter for generating unique branch/loop labels. -/
  nextLbl        : Nat          := 0
  /-- Hashes already emitted as subroutines. Prevents duplicate emission
      when multiple call sites share the same callee. -/
  visited        : Array Hash   := #[]
  /-- EQU declarations for data and peripheral nodes, emitted as a data section
      before the code section. Collected during the emit pass. -/
  dataDecls      : Array String := #[]
  /-- Hashes already added to dataDecls. Prevents duplicate EQU emission when
      the same data or peripheral node is referenced from multiple ops. -/
  declaredHashes : Array Hash   := #[]
  /-- The store being compiled (read-only). -/
  store          : Store
  /-- Type environment for the store (read-only). -/
  tyEnv          : TyEnv
  /-- Named roots: when a hash appears here, its name is emitted as a label
      alias alongside the hash label (AIL#25). -/
  nameTable      : NameTable := NameTable.empty
  /-- Current BSR (Bank Select Register) value, if known (AIL#24).
      `none` = unknown (e.g. at ISR entry or after a call that may change BSR).
      The emitter tracks this to avoid redundant MOVLB instructions. -/
  currentBSR     : Option UInt8 := none

/-- The emitter monad: mutable state + error reporting. -/
abbrev Emit := StateT EmitState (Except String)

-- ---------------------------------------------------------------------------
-- Emitter primitives
-- ---------------------------------------------------------------------------

private def out (i : Insn) : Emit Unit :=
  modify fun s => { s with insns := s.insns.push i }

private def outComment (t : String) : Emit Unit := out (.comment t)

private def freshLabel (pfx : String) : Emit String := do
  let n := (← get).nextLbl
  modify fun s => { s with nextLbl := s.nextLbl + 1 }
  return s!"_{pfx}_{n}"

private def lookupNode (h : Hash) : Emit Node := do
  match (← get).store.lookup h with
  | some n => return n
  | none   => throw s!"emitter: hash {h} not in store"

private def markVisited (h : Hash) : Emit Unit :=
  modify fun s => { s with visited := s.visited.push h }

private def wasVisited (h : Hash) : Emit Bool := do
  return (← get).visited.contains h

-- hashLabel is defined in AIL.Core.Hash (public); used here and in node constructors.

/-- Emit a label for each NameTable entry whose hash matches h.
    These are alias labels: the hash label is always emitted first, then any
    human-readable names follow.  Callers (CALL/GOTO) always use hash labels
    for stability; named labels are for linker scripts and debuggers. -/
private def emitNamedLabels (h : Hash) : Emit Unit := do
  let nt := (← get).nameTable
  for entry in nt do
    if entry.hash == h then out (.lbl entry.name)

-- ---------------------------------------------------------------------------
-- Data / peripheral node helpers
-- ---------------------------------------------------------------------------

private def renderWidth : Width → String
  | .w8  => "u8"
  | .w16 => "u16"
  | .w32 => "u32"

private def renderAddrSpace : AddrSpace → String
  | .data    => "data"
  | .program => "prog"
  | .sfr     => "sfr"

-- ---------------------------------------------------------------------------
-- Address resolution and bank-select (AIL#24)
--
-- resolveAddr declares an EQU for a data/peripheral/staticArray node and
-- returns (symbol, fullAddr).
--
-- PIC18 Access Bank:
--   0x00–0xFF — directly accessible with ',c' qualifier; no BSR needed.
-- Banked GPR (address >= 0x100):
--   bank   = (addr >> 8) & 0xF  — selects BSR value (MOVLB)
--   offset = addr & 0xFF         — 8-bit file register offset within the bank
--   EQU declares the offset so instruction operands are in range.
--   The full address is preserved in the EQU comment.
--
-- emitBankSelect: given a full address, emits MOVLB if BSR doesn't match,
-- updates EmitState.currentBSR, and returns the appropriate access qualifier.
-- ---------------------------------------------------------------------------

/-- Resolve a data/peripheral/staticArray node to its assembly symbol.
    Returns (symbol, fullAddr).  Declares the EQU in the data section
    the first time this hash is seen.
    For banked addresses (>= 0x100) the EQU holds the low byte (register
    offset within the bank); the full address is noted in the comment. -/
private def resolveAddr (h : Hash) : Emit (String × UInt32) := do
  let sym := hashLabel h
  -- Only add to data section once per hash.
  if (← get).declaredHashes.contains h then do
    -- Still need to return the address.
    let addr : UInt32 ← match ← lookupNode h with
      | Node.data _ _ a _         => return (sym, a)
      | Node.peripheral _ a _ _   => return (sym, a)
      | Node.staticArray _ _ a _ _ => return (sym, a)
      | _ => throw s!"emitter: hash {h} is not a data, peripheral, or staticArray node"
    return (sym, addr)
  match ← lookupNode h with
  | Node.data addrSpace width addr lbl =>
      let equVal := addr &&& 0xFF  -- low byte for banked; same as addr for access bank
      let decl := s!"{sym}\tequ\t{equVal.toNat}\t; {lbl} ({renderWidth width}, {renderAddrSpace addrSpace})" ++
                  (if addr.toNat >= 0x100 then s!" [full: 0x{String.ofList (Nat.toDigits 16 addr.toNat)}]" else "")
      modify fun s => { s with
        dataDecls      := s.dataDecls.push decl
        declaredHashes := s.declaredHashes.push h }
      return (sym, addr)
  | Node.peripheral addrSpace addr _ lbl =>
      let equVal := addr &&& 0xFF
      let decl := s!"{sym}\tequ\t{equVal.toNat}\t; sfr: {lbl} ({renderAddrSpace addrSpace})" ++
                  (if addr.toNat >= 0x100 then s!" [full: 0x{String.ofList (Nat.toDigits 16 addr.toNat)}]" else "")
      modify fun s => { s with
        dataDecls      := s.dataDecls.push decl
        declaredHashes := s.declaredHashes.push h }
      return (sym, addr)
  | Node.staticArray _ _ addr _ lbl =>
      let equVal := addr &&& 0xFF
      let decl := s!"{sym}\tequ\t{equVal.toNat}\t; array base: {lbl}" ++
                  (if addr.toNat >= 0x100 then s!" [full: 0x{String.ofList (Nat.toDigits 16 addr.toNat)}]" else "")
      modify fun s => { s with
        dataDecls      := s.dataDecls.push decl
        declaredHashes := s.declaredHashes.push h }
      return (sym, addr)
  | _ =>
      throw s!"emitter: hash {h} is not a data, peripheral, or staticArray node"

/-- Emit MOVLB if the address is banked and BSR doesn't already point to the
    correct bank.  Returns the XC8 access qualifier: "c" for access bank,
    "b" for banked.  Updates EmitState.currentBSR. -/
private def emitBankSelect (addr : UInt32) : Emit String := do
  if addr.toNat < 0x100 then
    return "c"   -- access bank: no MOVLB needed
  else
    let bank : UInt8 := ((addr >>> 8) &&& 0xF).toUInt8
    let cur := (← get).currentBSR
    if cur != some bank then
      out (.movlb bank)
      modify fun s => { s with currentBSR := some bank }
    return "b"

/-- Shorthand: resolve address + emit bank-select + return (symbol, qualifier). -/
private def resolveWithBank (h : Hash) : Emit (String × String) := do
  let (sym, addr) ← resolveAddr h
  let qual ← emitBankSelect addr
  return (sym, qual)

-- ---------------------------------------------------------------------------
-- Flag output support (AIL#31)
-- ---------------------------------------------------------------------------

/-- Bit position of each FlagKind in the PIC18 STATUS register (DS40002329F §3.7.1).
    STATUS is at SFR address 0xFD8; all five flags are in the low 5 bits. -/
def flagBitPos : FlagKind → UInt8
  | .C  => 0
  | .DC => 1
  | .Z  => 2
  | .OV => 3
  | .N  => 4

-- The PIC18 STATUS register symbol. Predefined by the XC8 assembler; no EQU needed.
private def statusRegSym : String := "STATUS"

/-- The STATUS flags produced by each AbstractOp on PIC18.
    Conservative: only flags that are definitely set by the instruction.
    Used to validate FormalKind.flag rets (FlagNotProduced diagnostic — TODO: enforce).
    Source: PIC18 Instruction Set Summary (DS39500A / DS40002329F). -/
def flagOutputs : AbstractOp → Array FlagKind
  | .load        => #[.Z, .N]   -- MOVF f,W: sets Z, N
  | .loadDiscard => #[.Z, .N]   -- same instruction
  | .add         => #[.C, .DC, .Z, .OV, .N]  -- ADDWF
  | .sub         => #[.C, .DC, .Z, .OV, .N]  -- SUBWF
  | .and         => #[.Z, .N]   -- ANDWF
  | .or          => #[.Z, .N]   -- IORWF
  | .xor         => #[.Z, .N]   -- XORWF
  | .addImm _    => #[.C, .DC, .Z, .OV, .N]  -- ADDLW
  | .xorImm _    => #[.Z, .N]   -- XORLW
  | .andImm _    => #[.Z, .N]   -- ANDLW
  | .movImm _    => #[]          -- MOVLW does NOT affect STATUS
  | .compare      => #[]         -- CPFSEQ is a skip; does not set STATUS flags
  | .compareImm _ => #[]         -- MOVLW+CPFSEQ is a skip; does not set STATUS flags
  | _             => #[]

/-- After emitting a flag-producing atomic proc as a condition test, append
    BTFSS STATUS, bit if the proc declares a FormalKind.flag ret.
    This completes the PIC18 skip protocol for cond/whileLoop:
      <arithmetic op>   ; sets STATUS flags as a side effect
      btfss STATUS, N   ; skip GOTO when condition is TRUE (flag is set)
      goto _else        ; taken when FALSE
    Only acts on ProcBody.atomic procs with non-skip ops; all other body forms
    (seq, testBit, compare) are assumed to already end with a skip instruction. -/
private def emitFlagSkip (testH : Hash) : Emit Unit := do
  match ← lookupNode testH with
  | Node.proc _ rets (ProcBody.atomic (.abstract op) _ _) _ =>
      -- Direct-skip ops (testBit, compare) already emit a PIC18 skip instruction;
      -- do not add a redundant BTFSS.
      match op with
      | .testBit | .compare | .compareImm _ => return
      | _ =>
          -- Find the first flag-kind ret and emit BTFSS STATUS, bit.
          for retH in rets do
            match ← lookupNode retH with
            | Node.formal _ (.flag f) =>
                out (.btfss statusRegSym (flagBitPos f))
                return
            | _ => pure ()
  | _ => pure ()

-- Resolve a bitField node to (register_symbol, bit_position).
-- Used by testBit, setBit, clearBit op emitters.
private def resolveBitField (h : Hash) : Emit (String × UInt8) := do
  match ← lookupNode h with
  | Node.bitField regH bitPos _ =>
      let (sym, _) ← resolveAddr regH
      return (sym, bitPos)
  | _ => throw s!"emitter: hash {h} is not a bitField node"

-- ---------------------------------------------------------------------------
-- Op emission (from ProcBody.atomic)
-- ---------------------------------------------------------------------------

private def emitOp (ref : OpRef) (reads writes : Array Hash) : Emit Unit := do
  match ref with
  | .abstract op =>
      match op with
      | .load | .loadDiscard =>
          -- MOVF src, W, c/b  — load byte to WREG.
          -- loadDiscard: same instruction; the distinction is in the type checker
          -- (load on a read_clears peripheral warns if result is untracked;
          --  loadDiscard suppresses that warning — explicit intentional discard).
          -- Bank-select: for addresses >= 0x100, emit MOVLB and use banked mode (AIL#24).
          let (src, qual) ← resolveWithBank (← reads[0]? |>.elim (throw "load: no source") pure)
          out (.movf src .w (qual == "b"))
      | .store   =>
          -- MOVWF dst, c/b  — WREG → dst  (caller loads WREG via a prior .load)
          let (dst, qual) ← resolveWithBank (← writes[0]? |>.elim (throw "store: no dest") pure)
          out (.movwf dst (qual == "b"))
      | .add     =>
          -- ADDWF f, F  — f + WREG → f  (second operand already in WREG).
          -- Access Bank only (arithmetic ops on banked RAM require future BANKSEL support).
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "add: no operand") pure)
          out (.addwf f .f)
      | .sub     =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "sub: no operand") pure)
          out (.subwf f .f)
      | .mul     =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "mul: no operand") pure)
          out (.mulwf f)
      | .and     =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "and: no operand") pure)
          out (.andwf f .f)
      | .or      =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "or: no operand") pure)
          out (.iorwf f .f)
      | .xor     =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "xor: no operand") pure)
          out (.xorwf f .f)
      | .not     =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "not: no operand") pure)
          out (.comf f .f)
      | .shiftL  =>
          -- PIC18 has no barrel shifter; single-bit left rotate only.
          -- Multi-bit shifts must use multiple ops or an Intrinsic.
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "shiftL: no operand") pure)
          out (.rlncf f .f)
      | .shiftR  =>
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "shiftR: no operand") pure)
          out (.rrncf f .f)
      | .testBit =>
          -- BTFSS f, b  — skip next instruction if bit b of f is SET.
          -- In the cond skip-style protocol: skip happens when condition is TRUE,
          -- so thenB executes when the bit is set. reads[0] must be a bitField node.
          let (f, b) ← resolveBitField (← reads[0]? |>.elim (throw "testBit: no bitField") pure)
          out (.btfss f b)
      | .setBit =>
          -- BSF f, b  — set bit b of f.  writes[0] must be a bitField node.
          let (f, b) ← resolveBitField (← writes[0]? |>.elim (throw "setBit: no bitField") pure)
          out (.bsf f b)
      | .clearBit =>
          -- BCF f, b  — clear bit b of f.  writes[0] must be a bitField node.
          let (f, b) ← resolveBitField (← writes[0]? |>.elim (throw "clearBit: no bitField") pure)
          out (.bcf f b)
      | .compare =>
          -- CPFSEQ f, c  — skip if f == WREG.
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "compare: no operand") pure)
          out (.cpfseq f)
      | .indexLoad =>
          -- FSR0-indirect read: WREG = array[index].
          -- reads[0] = staticArray node (base address), reads[1] = index node.
          -- LFSR 0, base  → FSR0 = base_address
          -- MOVF idx, W   → WREG = index
          -- ADDWF FSR0L,F → FSR0L += index  (assumes no carry into FSR0H)
          -- MOVF INDF0, W → WREG = *(FSR0)
          -- TODO: handle carry into FSR0H for arrays that cross a 256-byte boundary.
          let (arrSym, _) ← resolveAddr (← reads[0]? |>.elim (throw "indexLoad: no array") pure)
          let (idxSym, _) ← resolveAddr (← reads[1]? |>.elim (throw "indexLoad: no index") pure)
          out (.lfsr 0 arrSym)
          out (.movf idxSym .w)
          out (.addwf "FSR0L" .f)
          out (.movf "INDF0" .w)
      | .indexStore =>
          -- FSR0-indirect write: array[index] = WREG.
          -- reads[0] = staticArray node, reads[1] = index node.
          -- WREG must hold the value to write on entry to this op.
          -- LFSR 0, base  → FSR0 = base_address
          -- MOVF idx, W   → WREG = index  (NOTE: overwrites the value in WREG!)
          -- ADDWF FSR0L,F → FSR0L += index
          -- MOVWF INDF0   → *(FSR0) = WREG
          -- TODO: caller must reload value into WREG after the index computation.
          --       This is a known limitation of the implicit WREG convention;
          --       resolves when SSA wiring tracks WREG explicitly.
          let (arrSym, _) ← resolveAddr (← reads[0]? |>.elim (throw "indexStore: no array") pure)
          let (idxSym, _) ← resolveAddr (← reads[1]? |>.elim (throw "indexStore: no index") pure)
          out (.lfsr 0 arrSym)
          out (.movf idxSym .w)
          out (.addwf "FSR0L" .f)
          out (.movwf "INDF0")
      | .xorImm k => out (.xorlw k)
      | .addImm k => out (.addlw k)
      | .andImm k => out (.andlw k)
      | .movImm k => out (.movlw k)
      | .compareImm k =>
          -- Compare reads[0] with literal k: skip if equal.
          -- MOVLW k     — load the constant into WREG
          -- CPFSEQ f    — skip next instruction if f == WREG
          -- This is the skip-when-TRUE protocol; elseB/whileDone follows as the skipped insn.
          let (f, _) ← resolveAddr (← reads[0]? |>.elim (throw "compareImm: no operand") pure)
          out (.movlw k)
          out (.cpfseq f)
  | .intrinsic ih =>
      -- Inline an intrinsic proc's instruction sequence.
      -- The hash must point to a Node.proc with ProcBody.intrinsic body.
      -- Obligations emitted as comments; instructions emitted verbatim via Insn.raw.
      -- Symbol names in instruction strings must use hashLabel format (_n<hash>).
      match ← lookupNode ih with
      | Node.proc _ _ (ProcBody.intrinsic instructions _ _ obligations _) label =>
          outComment s!" [intrinsic: {label}]"
          for obl in obligations do outComment s!"   obligation: {obl}"
          for insn in instructions do out (.raw insn)
      | _ => throw s!"emitter: OpRef.intrinsic {ih} does not name a proc with intrinsic body"

-- ---------------------------------------------------------------------------
-- Node emission  (inline + subroutine)
-- emitNode, emitProcBody, and emitSubroutine are mutually recursive:
--   emitNode dispatches on Node; for Node.proc it calls emitProcBody.
--   emitProcBody handles ProcBody variants; for call it calls emitSubroutine.
--   emitSubroutine emits a labeled wrapper and calls emitNode for the body.
-- ---------------------------------------------------------------------------

mutual

partial def emitNode (h : Hash) : Emit Unit := do
  let n ← lookupNode h
  match n with

  | Node.data _ _ _ _ =>
      -- Ensure this node is declared in the data section (EQU).
      -- No code is emitted: a data node is a location, not a computation.
      let (_, _) ← resolveAddr h

  | Node.peripheral _ _ _ _ =>
      -- Ensure this SFR is declared in the data section (EQU).
      -- No code is emitted: peripheral nodes are address equates only.
      let (_, _) ← resolveAddr h

  | Node.staticArray _ _ _ _ _ =>
      -- Declare the array base address as an EQU in the data section.
      -- No code emitted: a staticArray is a location, not a computation.
      let (_, _) ← resolveAddr h

  | Node.bitField regH _ _ =>
      -- Ensure the parent register is declared in the data section.
      -- No code emitted: a bitField is a location, not a computation.
      let (_, _) ← resolveAddr regH

  | Node.formal _ _ =>
      -- Formal nodes are typed placeholders; no code emitted.
      -- At call sites, formals are substituted with actuals via args/retBinds.
      pure ()

  | Node.proc params _ body _ =>
      emitProcBody params body

-- Emit the instructions for a ProcBody.
-- `params` is the containing proc's params array (needed for loop bounds).
partial def emitProcBody (params : Array Hash) (body : ProcBody) : Emit Unit := do
  match body with

  | ProcBody.atomic ref reads writes =>
      emitOp ref reads writes

  | ProcBody.seq steps =>
      for stepHash in steps do
        emitNode stepHash

  | ProcBody.cond test thenB elseB =>
      -- PIC18 condition model: the test proc ends with a skip instruction
      -- (BTFSC / CPFSEQ / etc.) that skips one instruction when true.
      -- We emit GOTO else as the "skipped" instruction, fall through to then.
      -- For flag-producing ops (xorImm, addImm, etc.) emitFlagSkip appends
      -- BTFSS STATUS, bit to complete the skip protocol (AIL#31).
      let lblElse ← freshLabel "else"
      let lblEnd  ← freshLabel "end"
      emitNode test
      emitFlagSkip test        -- no-op if test already ends with a skip insn
      out (.goto_ lblElse)     -- skipped when condition is true
      emitNode thenB
      out (.goto_ lblEnd)
      out (.lbl lblElse)
      emitNode elseB
      out (.lbl lblEnd)

  | ProcBody.loop body =>
      -- Decrement-and-branch loop.
      -- The containing proc's params[0] is the loop bound (a data node).
      -- bound is decremented each iteration; loop exits when it reaches 0.
      -- TODO: 16/32-bit bounds require multi-byte decrement.
      let lblTop ← freshLabel "loop"
      let boundH ← match params[0]? with
        | some h => pure h
        | none   => throw "emitter: ProcBody.loop proc has no params[0] (loop bound)"
      let (addr, _) ← resolveAddr boundH
      out (.lbl lblTop)
      emitNode body
      out (.decfsz addr .f)    -- decrement; skip BRA when bound reaches 0
      out (.bra lblTop)

  | ProcBody.forever body =>
      -- Unconditional infinite loop.
      -- Emits: top_label: <body inlined>; goto top_label
      -- Body is inlined (not called as a subroutine) to avoid CALL overhead on
      -- the hot path. Use ProcBody.call inside a forever body for subroutine calls.
      let lblTop ← freshLabel "forever"
      out (.lbl lblTop)
      emitNode body
      out (.goto_ lblTop)

  | ProcBody.whileLoop cond body =>
      -- Conditional loop: execute body while cond evaluates to TRUE.
      -- Uses the PIC18 skip protocol: the cond proc ends with a skip instruction
      -- that skips the next instruction when the condition is TRUE.
      -- Emitted as:
      --   _while_N:
      --     <cond>               ; ends with skip-when-TRUE instruction
      --     goto _whileDone_N    ; executed when FALSE (exit); SKIPPED when TRUE
      --     <body>               ; executes when TRUE
      --     goto _while_N        ; loop back
      --   _whileDone_N:
      let lblTop  ← freshLabel "while"
      let lblDone ← freshLabel "whileDone"
      out (.lbl lblTop)
      emitNode cond
      emitFlagSkip cond      -- no-op if cond already ends with a skip insn (AIL#31)
      out (.goto_ lblDone)   -- skipped when condition TRUE (fall through to body)
      emitNode body
      out (.goto_ lblTop)
      out (.lbl lblDone)

  | ProcBody.call callee _args _retBinds callDepth =>
      -- Emit a CALL to the callee subroutine.
      -- args/retBinds are type-checked by checkStore. At this point the emitter
      -- relies on the caller having pre-populated shared memory locations.
      -- TODO: specialization — substitute formals with actuals before emission.
      -- TODO: expose the FAST bit (CALL target, 1) on the Call node.
      -- TODO: subroutine scheduling — callees should be emitted after the
      --       caller's RETURN, not inline at the call site (ordering bug).
      outComment s!" call (depth {callDepth})"
      out (.call (hashLabel callee))
      if !(← wasVisited callee) then
        emitSubroutine callee

  | ProcBody.intrinsic instructions _ _ obligations _ =>
      -- Obligations emitted as comments; instructions emitted verbatim via Insn.raw.
      outComment " [intrinsic]"
      for obl in obligations do outComment s!"   obligation: {obl}"
      for insn in instructions do out (.raw insn)

  | ProcBody.critical gie body =>
      -- Typed critical section (AIL#27).
      -- Emits: BCF gie_reg, gie_bit ; body ; BSF gie_reg, gie_bit.
      -- The GIE bitField hash is carried in the node so the emitter can
      -- call resolveBitField rather than hardcoding the register address.
      let (gieReg, gieBit) ← resolveBitField gie
      out (.bcf gieReg gieBit)
      emitNode body
      out (.bsf gieReg gieBit)

-- Emit `h` as a labeled subroutine (label at top, RETURN at bottom).
-- Guards against re-emission via the visited set.
partial def emitSubroutine (h : Hash) : Emit Unit := do
  if ← wasVisited h then return
  markVisited h
  out (.lbl (hashLabel h))
  emitNamedLabels h        -- emit named aliases if any (AIL#25)
  emitNode h
  out .return_

end  -- mutual

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

/-- Symbolic PIC18 interrupt vector names (AIL#32).
    Classic PIC18: reset/hiISR/loISR map to vectors 0/1/2.
    Q71 VIC: use vic n for arbitrary vector numbers 0x00–0x58.
    Agents write .reset / .hiISR / .loISR rather than raw integers. -/
inductive PIC18Vector where
  | reset          -- vector 0: program entry point (PSECT at 0x0000)
  | hiISR          -- vector 1: high-priority ISR (0x0008 on classic PIC18)
  | loISR          -- vector 2: low-priority ISR  (0x0018 on classic PIC18)
  | vic (n : UInt8) -- Q71 VIC: arbitrary vector number 0x00–0x58
deriving Repr, BEq

/-- Hardware vector number for linker/IVT addressing. -/
def PIC18Vector.toVecNum : PIC18Vector → UInt8
  | .reset  => 0
  | .hiISR  => 1
  | .loISR  => 2
  | .vic n  => n

/-- Symbolic name for comments and diagnostics. -/
def PIC18Vector.name : PIC18Vector → String
  | .reset  => "reset"
  | .hiISR  => "hiISR"
  | .loISR  => "loISR"
  | .vic n  => s!"vic{n}"

/-- Hardware byte address for classic PIC18 interrupt vectors (AIL#23).
    reset → 0x0000, hiISR → 0x0008, loISR → 0x0018.
    vic n has no fixed classic-PIC18 address (Q71 VIC hardware only). -/
def PIC18Vector.hwAddr? : PIC18Vector → Option UInt32
  | .reset  => some 0x0000
  | .hiISR  => some 0x0008
  | .loISR  => some 0x0018
  | .vic _  => none

/-- Format a 16-bit address as 4-digit XC8 hex literal (e.g. 0x0008 → "0008h"). -/
private def fmtHex4 (n : UInt32) : String :=
  let d : Nat → String := fun k =>
    let nibble := (n.toNat >>> k) &&& 0xF
    if nibble < 10 then toString nibble else String.singleton (Char.ofNat (nibble - 10 + 'a'.toNat))
  s!"{d 12}{d 8}{d 4}{d 0}h"

/-- ISR context save/restore mode (AIL#28).
    Selects what the emitter emits around the ISR body.

    - `none`:  No save/restore emitted. Used for the reset vector (program
               entry — not an ISR) or bare ISRs where the agent manages context.
               Emits `return` for reset, `retfie 0` for interrupt vectors.
    - `full`:  Compiler emits full context save/restore:
               prologue saves WREG, STATUS, BSR, FSR0L/H, FSR1L/H, FSR2L/H
               into access-bank slots; epilogue restores in reverse order
               and emits `retfie 0`.  Valid for both hi- and low-priority ISRs.
    - `fast`:  Shadow-register save (high-priority ISR only).
               No explicit save emitted; emits `retfie FAST`.  The hardware
               saves/restores WREG, STATUS, BSR via shadow registers on
               classic PIC18 and Q71 devices. -/
inductive ISRSaveMode where
  | none   -- no compiler save/restore (reset vector, or agent-managed)
  | full   -- full software save/restore (MOVFF-based)
  | fast   -- hardware shadow-register save (RETFIE FAST; hi-priority only)
  deriving Repr, BEq

/-- Interrupt vector table entry: (symbolic vector, proc_hash).
    The proc must satisfy Ty.proc [] [] d with d ≤ cfg.maxCallDepth. -/
abbrev IVTEntry := PIC18Vector × Hash

/-- Compile a program from the store to PIC18 assembly lines.

    The program is described by an IVT — a list of (vector, proc_hash) pairs.
    Every entry must be a proc typed Ty.proc [] [] d (no params, no rets).
    The emitter emits each entry as a labeled subroutine plus an IVT section,
    then recursively emits all callees reachable from those entry procs.

    Prerequisites (caller's responsibility):
    - `checkStore targetConfig store` must succeed before calling this.
    - All hashes in ivt must exist in the store.
    - Nodes must be in dependency order in the store.

    Returns an Array of XC8 PIC Assembler-compatible assembly lines.
    Join with "\n" to produce a .s file for xc8-cc / xc8-as.

    Named roots (AIL#25): if a NameTable is supplied, each hash that appears in
    the table gets its name emitted as an alias label alongside the hash label.
    Callers (CALL/GOTO) always use the stable hash label; named labels serve
    linker scripts and debuggers.  Default: NameTable.empty (no named labels).

    TODO: emit processor directive and config words for a complete .asm file.
    TODO: emit hardware IVT section (Q71: dw entries at IVTBASE; classic PIC18:
          absolute psects at 0x0000 / 0x0008 / 0x0018). -/
def compile (store : Store) (tyEnv : TyEnv) (ivt : Array IVTEntry)
    (nameTable : NameTable := NameTable.empty)
    (saveModes : Array (PIC18Vector × ISRSaveMode) := #[])
    : Except String (Array String) := do
  let initState : EmitState := { store, tyEnv, nameTable }
  -- Resolve the ISRSaveMode for a vector (default: .none).
  let saveMode (vec : PIC18Vector) : ISRSaveMode :=
    match saveModes.findSome? (fun (v, m) => if v == vec then some m else none) with
    | some m => m
    | none   => .none
  -- ISR context save slot base address in the access bank (AIL#28).
  -- Each full-save ISR uses 9 contiguous bytes starting at:
  --   0x060 + isrIndex * 9
  -- where isrIndex counts only ISRs with saveMode = .full, in IVT order.
  -- The slot names are: _ail_save_{vecName}_{field} (e.g. _ail_save_hiISR_wreg).
  -- These are defined as EQU pseudo-ops in the data section.
  let mkSaveSlotEQUs (vec : PIC18Vector) (baseAddr : UInt32) : Array String :=
    let n := vec.name
    let fields : Array String := #["wreg", "status", "bsr", "fsr0l", "fsr0h", "fsr1l", "fsr1h", "fsr2l", "fsr2h"]
    fields.mapIdx fun i f =>
      s!"_ail_save_{n}_{f}  EQU  {baseAddr.toNat + i}"
  -- Emit ISR prologue: save WREG, STATUS, BSR, FSRs to access-bank slots.
  -- Uses MOVWF for WREG (doesn't touch STATUS), MOVFF for STATUS/BSR/FSRs.
  let emitPrologue (vec : PIC18Vector) : Emit Unit := do
    let n := vec.name
    out (.comment s!" ISR prologue: save context ({n}, full)")
    out (.movwf  s!"_ail_save_{n}_wreg")
    out (.movff  "STATUS"  s!"_ail_save_{n}_status")
    out (.movff  "BSR"     s!"_ail_save_{n}_bsr")
    out (.movff  "FSR0L"   s!"_ail_save_{n}_fsr0l")
    out (.movff  "FSR0H"   s!"_ail_save_{n}_fsr0h")
    out (.movff  "FSR1L"   s!"_ail_save_{n}_fsr1l")
    out (.movff  "FSR1H"   s!"_ail_save_{n}_fsr1h")
    out (.movff  "FSR2L"   s!"_ail_save_{n}_fsr2l")
    out (.movff  "FSR2H"   s!"_ail_save_{n}_fsr2h")
  -- Emit ISR epilogue: restore in reverse order; restore STATUS last via MOVFF
  -- so the STATUS we set with MOVFF sticks (MOVFF doesn't modify STATUS).
  let emitEpilogue (vec : PIC18Vector) : Emit Unit := do
    let n := vec.name
    out (.comment s!" ISR epilogue: restore context ({n}, full)")
    out (.movff  s!"_ail_save_{n}_fsr2h" "FSR2H")
    out (.movff  s!"_ail_save_{n}_fsr2l" "FSR2L")
    out (.movff  s!"_ail_save_{n}_fsr1h" "FSR1H")
    out (.movff  s!"_ail_save_{n}_fsr1l" "FSR1L")
    out (.movff  s!"_ail_save_{n}_fsr0h" "FSR0H")
    out (.movff  s!"_ail_save_{n}_fsr0l" "FSR0L")
    out (.movff  s!"_ail_save_{n}_bsr"   "BSR")
    out (.movf   s!"_ail_save_{n}_wreg"  .w)
    out (.movff  s!"_ail_save_{n}_status" "STATUS")
  -- Emit each IVT entry as a labeled subroutine.
  -- The vec label (_ail_vec{n}) is the stable name callers / linker scripts use.
  -- The hash label is also emitted so callees can CALL/GOTO by content address.
  let emitIVT : Emit Unit := do
    -- Count ISRs with full-save mode to assign sequential save-slot addresses.
    let mut fullSaveIdx : Nat := 0
    for (vec, h) in ivt do
      let vecNum := vec.toVecNum
      let mode   := saveMode vec
      -- Collect save-slot EQUs if this is a full-save ISR.
      if mode == .full then
        let baseAddr : UInt32 := 0x060 + (fullSaveIdx * 9).toUInt32
        let equs := mkSaveSlotEQUs vec baseAddr
        modify fun s => { s with dataDecls := s.dataDecls ++ equs }
        fullSaveIdx := fullSaveIdx + 1
      if ← wasVisited h then
        -- Proc already emitted (shared across two vectors); emit a redirect.
        out (.global s!"_ail_vec{vecNum}")
        out (.lbl s!"_ail_vec{vecNum}")
        out (.goto_ (hashLabel h))
      else
        markVisited h
        out (.global s!"_ail_vec{vecNum}")
        out (.lbl s!"_ail_vec{vecNum}")
        out (.lbl (hashLabel h))
        emitNamedLabels h  -- emit named aliases if any (AIL#25)
        if mode == .full then emitPrologue vec
        emitNode h
        -- Suppress trailing RETFIE/RETURN if the proc never returns.
        -- Two cases: explicit Ty.never return type, or a ProcBody.forever body
        -- (which loops unconditionally; its trailing return would be dead code).
        let isForever := match (← get).store.lookup h with
          | some (Node.proc _ _ (ProcBody.forever _) _) => true
          | _                                            => false
        let isNever := match (← get).tyEnv h with
          | some (Ty.proc _ [Ty.never] _) => true
          | _                              => false
        if !(isForever || isNever) then
          match mode with
          | .full => emitEpilogue vec; out (.retfie false)
          | .fast => out (.retfie true)
          | .none =>
            -- Reset vector gets RETURN; interrupt vectors (no save) get RETFIE 0.
            match vec with
            | .reset => out .return_
            | _      => out (.retfie false)
  let (_, final) ← emitIVT.run initState
  -- Data section: EQU declarations collected during the emit pass.
  -- These must precede the code section so forward references resolve.
  let dataSection : Array String :=
    if final.dataDecls.isEmpty then #[]
    else
      #["; --- Data / peripheral node declarations ---"] ++
      final.dataDecls ++
      #[""]
  -- IVT summary as comments.
  let ivtComments : Array String :=
    #["; --- IVT ---"] ++
    ivt.map (fun (vec, h) =>
      let names := nameTable.filter (·.hash == h) |>.map (·.name)
      let nameStr := if names.isEmpty then "" else " (" ++ String.intercalate ", " names.toList ++ ")"
      s!"; {vec.name} (vec {vec.toVecNum}) → {hashLabel h}{nameStr}") ++
    #[""]
  -- Code section: typed instructions rendered to assembly text.
  let codeLines := final.insns.map renderInsn
  -- Hardware IVT stubs (AIL#23): absolute PSECTs at classic PIC18 vector addresses.
  -- Each stub jumps to the actual handler in ailCode.
  -- Emitted as separate PSECTs so the linker can place them at exact addresses.
  -- The reset vector (0x0000) stub is included; real builds need it even if C wrappers
  -- call _ail_vec0 directly for test purposes.
  let ivtStubs : Array String :=
    ivt.foldl (fun acc (vec, h) =>
      match vec.hwAddr? with
      | none => acc   -- Q71 VIC: no fixed classic-PIC18 address
      | some addr =>
          let psectName := s!"ail_{vec.name}"
          acc ++ #[
            s!"    PSECT   {psectName},class=CODE,reloc=2,abs,ovrld",
            s!"    ORG     {fmtHex4 addr}",
            s!"    goto    {hashLabel h}",
            ""
          ]) #[]
  return dataSection ++ ivtComments ++ codeLines ++
    (if ivtStubs.isEmpty then #[] else #["", "; --- Hardware IVT stubs ---"] ++ ivtStubs)

end AIL.PIC18
