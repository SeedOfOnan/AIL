-- AIL.Targets.PIC18.ISA
-- PIC18 typed instruction set, renderers, and single-instruction node builders.
--
-- TIER: Tier 1 only. No Core module may import this file.
-- See docs/TIERS.md for the separation discipline.
--
-- This module was extracted from Emitter.lean to separate ISA knowledge from
-- the walk/emit algorithm, and extended with single-instruction Node builders
-- that replace raw Array String intrinsics (AIL issue #9).
--
-- Node builders
-- -------------
-- Each builder produces a Node.proc #[] #[] (ProcBody.intrinsic ...) with:
--   - A single rendered instruction as the instruction string
--   - Semantically correct reads/writes arrays (for type-environment resolution)
--   - An obligation string documenting the instruction's effect
--
-- params and rets are always #[] for step nodes: the proc type is Ty.proc [] [] 0.
-- Semantic data dependencies are captured in the intrinsic's reads/writes arrays.
-- The enclosing proc's params/rets determine its overall type; step types need
-- only be Ty.proc _ _ d for the seq_ok rule to accept them.
--
-- Callers compose builder nodes in ProcBody.seq to replace multi-instruction
-- ProcBody.intrinsic nodes, gaining typed, composable, hash-deduplicable
-- single-instruction granularity.

import AIL.Core.Hash
import AIL.Core.AST

namespace AIL.PIC18

-- ---------------------------------------------------------------------------
-- Dest: result destination for byte-oriented file register operations
-- ---------------------------------------------------------------------------

/-- Result destination for byte-oriented file register operations. -/
inductive Dest where
  | w  -- result written to WREG
  | f  -- result written back to file register f
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Insn: typed PIC18 instruction representation
-- ---------------------------------------------------------------------------

/-- A PIC18 instruction or assembler pseudo-op.
    File register addresses (f) are Strings: either a hash-derived symbol name
    (e.g. "_n12345") defined by an EQU in the data section, or a numeric literal.
    Using String allows the assembler to resolve symbols, improving readability
    and enabling cross-file linking when compilation is split.
    TODO: extend to banked addresses (BANKMASK + BSR management). -/
inductive Insn where
  -- Byte-oriented file register operations
  | movwf  (f : String)              -- MOVWF f, c   ; WREG → f
  | movf   (f : String) (d : Dest)   -- MOVF  f, d   ; f → d
  | movlw  (k : UInt8)               -- MOVLW k      ; k → WREG
  | addlw  (k : UInt8)               -- ADDLW k      ; WREG += k
  | andlw  (k : UInt8)               -- ANDLW k      ; WREG &= k
  | xorlw  (k : UInt8)               -- XORLW k      ; WREG ^= k
  | sublw  (k : UInt8)               -- SUBLW k      ; WREG = k - WREG
  | addwf  (f : String) (d : Dest)   -- ADDWF f, d   ; f + WREG → d
  | subwf  (f : String) (d : Dest)   -- SUBWF f, d   ; f - WREG → d
  | andwf  (f : String) (d : Dest)   -- ANDWF f, d
  | iorwf  (f : String) (d : Dest)   -- IORWF f, d
  | xorwf  (f : String) (d : Dest)   -- XORWF f, d
  | comf   (f : String) (d : Dest)   -- COMF  f, d   ; ~f → d
  | rlncf  (f : String) (d : Dest)   -- RLNCF f, d   ; rotate left, no carry
  | rrncf  (f : String) (d : Dest)   -- RRNCF f, d   ; rotate right, no carry
  | mulwf  (f : String)              -- MULWF f      ; WREG × f → PRODH:PRODL
  | mullw  (k : UInt8)               -- MULLW k      ; WREG × k → PRODH:PRODL
  | decfsz (f : String) (d : Dest)   -- DECFSZ f, d  ; decrement, skip if zero
  | incf   (f : String) (d : Dest)   -- INCF  f, d   ; increment f → d
  | setf   (f : String)              -- SETF  f, c   ; f = 0xFF
  | clrf   (f : String)              -- CLRF  f, c   ; f = 0x00
  -- Bit-oriented operations
  | bcf    (f : String) (b : UInt8)  -- BCF f, b
  | bsf    (f : String) (b : UInt8)  -- BSF f, b
  | btfsc  (f : String) (b : UInt8)  -- BTFSC f, b   ; skip if bit clear
  | btfss  (f : String) (b : UInt8)  -- BTFSS f, b   ; skip if bit set
  -- Comparison
  | cpfseq (f : String)              -- CPFSEQ f     ; skip if f == WREG
  | cpfsgt (f : String)              -- CPFSGT f     ; skip if f > WREG
  | cpfslt (f : String)              -- CPFSLT f     ; skip if f < WREG
  | tstfsz (f : String)              -- TSTFSZ f     ; skip if f == 0
  -- Control flow
  | call   (lbl : String)           -- CALL  label, 0
  | goto_  (lbl : String)           -- GOTO  label
  | bra    (lbl : String)           -- BRA   label       ; short relative branch
  | return_                         -- RETURN
  | retfie (fast : Bool)            -- RETFIE [FAST]     ; return from interrupt
  -- FSR indirect
  | lfsr   (f : UInt8) (sym : String) -- LFSR FSRf, sym ; load FSR with 12-bit address literal
  -- Assembler pseudo-ops
  | lbl    (name : String)          -- name:             ; label definition
  | global (name : String)          --     GLOBAL name
  | nop                             --     NOP
  | comment (text : String)         -- ; text
  /-- Raw assembly line emitted verbatim. Used for constructs without a typed Insn.
      The agent is responsible for correctness of the text.
      Symbols must use the hashLabel format (_n<hash>) to match emitter EQUs. -/
  | raw     (text : String)
  deriving Repr

-- ---------------------------------------------------------------------------
-- Instruction text rendering  (XC8 PIC Assembler syntax)
-- ---------------------------------------------------------------------------

-- XC8 PIC Assembler operand tokens (source: MPLAB XC8 PIC Assembler User Guide).
-- XC8 uses letter tokens, NOT the numeric 0/1 style or MPASM symbolic names.
-- Destination: ,w (WREG) or ,f (file register).
-- Access bank qualifier: ,c (or ,a) for Access Bank, ,b for banked.
-- Do NOT mix letter and numeric forms in the same instruction.

def renderDest : Dest → String
  | .w => "w"   -- XC8: lowercase 'w' (not W, not 0)
  | .f => "f"   -- XC8: lowercase 'f' (not F, not 1)

-- Access bank qualifier in XC8 style.
def renderAccess : String := "c"  -- 'c' = Access Bank (unbanked); 'b' = banked

/-- Render a single instruction to XC8 PIC Assembler assembly text.
    Syntax follows MPLAB XC8 PIC Assembler User Guide (XC8 v3.x, LLVM backend).
    Operand style: ,w / ,f for destination; ,c for access bank (not ,0 / ,1 / ACCESS). -/
def renderInsn : Insn → String
  | .movwf  f     => s!"    movwf   {f}, {renderAccess}"
  | .movf   f d   => s!"    movf    {f}, {renderDest d}, {renderAccess}"
  | .movlw  k     => s!"    movlw   {k}"
  | .addlw  k     => s!"    addlw   {k}"
  | .andlw  k     => s!"    andlw   {k}"
  | .xorlw  k     => s!"    xorlw   {k}"
  | .sublw  k     => s!"    sublw   {k}"
  | .addwf  f d   => s!"    addwf   {f}, {renderDest d}, {renderAccess}"
  | .subwf  f d   => s!"    subwf   {f}, {renderDest d}, {renderAccess}"
  | .andwf  f d   => s!"    andwf   {f}, {renderDest d}, {renderAccess}"
  | .iorwf  f d   => s!"    iorwf   {f}, {renderDest d}, {renderAccess}"
  | .xorwf  f d   => s!"    xorwf   {f}, {renderDest d}, {renderAccess}"
  | .comf   f d   => s!"    comf    {f}, {renderDest d}, {renderAccess}"
  | .rlncf  f d   => s!"    rlncf   {f}, {renderDest d}, {renderAccess}"
  | .rrncf  f d   => s!"    rrncf   {f}, {renderDest d}, {renderAccess}"
  | .mulwf  f     => s!"    mulwf   {f}, {renderAccess}"
  | .mullw  k     => s!"    mullw   {k}"
  | .decfsz f d   => s!"    decfsz  {f}, {renderDest d}, {renderAccess}"
  | .incf   f d   => s!"    incf    {f}, {renderDest d}, {renderAccess}"
  | .setf   f     => s!"    setf    {f}, {renderAccess}"
  | .clrf   f     => s!"    clrf    {f}, {renderAccess}"
  | .bcf    f b   => s!"    bcf     {f}, {b}, {renderAccess}"
  | .bsf    f b   => s!"    bsf     {f}, {b}, {renderAccess}"
  | .btfsc  f b   => s!"    btfsc   {f}, {b}, {renderAccess}"
  | .btfss  f b   => s!"    btfss   {f}, {b}, {renderAccess}"
  | .cpfseq f     => s!"    cpfseq  {f}, {renderAccess}"
  | .cpfsgt f     => s!"    cpfsgt  {f}, {renderAccess}"
  | .cpfslt f     => s!"    cpfslt  {f}, {renderAccess}"
  | .tstfsz f     => s!"    tstfsz  {f}, {renderAccess}"
  | .call   lbl   => s!"    call    {lbl}, 0"
  | .goto_  lbl   => s!"    goto    {lbl}"
  | .bra    lbl   => s!"    bra     {lbl}"
  | .lfsr   f sym => s!"    lfsr    {f}, {sym}"
  | .return_      => s!"    return"
  | .retfie true  => s!"    retfie  1"       -- FAST bit
  | .retfie false => s!"    retfie  0"
  | .lbl    name  => s!"{name}:"
  | .global name  => s!"    global  {name}"
  | .nop          => s!"    nop"
  | .comment t    => s!";{t}"
  | .raw     t    => t

-- ---------------------------------------------------------------------------
-- Single-instruction node builders
-- ---------------------------------------------------------------------------
-- Each builder creates a Node.proc #[] #[] with a single rendered instruction.
-- params and rets are always #[] (type = Ty.proc [] [] 0). Semantic data
-- dependencies are captured in the intrinsic's reads/writes arrays.
-- Callers compose these in ProcBody.seq to build multi-step operations.
-- ---------------------------------------------------------------------------

/-- MOVWF sym, c  —  WREG → f  (store WREG into file register).
    writes = [hDst]: the file register is modified. -/
def nodeMovwf (hDst : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movwf (hashLabel hDst))] #[] #[hDst]
                #[s!"WREG → {hashLabel hDst}"] #[])
    label

/-- MOVF sym, W, c  —  f → WREG  (load file register into WREG).
    reads = [hSrc]: the file register is consumed. -/
def nodeMovf_w (hSrc : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movf (hashLabel hSrc) .w)] #[hSrc] #[]
                #[s!"{hashLabel hSrc} → WREG"] #[])
    label

/-- MOVF INDF0, W, c  —  *(FSR0) → WREG  (FSR0-indirect read).
    No typed reads/writes: FSR0 is a hardware register, not a Store node. -/
def nodeMovf_INDF0_w (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movf "INDF0" .w)] #[] #[]
                #["*(FSR0) → WREG"] #[0])
    label

/-- MOVWF INDF0, c  —  WREG → *(FSR0)  (FSR0-indirect write).
    No typed reads/writes: FSR0/INDF0 are hardware registers. -/
def nodeMovwf_INDF0 (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movwf "INDF0")] #[] #[]
                #["WREG → *(FSR0)"] #[0])
    label

/-- MOVWF INDF1, c  —  WREG → *(FSR1)  (FSR1-indirect write).
    No typed reads/writes: FSR1/INDF1 are hardware registers. -/
def nodeMovwf_INDF1 (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movwf "INDF1")] #[] #[]
                #["WREG → *(FSR1)"] #[1])
    label

/-- ADDWF FSR0L, F, c  —  FSR0L += WREG  (advance FSR0 by index in WREG).
    No typed reads/writes: FSR0L is a hardware register. -/
def nodeAddwf_FSR0L (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.addwf "FSR0L" .f)] #[] #[]
                #["FSR0L += WREG"] #[0])
    label

/-- ADDWF FSR1L, F, c  —  FSR1L += WREG  (advance FSR1 by index in WREG).
    No typed reads/writes: FSR1L is a hardware register. -/
def nodeAddwf_FSR1L (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.addwf "FSR1L" .f)] #[] #[]
                #["FSR1L += WREG"] #[1])
    label

/-- LFSR 0, sym  —  FSR0 = address of hArr  (load FSR0 with array base address).
    reads = [hArr]: the array base address is consumed (to form the address literal). -/
def nodeLfsr0 (hArr : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.lfsr 0 (hashLabel hArr))] #[hArr] #[]
                #[s!"FSR0 ← &{hashLabel hArr}"] #[0])
    label

/-- LFSR 1, sym  —  FSR1 = address of hArr  (load FSR1 with array base address).
    reads = [hArr]: the array base address is consumed. -/
def nodeLfsr1 (hArr : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.lfsr 1 (hashLabel hArr))] #[hArr] #[]
                #[s!"FSR1 ← &{hashLabel hArr}"] #[1])
    label

/-- INCF sym, F, c  —  f += 1  (increment file register in place).
    writes = [hDst]: the file register is modified. -/
def nodeIncf_f (hDst : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.incf (hashLabel hDst) .f)] #[] #[hDst]
                #[s!"{hashLabel hDst} += 1"] #[])
    label

/-- MOVLW k  —  k → WREG  (load literal into WREG).
    No typed reads/writes: k is an immediate constant. -/
def nodeMovlw (k : UInt8) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.movlw k)] #[] #[]
                #[s!"WREG ← {k}"] #[])
    label

/-- ANDWF sym, F, c  —  f &= WREG  (mask file register in place).
    writes = [hDst]: the file register is modified. -/
def nodeAndwf_f (hDst : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.andwf (hashLabel hDst) .f)] #[] #[hDst]
                #[s!"{hashLabel hDst} &= WREG"] #[])
    label

/-- SETF sym, c  —  f = 0xFF  (set all bits of file register).
    writes = [hDst]: the file register is modified. -/
def nodeSetf (hDst : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.setf (hashLabel hDst))] #[] #[hDst]
                #[s!"{hashLabel hDst} ← 0xFF"] #[])
    label

/-- CLRF sym, c  —  f = 0x00  (clear file register).
    writes = [hDst]: the file register is modified. -/
def nodeClrf (hDst : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.clrf (hashLabel hDst))] #[] #[hDst]
                #[s!"{hashLabel hDst} ← 0x00"] #[])
    label

/-- RETFIE [fast]  —  return from interrupt handler.
    fast = true: use shadow registers (FAST bit); valid for high-priority ISR only.
    No typed reads/writes: context save/restore is implicit in hardware. -/
def nodeRetfie (fast : Bool) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.retfie fast)] #[] #[]
                #[if fast then "retfie FAST (shadow registers)" else "retfie 0"] #[])
    label

/-- CPFSEQ sym, c  —  skip next instruction if f == WREG.
    Skip-when-TRUE condition protocol: this instruction is the last step of a
    condition proc (type proc [] [Bool] 0). The PIC18 skip-when-equal behavior
    satisfies the AIL cond/whileLoop convention that the skip occurs when TRUE.
    reads = [hSrc]: the file register is compared. -/
def nodeCpfseq (hSrc : Hash) (label : String) : Node :=
  .proc #[] #[]
    (.intrinsic #[renderInsn (.cpfseq (hashLabel hSrc))] #[hSrc] #[]
                #[s!"skip if {hashLabel hSrc} == WREG (condition: equal = TRUE)"] #[])
    label

end AIL.PIC18
