# LANGDEF — AIL Language Definition

Accumulated during design-by-doing session. Each entry records the minimal
decision made at the point it was needed, and why.

Design principle: **the language primitive set is exactly what requires
compiler/linker knowledge of the hardware. Everything expressible in terms
of other AIL constructs is user-definable — including by the AI agent.**

---

## Instruction intrinsics

AIL has an intrinsic for each target machine instruction. These are the
lowest-level AIL constructs — typed function-like calls that emit a single
instruction. They replace the need for inline assembly.

**Why:** The agent writes everything in AIL. Intrinsics are typed (unlike raw
assembly text), composable, and analyzable by the compiler. No mode-switch
to an assembly sublanguage.

**Example (PIC18):** `bra(label)`, `bcf(reg, bit)`, `bsf(reg, bit)`, `retfie()`

---

## Hardware entry points

All functions the hardware calls — not functions your code calls — are declared
with `entry`. This unifies reset and interrupt handlers under one concept.
The complete set of `entry` declarations in a program is the vector table.

**Syntax:**
```
entry(reset)                       fn name { body }
entry(interrupt, priority, save: mode) fn name { body }
```

**Forms:**

`entry(reset)`:
- Placed at reset vector (`0x0000` on PIC18, via a compiler-emitted `goto`)
- Implicitly returns `Never` — it never returns to a caller
- No context save (nothing to save from)
- At most one per program

`entry(interrupt, priority, save: mode)`:
- `priority`: `high` | `low`
  - `high` → vector at `0x0008` (PIC18)
  - `low`  → vector at `0x0018` (PIC18)
- `save: mode`: `full` | `fast`
  - `full` → compiler saves/restores WREG, STATUS, BSR, FSRs
  - `fast` → uses PIC18 shadow registers (only valid for `high`)
- At most one `high` and one `low` per program

**Constraints (all forms):**
- No parameters, no return value (other than `Never` for reset)
- Not callable from user code — hardware-invoked only

**Example:**
```
entry(reset) fn startup {
  ...
}

entry(interrupt, high, save: full) fn uart_rx_isr {
  ...
}

entry(interrupt, low, save: full) fn timer_isr {
  ...
}
```

**Why `entry` as the unifying keyword:**
- All these functions share the same nature: hardware-dispatched, not user-called
- A single keyword makes the vector table visible as a concept — it is exactly
  the set of `entry` declarations in the program
- Avoids `main` (implies a calling convention that doesn't exist here) and
  avoids `interrupt` alone (which doesn't cover reset)

---

## Hardware register (SFR) declarations

**Syntax:**
```
reg NAME : TYPE at ADDRESS [, qualifier]*
```

**Qualifiers:**
- `volatile` — read/write must not be reordered or elided by the compiler
- `read_clears` — reading has a hardware side effect (e.g. clears FIFO slot)
- `write_clears` — writing clears a flag rather than setting a value
- (others added as needed)

**Type:** `u8` for PIC18 (all SFRs are 8-bit)

**Example:**
```
reg RCREG   : u8 at 0xFAE, volatile, read_clears
reg RCSTA   : u8 at 0xFAB, volatile
reg TXREG   : u8 at 0xFAD, volatile
```

**Placement:** SFR declarations belong in a peripheral definition file
(e.g. `AIL/Targets/PIC18/Peripherals/UART.ail`), not in handler code.
Handler code references them by name. The AI agent writes these declarations
— they are not built into the language.

**Why explicit qualifiers:**
- `volatile` prevents the optimizer from treating two reads as one
- `read_clears` lets the type system warn if a read result is discarded
  (discarding it would silently drop received data)

---

## Register bit field declarations

**Syntax:** bit fields declared inside a `reg` body:
```
reg NAME : u8 at ADDRESS [, qualifier]* {
    bit FIELDNAME = BIT_POSITION
    ...
}
```

**Access:**
- `REG.FIELD` reads as `bool`
- `REG.FIELD = true/false` sets/clears the bit (generates BSF/BCF on PIC18)

**Example:**
```
reg RCSTA : u8 at 0xFAB, volatile {
    bit SPEN  = 7
    bit RX9   = 6
    bit SREN  = 5
    bit CREN  = 4
    bit ADDEN = 3
    bit FERR  = 2
    bit OERR  = 1
    bit RX9D  = 0
}
```

Usage: `RCSTA.OERR` → `bool`, `RCSTA.CREN = false` clears overrun.

**Why:**
- Bit manipulation via named fields eliminates mask/shift errors
- Bool type for single bits is unambiguous — no "is this 0 or 1 or nonzero?" question
- Clearing overrun by writing a field is the PIC18 hardware mechanism; making it
  a simple assignment makes the intent obvious to the agent writing the code

---

## Never — the bottom type

**Syntax:** `Never` (as a return type)

**Semantics:** A function returning `Never` does not return. The compiler
does not emit code after a call to such a function and accepts it in any
type position (since it never produces a value of the wrong type).

**Why a primitive:** The compiler must know about `Never` to perform
control-flow analysis. It cannot be defined by the user.

---

## Explicit discard

**Syntax:** `_ = EXPR`

**Semantics:** Evaluates EXPR for its side effects; result is intentionally discarded.

**Why:** Registers declared `read_clears` emit a warning if their read result is unused
(dropping it silently would lose data). `_ =` is the explicit acknowledgement that
the discard is intentional — suppresses the warning.

**Example:**
```
_ = RCREG   -- advance FIFO, discard framing-errored byte
```

---

## Static variable declarations

**Syntax:**
```
static NAME : TYPE [= INITIAL_VALUE]
```

**Semantics:**
- Allocated in fixed RAM at link time (no heap)
- Initialized once at startup (before `main` / before interrupts enabled)
- Mutable
- Module-scoped (not inside a function)

**Example:**
```
static rx_buffer         : RingBuf[u8, 32]
static rx_buffer_overrun : bool = false
```

**Why:** PIC18 has no heap. All buffers and flags must be statically allocated.
Explicit `static` makes the RAM budget visible and auditable.

---

## User-definable: panic

`panic` is not a language primitive. It is definable by the agent using
instruction intrinsics and the `Never` return type:

```
fn panic() -> Never {
    label L
    bra(L)
}
```

The agent writes this (or imports it from a platform library) and uses it
like any other function. The compiler understands it never returns because
of the `Never` return type.

---

## User-definable: RingBuf

`RingBuf` is not a language built-in. It is a data structure definable
by the agent from primitives: fixed-size arrays, integer arithmetic (or
bitwise AND for power-of-2 wrap), user-defined types with methods, and
`static` allocation.

**Interface the agent would define:**
```
type RingBuf[T, N] { ... }   -- N must be power of 2

impl RingBuf[T, N] {
    fn is_full()  -> bool  { ... }
    fn is_empty() -> bool  { ... }
    fn push(val: T)        { ... }   -- unchecked; caller ensures not full
    fn pop()      -> Option[T] { ... }
}
```

**What primitives are needed to define it:**
- User-defined parameterized types (generics with const parameters)
- Fixed-size arrays: `[T; N]`
- Bitwise AND: for index wrap without division
- `Option[T]`: either a language primitive or also user-definable

**Power-of-2 constraint:** enforced by a compile-time assertion in the
type definition, not by the language.

---
