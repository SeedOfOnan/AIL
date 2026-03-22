# AIL TODO — Pinned items (implementation-level)

These are deferred implementation details. Do not let them block spec/design work.
Items marked ✓ are resolved; kept here for history. See GitHub issues for active tracking.

## Emitter (PIC18)

- ✓ Banked RAM: MOVLB emission for addresses outside 0x00–0xFF (AIL#24)
- ✓ IVT section: GLOBAL directives + hardware PSECTs at vector addresses (AIL#23)
- ✓ NameTable: callee labels use hash labels; named aliases emitted alongside (AIL#25)
- ✓ ISR context save/restore: prologue/epilogue for full/fast save modes (AIL#28)
- [ ] Subroutine ordering bug: callees emitted inline at call site, not scheduled after
      caller RETURN — produces correct but non-standard output (see GitHub issue)
- [ ] Data EQU declarations appear inside the code PSECT rather than before it —
      cosmetic only, assembler-correct
- [ ] `resolveAddr` returns decimal addresses; hex (0x20) would be more readable
- [ ] `decfsz` loop bound not a typed instruction — only 8-bit bounds supported;
      16/32-bit bounds need multi-byte decrement sequence (see GitHub issue)
- [ ] Condition protocol for `branch` not formalised — `btfsc`/`cpfseq` skip
      convention is implicit
- [ ] `call` FAST bit not exposed on the Call node
- [ ] `intrinsic` instructions emitted as raw strings — pending typed Insn migration
      (each intrinsic should be a typed Insn node, not a freeform string array)
- [ ] ISR save slots fixed at access-bank 0x060+; no FSR3/PRODH/PRODL save

## Type system

- [ ] `inferTy_sound` and `inferTy_complete` are `sorry`'d (see GitHub issue)
- [ ] `interruptHandler.vector : UInt8` is a tier violation — needs to become a hash
      to a target-specific interrupt descriptor

## Hash / Store

- [ ] FNV-1a hash — not collision-resistant; replace with SHA-256 or similar before
      any production content-addressing use (see GitHub issue)
- [ ] `Store` uses HashMap but insertion-ordered Array for keys — should unify

## Analysis

- [ ] `String.trimLeft` deprecated in BudgetCheck.lean — use `String.trimAsciiStart`
      (blocked on Lean 4 API: return type changed to `String.Slice`)

## Pipeline / tooling

- [ ] `ailc` hardcodes a test store — needs a real input format (or content-addressed
      store serialisation)
- [ ] Integration test uses gpsim `pic18f4520` as a stand-in; Q71-specific peripherals
      require MPLAB X simulator
