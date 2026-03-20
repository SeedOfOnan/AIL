# AIL TODO — Pinned items (implementation-level)

These are deferred implementation details. Do not let them block spec/design work.

## Emitter (PIC18)

- [ ] Data EQU declarations appear inside the code PSECT rather than before it — cosmetic only, assembler-correct
- [ ] `resolveAddr` returns decimal addresses; hex (0x20) would be more readable
- [ ] Banked RAM: `resolveAddr` currently truncates to UInt8 (Access Bank only); need MOVLB emission for addresses outside 0x00–0xFF
- [ ] IVT section not emitted — ISR labels exist but the interrupt vector table entries are missing
- [ ] `decfsz` loop bound not a typed instruction — only 8-bit bounds supported
- [ ] Condition protocol for `branch` not formalised — `btfsc`/`cpfseq` skip convention is implicit
- [ ] `call` FAST bit not exposed on the Call node
- [ ] NameTable not consulted — callee labels are always hash-derived
- [ ] `intrinsic` instructions emitted as comments — pending typed Insn migration

## Type system

- [ ] `inferTy_sound` and `inferTy_complete` are `sorry`'d
- [ ] `interruptHandler.vector : UInt8` is a tier violation — needs to become a hash to a target-specific interrupt descriptor

## Hash / Store

- [ ] FNV-1a hash — replace with SHA-256 before any serious content-addressing use
- [ ] `Store` is an Array (linear scan) — replace with a hash map before scale

## Pipeline / tooling

- [ ] `ailc` hardcodes a test store — needs a real input format (or content-addressed store serialisation)
- [ ] Integration test uses gpsim `pic18f4520` as a stand-in; Q71-specific peripherals require MPLAB X simulator
