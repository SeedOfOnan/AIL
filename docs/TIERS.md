# AIL Target Tiers

This document defines the tiered target architecture for AIL.
Tiers are strictly separated. Tier 3 informs language design aspirations.
Tier 1 grounds them in present hardware reality.

---

## Tier 1 — PIC18 (Concrete, buildable now)

**Architecture:** 8-bit Harvard, Microchip PIC18 family  
**Status:** Primary initial target  
**Constraints:**
- ~4KB RAM typical
- Program memory separate from data memory (Harvard)
- No hardware FPU
- Limited register file
- Specific peripheral models (UART, SPI, I2C, ADC, timers)
- Interrupts with strict latency requirements
- No OS, no heap allocator by default

**Compiler output:** PIC18 assembly or relocatable object (COFF)

**Design obligations this places on AIL:**
- Must be able to express memory-mapped I/O access precisely
- Must be able to express interrupt handlers with known stack bounds
- Must be able to express fixed-point arithmetic (no floats on base hardware)
- Must allow agent to reason about and bound resource consumption (RAM, flash)

---

## Tier 2 — ARM Thumb2 (Near-term, realistic)

**Architecture:** ARM Cortex-M family (M0+, M3, M4, M7)  
**Status:** Secondary target, design informed but not yet implemented  
**Constraints:**
- 16/32-bit mixed instruction encoding
- Some devices have FPU (Cortex-M4F, M7)
- CMSIS peripheral access patterns
- RTOS possible (FreeRTOS, Zephyr)
- Much richer register file than PIC18

**Compiler output:** ARM Thumb2 assembly or ELF object

**Design obligations this places on AIL:**
- Must parameterize over presence/absence of FPU
- Should express RTOS primitives (tasks, mutexes, queues) if present
- Should allow vectorized DSP operations where available (M4/M7 DSP extensions)

---

## Tier 3 — Hypothetical AI-designed CPU (Speculative, unconstrained)

**Architecture:** Not yet defined. No assumptions borrowed from human engineering history.  
**Status:** Informs language design aspirations only. Not a build target.  
**Purpose:** Ensures language primitives are not unnecessarily anthropocentric.

**Speculative native operations that might exist:**
- Stochastic execution units (non-deterministic by design)
- Graph traversal as a native instruction class
- Approximate arithmetic with explicit error bounds
- Associative memory lookup as a primitive
- Batch/parallel operation as default, not exception

**Design obligation this places on AIL:**
- Language primitives must not be *inherently* tied to deterministic, sequential,
  von Neumann assumptions
- Where Tier 1/2 force determinism, this should be an explicit lowering/approximation
  step, not a fundamental language assumption
- The AST and type system should be able to *represent* non-deterministic or
  approximate computations even if Tier 1/2 emitters must serialize/approximate them

---

## Separation discipline

- `AIL.Targets.PIC18.*` — Tier 1 only
- `AIL.Targets.Thumb2.*` — Tier 2 only  
- `AIL.Targets.Speculative.*` — Tier 3, clearly marked, never depended on by Tier 1/2
- `AIL.Core.*` — tier-neutral; must not import any target module
