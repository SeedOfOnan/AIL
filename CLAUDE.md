# CLAUDE.md — Project Briefing for AI Agent Sessions

**Read this entire file before touching anything in this repository.**

---

## What this project is

This is the bootstrap repository for **AIL** (placeholder name — renaming is low priority).

AIL is a programming language being designed and built with the following unusual properties:

1. **The primary user of the language is an AI agent**, not a human developer.
   The agent's job is to author and maintain a software repository written in AIL.
   Human readability is a non-goal. Agent ergonomics are the goal.

2. **The compilation target is embedded systems**, initially PIC18 (8-bit Harvard),
   then ARM Thumb2 (Cortex-M). The *task master* running on the embedded target
   is not our concern — we are building tools for the agent that writes code for it.

3. **The project is intended to be self-hosting.** Lean 4 is a bootstrapping vehicle.
   Ultimately the compiler and toolchain should be written in AIL itself.

4. **Design is tiered.** See `docs/TIERS.md` for the strict separation between:
   - Tier 1: PIC18 (build this now)
   - Tier 2: ARM Thumb2 (design-informed, not yet implemented)
   - Tier 3: Hypothetical AI-designed CPUs (speculative, informs aspirations only)

---

## What you should and should not do

**DO:**
- Read `docs/REQUIREMENTS.md` and `docs/TIERS.md` before any design work
- Keep `AIL.Core.*` tier-neutral (no target imports)
- Mark any speculative/Tier-3 work clearly with `-- SPECULATIVE` comments
- Prefer explicit, unambiguous semantics over clever shortcuts
- Keep compilation units small and dependency graphs explicit
- Write Lean 4 proofs or `sorry`-marked proof obligations where correctness matters
- Update `docs/REQUIREMENTS.md` when new requirements are discovered
- Update `docs/TODO.md` when deferred items are resolved

**DO NOT:**
- Design for human developer ergonomics — that is explicitly not the goal
- Mix tier concerns (no Tier 1 assumptions in Core, no Tier 3 in Tier 1 emitter)
- Introduce undefined behavior
- Assume a heap allocator exists in the target environment (Tier 1)
- Treat `sorry` as a permanent solution — mark it `-- TODO: prove`

---

## Current state

Active development. The PIC18 backend is functional and growing.

### What exists and works
- **Core AST** (`AIL/Core/AST.lean`): Node, ProcBody, AbstractOp, Width, etc.
- **Type system** (`AIL/Core/Types.lean`): `inferBodyDepth`, `checkStore`, `TyEnv`
- **Content-addressed store** (`AIL/Core/Store.lean`): FNV-1a hashed, insertion-ordered
- **PIC18 emitter** (`AIL/Targets/PIC18/Emitter.lean`): full emit pass; see capabilities
- **PIC18 ISA** (`AIL/Targets/PIC18/ISA.lean`): typed instruction set + node builders
- **PIC18 capabilities** (`AIL/Targets/PIC18/Capabilities.lean`): machine-queryable
- **Structured diagnostics** (`AIL/Core/Diagnostic.lean`): typed kinds, JSON output
- **Static RAM allocator** (`AIL/Core/StaticAlloc.lean`): flat, contiguous allocation
- **Budget checker** (`AIL/Analysis/BudgetCheck.lean`): RAM + flash estimation
- **FSR liveness check** (`AIL/Analysis/FSRCheck.lean`)
- **WREG check** (`AIL/Analysis/WREGCheck.lean`)
- **Serializer** (`AIL/Core/Serialize.lean`): round-trip encode/decode
- **Git layout helper** (`AIL/Core/GitLayout.lean`)
- **PIC18 libraries**: `AIL/Lib/PIC18/RingBuf.lean`, `AIL/Lib/PIC18/INTCON.lean`
- **25 test exercises** in `TestRunner.lean` (all passing)

### Key PIC18 emitter features (implemented)
- All AbstractOps: arithmetic, bitwise, load/store, compare, indexed, immediate forms
- All ProcBody forms: atomic, seq, cond, loop, forever, whileLoop, call, intrinsic, critical
- Banked RAM: MOVLB emission with BSR tracking; addresses ≥ 0x100 emit bank-select
- IVT section: `GLOBAL` directives + hardware PSECTs at classic PIC18 vector addresses
- NameTable: named label aliases alongside hash labels (for linker scripts / debuggers)
- ISR context save/restore: `ISRSaveMode` (none/full/fast); full MOVFF-based prologue/epilogue
- Critical sections: `ProcBody.critical` emits BCF/BSF around body

### Known limitations (see Capabilities.lean for authoritative list)
- Subroutine ordering: callees emitted inline at call site, not after caller RETURN
- Loop bound decrement: 8-bit only; 16/32-bit need multi-byte sequence
- Save slots fixed at access-bank 0x060+; no FSR3/PRODH/PRODL save
- `intrinsic` nodes emit raw strings, not typed Insn (pending migration)

### Open design questions (not yet resolved)
- Does AIL have a textual surface syntax, or is AST-direct the native form?
  *(Likely both: AST-direct for agents, surface syntax for human review)*
- What is the right compilation unit granularity for an agent?
- Hash collision resistance: FNV-1a is fast but not collision-resistant (see issue)

---

## Repository layout

```
AIL/
  lakefile.lean             -- Lake build definition
  lean-toolchain            -- Pinned Lean/Lake version
  CLAUDE.md                 -- THIS FILE. Read first.
  TestRunner.lean           -- 25 test exercises (ailtest binary)
  SeedOfOnan_TODO.txt       -- Project-level TODO scratch pad
  docs/
    REQUIREMENTS.md         -- Structured requirements inventory
    TIERS.md                -- Target tier definitions and separation rules
    LANGDEF.md              -- Language definition (design decisions)
    TODO.md                 -- Deferred implementation items
  AIL/                      -- Library source
    AIL.lean                -- Root import
    Core/
      AST.lean              -- Language AST and ProcBody
      Types.lean            -- Type system (inferBodyDepth, checkStore)
      Store.lean            -- Content-addressed node store
      Hash.lean             -- FNV-1a node serialization + hashing
      Diagnostic.lean       -- Structured diagnostics (typed kinds, JSON)
      StaticAlloc.lean      -- Static RAM allocator
      Capability.lean       -- CapabilityRecord type
      Serialize.lean        -- Store round-trip serializer
      GitLayout.lean        -- Content-addressed git layout helper
    Analysis/
      FSRCheck.lean         -- FSR liveness analysis
      WREGCheck.lean        -- WREG usage check
      BudgetCheck.lean      -- RAM + flash budget estimation
    Lib/
      PIC18/
        RingBuf.lean        -- Ring buffer library (AST-direct)
        INTCON.lean         -- INTCON/GIE helpers for critical sections
    Targets/
      PIC18/
        ISA.lean            -- Typed PIC18 instruction set + node builders
        Emitter.lean        -- PIC18 code emitter
        Capabilities.lean   -- Machine-queryable capability record
      Thumb2/               -- (not yet created)
      Speculative/          -- (not yet created, Tier 3 only)
  AILApp/                   -- Example application (AST-direct AILApp)
    src/
      App.lean              -- Sample PIC18 application
  AILCompiler/
    Main.lean               -- ailc compiler executable entry point
```

---

## Build

```powershell
cd AIL
lake build          # builds all default targets
lake build ailtest  # builds the test runner
.lake/build/bin/ailtest  # run all tests (all should PASS)
```

Requires Lean 4 + Lake (elan managed). Toolchain version pinned in `lean-toolchain`.

---

## Bootstrapping lineage

This file and the initial project structure were created in a Claude claude.ai
web session. The conversation that produced this is the design record for decisions
made before this repository existed. Key decisions recorded:

- Language user: AI agent (not human developer, not embedded task master)
- Primary target: PIC18, then Thumb2, then speculative AI-native CPU
- Bootstrap tool: Lean 4 / Lake
- Self-hosting: long-term goal
- Design method: derive primitives from agent task inventory, not from AI internals
  and not from human cognitive preferences (analogous to how FORTRAN derived from
  physicist workflows, not from neuroscience)
