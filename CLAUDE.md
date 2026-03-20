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

**DO NOT:**
- Design for human developer ergonomics — that is explicitly not the goal
- Mix tier concerns (no Tier 1 assumptions in Core, no Tier 3 in Tier 1 emitter)
- Introduce undefined behavior
- Assume a heap allocator exists in the target environment (Tier 1)
- Treat `sorry` as a permanent solution — mark it `-- TODO: prove`

---

## Current state

Bootstrap stage. Stubs only. No real compiler exists yet.

### Immediate next tasks
1. Derive the minimal AIL primitive set from `docs/REQUIREMENTS.md` R1 + R2
2. Design the Core AST in `AIL/Core/AST.lean` — replace the stub
3. Design the type system in `AIL/Core/Types.lean` — replace the stub
4. Implement a PIC18 emitter skeleton in `AIL/Targets/PIC18/Emitter.lean`

### Open design questions (resolve before AST design)
- Does AIL have a textual surface syntax, or is AST-direct the native form?
- What is the right compilation unit granularity for an agent?
- How much of R2 (agent ergonomics) lives in the type system vs. tooling?

---

## Repository layout

```
AIL/
  lakefile.lean          -- Lake build definition
  CLAUDE.md              -- THIS FILE. Read first.
  docs/
    REQUIREMENTS.md      -- Structured requirements inventory
    TIERS.md             -- Target tier definitions and separation rules
  AIL/                   -- Library source
    AIL.lean             -- Root import
    Core/
      AST.lean           -- Language AST (stub)
      Types.lean         -- Type system (stub)
    Targets/
      PIC18/
        Emitter.lean     -- PIC18 code emitter (stub)
      Thumb2/            -- (not yet created)
      Speculative/       -- (not yet created, Tier 3 only)
  AILCompiler/
    Main.lean            -- ailc compiler executable entry point
```

---

## Build

```powershell
cd AIL
lake build
```

Note: `lean_lib` targets are not built by `lake build` without `@[default_target]`.
That annotation is present in `lakefile.lean`; plain `lake build` works.

Requires Lean 4 + Lake (elan managed).

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
