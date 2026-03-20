# AIL Requirements

## What AIL Is

AIL (placeholder name) is a programming language whose **primary user is an AI agent**
acting as author and maintainer of a software repository targeting embedded systems.

It is NOT designed to ease the work of:
- Human software developers (ergonomics for human cognition are a non-goal)
- The task master running on the embedded target (that is the *output*, not the user)

It IS designed to ease the work of:
- An AI agent reading, writing, refactoring, and reasoning about a codebase
- An AI agent managing correctness, versioning, and change impact across a repository

The language is intended to be **self-hosting**: ultimately the compiler and toolchain
will themselves be written in AIL. Lean 4 is a bootstrapping vehicle only.

---

## Derivation method

Requirements are derived by asking:
  *What does an AI agent actually do, repeatedly, when authoring and maintaining
   embedded software — and what do current languages express awkwardly or not at all?*

This parallels how FORTRAN was derived: not from neuroscience, but from observing
what physicists needed to do repeatedly and finding what made that natural.

Human cognitive preferences are explicitly excluded as a design input.

---

## Inventory (work in progress)

The following is a structured inventory of agent tasks, to be elaborated:

### R1 — Expressing embedded computation

- R1.1 Memory-mapped I/O access with precise address and width
- R1.2 Interrupt handlers with bounded stack and latency guarantees
- R1.3 Fixed-point and integer arithmetic (Tier 1: no FPU)
- R1.4 Peripheral configuration sequences (UART, SPI, I2C, ADC, timers)
- R1.5 Resource budgets: RAM, flash, cycle counts — expressible and checkable

### R2 — Agent read/write/refactor tasks

- R2.1 Structure that makes dependency and change-impact analysis tractable
- R2.2 Representations that compress well for agent context windows
- R2.3 Unambiguous semantics — no undefined behavior the agent must reason around
- R2.4 Explicit, machine-checkable invariants (leverage Lean 4 / dependent types)
- R2.5 Diff-friendly representation (small, local changes produce small, local diffs)

### R3 — Repository-level concerns

- R3.1 Versioning and compatibility expressible in the language/type system
- R3.2 Target parameterization: same source, multiple targets where possible
- R3.3 Test/verification artifacts as first-class repository citizens

### R4 — Speculative (Tier 3 aspirations, flagged)

- R4.1 Non-deterministic / approximate computation representable in AST
- R4.2 Type system capable of encoding probability distributions
- R4.3 Batch/parallel operations as language primitives, serialized by Tier 1/2 emitters

---

## Open questions (to be resolved before design freeze)

- What is the minimal set of language primitives that satisfies R1 + R2?
- How much of R2 can be handled by the type system vs. by tooling?
- What is the right granularity of a "compilation unit" for an agent?
- Should the language have a textual surface syntax at all, or is a structured
  (AST-direct) representation more natural for an agent author?
