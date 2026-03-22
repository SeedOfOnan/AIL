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

### R5 — Agent-compiler interface

The compiler's output is consumed by an AI agent, not read by a human.
Error messages and diagnostic output must be designed accordingly.

- R5.1 **Structured diagnostics.** Errors are emittable as typed records (JSON or
  S-expression), not only as human prose. The agent receives a machine-readable
  object it can pattern-match, not a string to parse.

- R5.2 **Hash-addressed errors.** Since AIL has no text source, errors reference
  nodes by their content hash. The hash uniquely identifies the problematic node
  in the Store; no source line numbers.

- R5.3 **No cascade errors.** Emit only root causes, or clearly mark which
  diagnostics are consequences of a root. An agent acting on 40 cascade errors
  wastes context; it needs one actionable fact.

- R5.4 **Closed error taxonomy.** Error *kinds* are a finite enum, not free-form
  English text. Prose descriptions are advisory comments on the record, not the
  data the agent acts on. This makes agent error-handling code straightforward.

- R5.5 **Structured fix suggestions.** Where the compiler can determine the
  correction, it emits a structured patch (e.g. `{ insert_formal: { node: ...,
  position: 0 } }`), not a human-readable hint. The agent applies it; it does
  not interpret advice.

- R5.6 **Machine-queryable capability boundary.** The set of constructs the
  compiler can currently emit for a given target must be queryable (e.g.
  `ailc capabilities --target pic18`). An agent must never have to remember
  cross-session which language constructs are implemented. The compiler is the
  authority; manual `-- TODO: unimplemented` annotations in source are a
  stop-gap only.

### R6 — Compiler-managed bookkeeping (derived from AILApp experience)

The following concerns arose during AST-direct AILApp development where the
agent was forced to manage them manually. Each is properly a compiler
responsibility:

- R6.1 **Implicit content-addressed identity.** The agent names things; the
  compiler computes hashes. Manual `hashNode` threading is boilerplate that
  obscures program structure and is error-prone.

- R6.2 **Formal uniqueness enforcement.** UIDs for formals (e.g. `boolUid`)
  must be unique across a Store. The compiler enforces this; the agent does not.

- R6.3 **Static RAM allocation.** `static` declarations are assigned addresses
  by the linker, not by the agent. The agent states the name and type; the
  compiler satisfies R1.5 (RAM budget checking).

- R6.4 **Implicit library node integration.** When an agent uses a library proc,
  its backing nodes are automatically in scope. Manual `Store.foldl insert`
  merging is plumbing that should be invisible.

- R6.5 **Register allocation.** Even a minimal register allocator eliminates
  the need for hand-introduced spill variables (e.g. the `temp` scratch byte
  in the ring buffer push). Related to FSR tracking (see issue #13).

- R6.6 **Typed calling convention.** WREG as an implicit side-channel between
  nodes is untracked and uncheckable. A typed register model (explicit WREG
  in/out in proc signatures) makes this a compiler-checked fact. Related to
  typed ISA nodes (see issue #9).

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
