-- AIL.Analysis.BudgetCheck
-- RAM and flash resource budget checking (AIL#29, R1.5).
--
-- Provides:
--   ramUsed    : Store → Nat        — sum of byte widths for data/staticArray nodes
--   flashUsed  : Array String → Nat — estimate from compiled assembly line count
--   checkBudget : Store → CapabilityRecord → Array String → Array Diagnostic
--
-- RAM estimate: each Node.data node occupies width.toBytes bytes; each
-- Node.staticArray node occupies width.toBytes * count bytes.
-- Peripheral nodes and bitField nodes are SFRs — not in GPR RAM.
-- Formal nodes are abstract — no RAM allocation.
--
-- Flash estimate: 2 bytes per PIC18 instruction word.  Assembly lines are
-- scanned for instruction lines (non-blank, non-comment, non-label, non-directive).
-- This is a conservative lower bound; actual size depends on the linker.

import AIL.Core.AST
import AIL.Core.Store
import AIL.Core.Capability
import AIL.Core.Diagnostic

namespace AIL.BudgetCheck

-- ---------------------------------------------------------------------------
-- Width → byte count
-- ---------------------------------------------------------------------------

private def widthBytes : Width → Nat
  | .w8  => 1
  | .w16 => 2
  | .w32 => 4

-- ---------------------------------------------------------------------------
-- RAM usage
-- ---------------------------------------------------------------------------

/-- Count bytes allocated in GPR RAM by data and staticArray nodes in the store.
    Peripheral, bitField, formal, and proc nodes consume no RAM. -/
def ramUsed (s : Store) : Nat :=
  s.toArray.foldl (fun acc (_, n) =>
    match n with
    | Node.data _ w _ _            => acc + widthBytes w
    | Node.staticArray _ w _ cnt _ => acc + widthBytes w * cnt.toNat
    | _                             => acc
  ) 0

-- ---------------------------------------------------------------------------
-- Flash usage estimate
-- ---------------------------------------------------------------------------

/-- Classify an assembly line as an instruction (true) or non-instruction (false).
    Non-instructions: blank, comments (;), labels (ends with :), and
    assembler directives (starts with whitespace + uppercase keyword like PSECT/ORG/EQU/GLOBAL). -/
private def isInstructionLine (l : String) : Bool :=
  let s := l.trimLeft
  if s.isEmpty then false
  else if s.startsWith ";" then false
  else if s.endsWith ":" then false
  else
    -- Directive heuristic: starts with a known assembler directive keyword.
    let upper := s.toUpper
    let directives := ["PSECT", "ORG", "EQU", "GLOBAL", "END", "PROCESSOR",
                       "RADIX", "INCLUDE", "IFDEF", "IFNDEF", "ELSE", "ENDIF",
                       "BANKSEL"]
    !directives.any (fun d => upper.startsWith d)

/-- Estimate flash bytes from compiled assembly lines.
    Each instruction line occupies 2 bytes (one PIC18 word).
    This is a lower bound; actual binary may differ slightly after linking. -/
def flashUsed (lines : Array String) : Nat :=
  lines.foldl (fun acc l => if isInstructionLine l then acc + 2 else acc) 0

-- ---------------------------------------------------------------------------
-- Budget checker
-- ---------------------------------------------------------------------------

/-- Check whether the store's RAM and flash usage fit within the capability limits.
    `lines` is the output of `compile` (used for the flash estimate).
    Returns an empty array if both resources are within budget.
    Returns one Diagnostic per exceeded resource. -/
def checkBudget (s : Store) (cap : CapabilityRecord) (lines : Array String)
    : Array Diagnostic :=
  let diags : Array Diagnostic := #[]
  -- RAM check (limit 0 = not enforced)
  let ramU := ramUsed s
  let diags :=
    if cap.ramBytesLimit > 0 && ramU > cap.ramBytesLimit then
      diags.push {
        kind     := .BudgetExceeded,
        severity := .error,
        nodeHash := 0,   -- no single node is responsible
        message  := s!"RAM budget exceeded: {ramU} bytes used, limit {cap.ramBytesLimit}",
        fix      := none }
    else diags
  -- Flash check (limit 0 = not enforced)
  let flashU := flashUsed lines
  let diags :=
    if cap.flashBytesLimit > 0 && flashU > cap.flashBytesLimit then
      diags.push {
        kind     := .BudgetExceeded,
        severity := .error,
        nodeHash := 0,
        message  := s!"Flash budget exceeded: ~{flashU} bytes used (estimate), limit {cap.flashBytesLimit}",
        fix      := none }
    else diags
  diags

end AIL.BudgetCheck
