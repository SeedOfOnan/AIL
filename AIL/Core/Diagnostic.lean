-- AIL.Core.Diagnostic
-- Structured diagnostic records for the AIL compiler (AIL#16).
--
-- Requirements: R5.1–R5.5 (agent-optimised diagnostics).
--
-- R5.1  Diagnostics emittable as typed records (JSON), not prose only.
-- R5.2  Errors reference nodes by content hash (no source line numbers).
-- R5.3  No cascade errors — emit root causes only (enforced by Except semantics:
--       checkStore stops at the first failing node).
-- R5.4  Closed error taxonomy — DiagnosticKind is a finite inductive, not a string.
-- R5.5  Structured fix suggestions — machine-applicable patches in FixSuggestion.
--
-- Design:
--   Each diagnostic has a kind (from the closed enum), a severity, the hash of
--   the node where the issue was detected, an advisory prose message, and an
--   optional machine-applicable fix suggestion.
--
--   JSON output is flat (no nested arrays) for easy parsing without a full JSON
--   library. The fix field is either null or a single-key object whose value is
--   a parameter object.

import AIL.Core.Hash

namespace AIL

-- ---------------------------------------------------------------------------
-- Severity
-- ---------------------------------------------------------------------------

/-- Severity level of a diagnostic. -/
inductive Severity where
  | error   -- compilation cannot proceed; store is invalid
  | warning -- potential bug; compilation may proceed with degraded guarantees
  | info    -- purely informational
deriving Repr, BEq, DecidableEq

def Severity.toJson : Severity → String
  | .error   => "\"error\""
  | .warning => "\"warning\""
  | .info    => "\"info\""

-- ---------------------------------------------------------------------------
-- DiagnosticKind  (R5.4 — closed taxonomy)
-- ---------------------------------------------------------------------------

/-- Closed taxonomy of diagnostic kinds.
    The kind is the machine-consumable classification; the message is advisory.
    Agents switch on kind, not on message strings. -/
inductive DiagnosticKind where
  /-- A hash referenced in a node's params, rets, reads, or writes is not
      present in the Store.  The referencing node is reported. -/
  | UndefinedRef
  /-- Type inference (inferTy) returned none for a node.  Root cause may be
      an undefined reference, a kind mismatch, or an unsupported body form.
      Future work: subdivide into finer kinds as inferTy gains detail. -/
  | TypeCheckFailure
  /-- A proc uses AbstractOp.load on a peripheral with sideEffectOnRead = true
      without acknowledging the discard via AbstractOp.loadDiscard.
      Fix: replace .load with .loadDiscard. -/
  | ReadClearsUnacked
  /-- An ISR-reachable intrinsic and a main-reachable intrinsic both declare
      the same FSR in their fsrUse field (AIL#13). -/
  | FSRConflict
  /-- A WREG-defining op's result is clobbered before it is consumed: a later
      op in the same seq writes WREG before the first result is read (AIL#22).
      Fix: insert an explicit store-to-temp before the clobbering op, or
      reorder the seq steps so the consumer precedes the next definer. -/
  | WREGClobber
  /-- A proc declares a FormalKind.flag ret for a flag that the enclosed op
      does not produce (AIL#31). For example, declaring a .C (Carry) ret on a
      proc whose body is xorImm — which does not set the Carry flag.
      Fix: change the flag kind to match what the op actually produces, or
      change the op. -/
  | FlagNotProduced
  /-- A ProcBody.critical body contains a setBit on the GIE bitField, which
      would re-enable interrupts inside a critical section (AIL#27).
      This is almost always a bug — the enable_ints call belongs outside the
      critical section, not inside it.
      Fix: move the setBit(GIE) outside the critical body, or remove it. -/
  | CriticalNested
  /-- The store's RAM or flash usage exceeds the target's declared limit (AIL#29).
      resource is "ram" or "flash"; used is the measured value; limit is the
      CapabilityRecord limit.
      Fix: reduce the number of data nodes, shrink static arrays, or target
      a larger device. -/
  | BudgetExceeded
deriving Repr, BEq, DecidableEq

def DiagnosticKind.toJson : DiagnosticKind → String
  | .UndefinedRef       => "\"UndefinedRef\""
  | .TypeCheckFailure   => "\"TypeCheckFailure\""
  | .ReadClearsUnacked  => "\"ReadClearsUnacked\""
  | .FSRConflict        => "\"FSRConflict\""
  | .WREGClobber        => "\"WREGClobber\""
  | .FlagNotProduced    => "\"FlagNotProduced\""
  | .CriticalNested     => "\"CriticalNested\""
  | .BudgetExceeded     => "\"BudgetExceeded\""

-- ---------------------------------------------------------------------------
-- FixSuggestion  (R5.5 — machine-applicable patches)
-- ---------------------------------------------------------------------------

/-- A machine-applicable fix suggestion.
    Agents apply these programmatically; prose message is advisory only.
    Each variant corresponds to a concrete AST edit. -/
inductive FixSuggestion where
  /-- Replace AbstractOp.load with AbstractOp.loadDiscard in the identified node.
      Applicable to ReadClearsUnacked diagnostics. -/
  | useLoadDiscard (nodeHash : Hash)
deriving Repr, BEq

def FixSuggestion.toJson : FixSuggestion → String
  | .useLoadDiscard h =>
      "{\"UseLoadDiscard\":{\"nodeHash\":\"" ++ hashLabel h ++ "\"}}"

-- ---------------------------------------------------------------------------
-- Diagnostic record
-- ---------------------------------------------------------------------------

/-- A structured diagnostic record (R5.1–R5.5).
    nodeHash identifies the node where the issue was detected (R5.2).
    message is advisory prose for human review; agents use kind. -/
structure Diagnostic where
  kind     : DiagnosticKind
  severity : Severity
  nodeHash : Hash
  message  : String
  fix      : Option FixSuggestion
deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- JSON renderer  (R5.1)
-- ---------------------------------------------------------------------------

-- Minimal JSON string escaping: handles the characters that appear in
-- node labels and obligation strings (backslash, double-quote, newline).
private def jsonEscapeStr (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

/-- Render a Diagnostic as a JSON object.
    nodeHash is rendered as a hashLabel string (\"_n<decimal>\").
    Output is a single-line JSON object suitable for streaming to stdout. -/
def Diagnostic.toJson (d : Diagnostic) : String :=
  let fixStr := match d.fix with
    | none   => "null"
    | some f => f.toJson
  let msg := jsonEscapeStr d.message
  "{\"kind\":" ++ d.kind.toJson ++ ",\"severity\":" ++ d.severity.toJson ++
  ",\"nodeHash\":\"" ++ hashLabel d.nodeHash ++ "\",\"message\":\"" ++ msg ++
  "\",\"fix\":" ++ fixStr ++ "}"

end AIL
