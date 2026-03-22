-- AIL.Core.Capability
-- Machine-queryable compiler capability boundary (AIL#17).
--
-- Requirements: R5.6 (agent-optimised capability declaration).
--
-- R5.6  The compiler must declare what it can emit, machine-queryably.
--       `ailc capabilities --target <t> --format json` exits 0 and prints a
--       JSON record describing the implemented subset of the AIL spec.
--       The record is generated from the actual emitter, not maintained by hand.
--
-- Design:
--   CapabilityRecord is a tier-neutral Core structure.  Each backend fills one
--   in (co-located with its Emitter.lean) and registers it with the CLI.
--   An agent reads this record before authoring a Store; it will not produce
--   nodes or ops the emitter cannot handle.
--
--   JSON output is a single-line object for easy machine parsing.
--   schemaVersion is bumped when field semantics change.

namespace AIL

-- ---------------------------------------------------------------------------
-- CapabilityRecord
-- ---------------------------------------------------------------------------

/-- A machine-queryable description of what a backend can compile.
    Fields correspond to the match arms present in the target's Emitter.
    An agent that reads this record before authoring a Store will not produce
    nodes or ops that the emitter cannot handle. -/
structure CapabilityRecord where
  /-- Schema version.  Increment when field semantics change. -/
  schemaVersion : Nat           := 1
  /-- Backend target identifier (e.g. "pic18"). -/
  target        : String
  /-- Implemented ProcBody variants (matches inductive constructor names). -/
  procBodyForms : Array String
  /-- Implemented AbstractOp variants. -/
  abstractOps   : Array String
  /-- Implemented Node types. -/
  nodeTypes     : Array String
  /-- Known partial implementations or hard limitations.
      Each entry is "key: prose" — agents split on ": " to extract the key. -/
  limitations   : Array String

-- ---------------------------------------------------------------------------
-- JSON renderer
-- ---------------------------------------------------------------------------

private def jsonStrArray (xs : Array String) : String :=
  let elems := xs.toList.map fun s => "\"" ++ s ++ "\""
  "[" ++ String.intercalate "," elems ++ "]"

/-- Render a CapabilityRecord as a single-line JSON object. -/
def CapabilityRecord.toJson (r : CapabilityRecord) : String :=
  "{\"schemaVersion\":" ++ toString r.schemaVersion ++
  ",\"target\":\"" ++ r.target ++ "\"" ++
  ",\"procBodyForms\":" ++ jsonStrArray r.procBodyForms ++
  ",\"abstractOps\":"   ++ jsonStrArray r.abstractOps ++
  ",\"nodeTypes\":"     ++ jsonStrArray r.nodeTypes ++
  ",\"limitations\":"   ++ jsonStrArray r.limitations ++
  "}"

end AIL
