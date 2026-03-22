-- AIL.Core.StaticAlloc
-- Static RAM allocator: assigns addresses to named static declarations.
--
-- Implements R6.2 (unique formal UIDs — agent names, compiler assigns) and
-- R6.3 (static name → address — agent declares, linker assigns).
--
-- The agent writes a list of StaticDecl values (name + type, no address).
-- allocateStatics assigns contiguous addresses starting at a configurable
-- base address and checks the total against the target's RAM budget.
-- The resulting RamMap is passed to library builders and Store constructors.
--
-- BOOTSTRAP NOTE: This is a flat allocator — no bank-switching awareness,
-- no alignment padding for multi-byte types, no BSR management.
-- Bank boundary enforcement is a future enhancement (see AIL#19).

import AIL.Core.AST

namespace AIL

-- ---------------------------------------------------------------------------
-- Width helpers
-- ---------------------------------------------------------------------------

/-- Width in bytes of a Width variant (for allocation size calculations). -/
def widthBytes : Width → UInt32
  | .w8  => 1
  | .w16 => 2
  | .w32 => 4

-- ---------------------------------------------------------------------------
-- Static declaration
-- ---------------------------------------------------------------------------

/-- A static RAM declaration. The agent specifies name and size;
    the allocator assigns an address at link time. -/
structure StaticDecl where
  name  : String    -- agent-assigned name (metadata only)
  width : Width     -- element bit width
  count : UInt32    -- 1 for scalar, >1 for static array

/-- Total byte footprint of a StaticDecl. -/
def StaticDecl.bytes (d : StaticDecl) : UInt32 :=
  widthBytes d.width * d.count

-- ---------------------------------------------------------------------------
-- RAM map (allocation result)
-- ---------------------------------------------------------------------------

/-- One entry in the allocation map: name, base address, size in bytes. -/
structure RamEntry where
  name  : String
  addr  : UInt32
  bytes : UInt32

/-- The result of static RAM allocation: an ordered table of name → address.
    The table is in declaration order, matching the input StaticDecl array. -/
structure RamMap where
  entries : Array RamEntry
deriving Inhabited

namespace RamMap

def empty : RamMap := { entries := #[] }

/-- Look up the address assigned to a named static declaration. -/
def addr (m : RamMap) (name : String) : Option UInt32 :=
  m.entries.findSome? fun e => if e.name == name then some e.addr else none

/-- Look up address, panicking with a descriptive error if not found.
    Use only when the caller has verified the name is present in the map. -/
def addr! (m : RamMap) (name : String) : UInt32 :=
  match m.addr name with
  | some a => a
  | none   => panic! s!"StaticAlloc: '{name}' not found in RamMap"

/-- Total bytes consumed by this allocation. -/
def totalBytes (m : RamMap) : UInt32 :=
  m.entries.foldl (fun acc e => acc + e.bytes) 0

end RamMap

-- ---------------------------------------------------------------------------
-- Hex formatting helper
-- ---------------------------------------------------------------------------

-- Hex digit characters in order 0–15.
private def hexChars : Array Char :=
  #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']

-- Build hex digits big-endian using fuel-based recursion (structurally terminating).
-- fuel = 20 covers any UInt64 (max 16 hex digits) with margin.
private def hexGo : Nat → Nat → List Char → List Char
  | 0,        _,  acc => acc
  | _,        0,  acc => acc
  | fuel + 1, n,  acc => hexGo fuel (n / 16) (hexChars[n % 16]! :: acc)

private def natToHex (n : Nat) : String :=
  if n == 0 then "0x0"
  else "0x" ++ String.ofList (hexGo 20 n [])

-- ---------------------------------------------------------------------------
-- Allocator
-- ---------------------------------------------------------------------------

/-- Assign contiguous addresses to a list of static declarations.
    Packs declarations sequentially starting at baseAddr (no alignment padding
    — all declarations are byte-addressable on PIC18).
    ramBytes: total bytes available in the target RAM region starting at baseAddr.
    Returns (RamMap, nextFreeAddr) or .error "RamBudgetExceeded: ..." if the
    total allocation exceeds ramBytes. -/
def allocateStatics
    (decls    : Array StaticDecl)
    (baseAddr : UInt32)
    (ramBytes : UInt32)
    : Except String (RamMap × UInt32) :=
  let (entries, nextAddr) := decls.foldl
    (fun (acc, ptr) decl =>
      let sz := StaticDecl.bytes decl
      (acc.push { name := decl.name, addr := ptr, bytes := sz }, ptr + sz))
    (#[], baseAddr)
  let used := nextAddr - baseAddr
  if used > ramBytes then
    .error s!"RamBudgetExceeded: need {used} bytes but only {ramBytes} available \
              at {natToHex baseAddr.toNat}"
  else
    .ok ({ entries }, nextAddr)

-- ---------------------------------------------------------------------------
-- Map file renderer
-- ---------------------------------------------------------------------------

/-- Render a RAM map as assembly comments for a human- or agent-readable
    map file. Each line: "; 0x<addr>  <name>  (<size> byte[s])". -/
def RamMap.renderMapFile (m : RamMap) : Array String :=
  m.entries.map fun e =>
    let sz  := e.bytes
    s!"; {natToHex e.addr.toNat}  {e.name}  ({sz} byte{if sz == 1 then "" else "s"})"

end AIL
