-- AIL.Core.Store
-- Content-addressed node store for AIL.
--
-- A "program" or "module" is a root Hash into this store.
-- There are no files. There is no text. There is no parser.
-- The store is the repository.
--
-- BOOTSTRAP: Store is Array (Hash × Node) for simplicity.
-- TODO: replace with a proper persistent hash map before scale.
-- The interface (lookup / insert / empty) is stable; the representation is not.

import AIL.Core.Hash
import AIL.Core.AST

namespace AIL

/-- The content-addressed node store.
    Maps Hash → Node. Representation is an opaque implementation detail. -/
abbrev Store := Array (Hash × Node)

namespace Store

def empty : Store := #[]

/-- Look up a node by its hash. Returns none if not present. -/
def lookup (s : Store) (h : Hash) : Option Node :=
  s.findSome? fun (k, v) => if k == h then some v else none

/-- Insert a node with its hash. Last-write-wins on collision.
    NOTE: callers are responsible for computing the correct hash.
    TODO: enforce hash correctness via a proof obligation once
          the real hash function is in place. -/
def insert (s : Store) (h : Hash) (n : Node) : Store :=
  s.push (h, n)

/-- Check whether a hash is present in the store. -/
def contains (s : Store) (h : Hash) : Bool :=
  s.any fun (k, _) => k == h

/-- All hashes currently in the store. -/
def hashes (s : Store) : Array Hash :=
  s.map (·.1)

-- NOTE: use s.size directly for store size; no wrapper needed.

end Store

-- ---------------------------------------------------------------------------
-- StoreM: builder monad for constructing a Store (AIL#18, AIL#31, R6.1–R6.2)
--
-- Eliminates the manual `let h := hashNode n; Store.insert s h n` pairing.
-- The agent names things; the monad computes hashes and threads the store.
-- A UID counter is threaded invisibly so freshFormal never collides (AIL#31).
--
-- Usage:
--   def myBuild : StoreM MyResult := do
--     let h_a ← StoreM.node (.data .data .w8 0x20 "a")
--     let h_b ← StoreM.freshFormal .bool        -- UID auto-assigned
--     return { h_a, h_b }
--   let (result, store) := StoreM.run myBuild
-- ---------------------------------------------------------------------------

/-- Internal state for StoreM: the accumulated store plus a UID counter for
    freshFormal.  The UID counter is invisible to callers; run/runFrom
    still return (result, store) with no change to the external API. -/
private structure StoreMState where
  store   : Store   := Store.empty
  nextUid : UInt64  := 0

/-- Builder monad for constructing a Store.
    `StoreM.node n` hashes n, inserts it into the running store, and returns
    its hash.  `StoreM.freshFormal kind` allocates a new formal node with a
    guaranteed-unique UID drawn from an internal counter (AIL#31).
    The agent names things; the monad computes hashes and UIDs invisibly.
    (AIL R6.1, R6.2) -/
abbrev StoreM := StateM StoreMState

namespace StoreM

/-- Insert a node into the running store, returning its hash. -/
def node (n : Node) : StoreM Hash :=
  let h := hashNode n
  modify (fun s => { s with store := Store.insert s.store h n }) *> pure h

/-- Allocate a fresh formal node with an auto-assigned UID.
    The UID is drawn from the internal counter — callers never manage UIDs.
    Use this in preference to `StoreM.node (.formal <literal_uid> kind)`. -/
def freshFormal (kind : FormalKind) : StoreM Hash := do
  let uid := (← get).nextUid
  modify fun s => { s with nextUid := s.nextUid + 1 }
  node (.formal uid kind)

/-- Run the builder starting from Store.empty. Returns (result, store). -/
def run (m : StoreM α) : α × Store :=
  let (result, s) := StateT.run m {}
  (result, s.store)

/-- Run the builder starting from an existing store. Returns (result, store). -/
def runFrom (s : Store) (m : StoreM α) : α × Store :=
  let (result, s') := StateT.run m { store := s }
  (result, s'.store)

end StoreM

-- ---------------------------------------------------------------------------
-- Named roots
-- A "version" or "program entry point" is a name mapped to a root Hash.
-- Names are metadata: changing a name does not change any node's identity.
-- ---------------------------------------------------------------------------

/-- A named root: maps a human-or-agent-assigned name to a root Hash.
    Renaming never touches the store. Two names may share a hash (aliasing). -/
structure NamedRoot where
  name : String
  hash : Hash
deriving Repr

/-- A name table: the full set of named roots for a repository. -/
abbrev NameTable := Array NamedRoot

namespace NameTable

def empty : NameTable := #[]

def lookup (t : NameTable) (name : String) : Option Hash :=
  t.findSome? fun r => if r.name == name then some r.hash else none

def insert (t : NameTable) (name : String) (h : Hash) : NameTable :=
  t.push { name, hash := h }

end NameTable

end AIL
