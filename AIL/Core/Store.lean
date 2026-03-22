-- AIL.Core.Store
-- Content-addressed node store for AIL.
--
-- A "program" or "module" is a root Hash into this store.
-- There are no files. There is no text. There is no parser.
-- The store is the repository.
--
-- Representation (AIL#26): chaining hash map for O(1) expected lookup +
-- insertion-ordered keys array for deterministic iteration (checkStore walks
-- nodes in dependency order; output ordering must be deterministic).
-- The public interface (lookup / insert / empty / contains / hashes) is stable.
-- No external package dependency: the hash map is implemented inline.

import AIL.Core.Hash
import AIL.Core.AST

namespace AIL

-- ---------------------------------------------------------------------------
-- StoreMap: simple chaining hash map  (AIL#26)
--
-- Fixed bucket count (power of 2); each bucket is a List (Hash × Node).
-- Expected O(1) lookup and insert.  No resizing needed for bootstrap scale.
-- ---------------------------------------------------------------------------

private def storeMapBuckets : Nat := 1024  -- must be a power of 2
private def storeMapMask    : UInt64 := 1023

private def emptyBuckets : Array (List (Hash × Node)) :=
  (List.replicate storeMapBuckets []).toArray

/-- Internal chaining hash map for Store. -/
private structure StoreMap where
  buckets : Array (List (Hash × Node))
  size    : Nat

private def StoreMap.empty : StoreMap := { buckets := emptyBuckets, size := 0 }

private def StoreMap.bucketIdx (h : Hash) : Nat :=
  (h &&& storeMapMask).toNat

private def StoreMap.find? (m : StoreMap) (h : Hash) : Option Node :=
  let bucket := m.buckets[StoreMap.bucketIdx h]!
  bucket.findSome? fun (k, v) => if k == h then some v else none

private def StoreMap.contains (m : StoreMap) (h : Hash) : Bool :=
  (m.find? h).isSome

private def StoreMap.insert (m : StoreMap) (h : Hash) (n : Node) : StoreMap :=
  let idx := StoreMap.bucketIdx h
  let bucket := m.buckets[idx]!
  -- Update existing entry if present; otherwise prepend a new one.
  let (newBucket, wasNew) :=
    if bucket.any (·.1 == h) then
      (bucket.map fun (k, v) => if k == h then (k, n) else (k, v), false)
    else
      ((h, n) :: bucket, true)
  { buckets := m.buckets.set! idx newBucket
    size    := if wasNew then m.size + 1 else m.size }

-- ---------------------------------------------------------------------------
-- Store: public API
-- ---------------------------------------------------------------------------

/-- The content-addressed node store.
    O(1) expected lookup via StoreMap; insertion-ordered keys for deterministic
    iteration (checkStore, readClearsWarnings, etc.).  (AIL#26) -/
structure Store where
  /-- O(1) expected hash → node lookup. -/
  hmap : StoreMap
  /-- Insertion-ordered hashes for deterministic foldl/mapM. -/
  keys : Array Hash

namespace Store

def empty : Store := { hmap := StoreMap.empty, keys := #[] }

/-- Look up a node by its hash. O(1) expected. -/
def lookup (s : Store) (h : Hash) : Option Node :=
  s.hmap.find? h

/-- Insert a node with its hash.
    Duplicate inserts update the value; the key is not added to the keys array
    again (first-insertion order is preserved). -/
def insert (s : Store) (h : Hash) (n : Node) : Store :=
  if s.hmap.contains h then
    { s with hmap := s.hmap.insert h n }
  else
    { hmap := s.hmap.insert h n, keys := s.keys.push h }

/-- Check whether a hash is present. O(1) expected. -/
def contains (s : Store) (h : Hash) : Bool :=
  s.hmap.contains h

/-- All hashes in insertion order. -/
def hashes (s : Store) : Array Hash := s.keys

/-- Number of nodes in the store. -/
def size (s : Store) : Nat := s.keys.size

/-- Convert to insertion-ordered (hash, node) pairs for iteration. -/
def toArray (s : Store) : Array (Hash × Node) :=
  s.keys.filterMap fun h => s.hmap.find? h |>.map (h, ·)

end Store

/-- Coerce Store to Array (Hash × Node) for iteration.
    Existing call sites using `(s : Array (Hash × Node))` work unchanged. -/
instance : Coe Store (Array (Hash × Node)) := ⟨Store.toArray⟩

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

/-- Insert a well-known no-op proc (empty seq) into the store.
    Useful as a placeholder branch, default else-arm, or spin-wait body stub.
    The label "nop" is excluded from identity, so all nop nodes share one hash. -/
def nop : StoreM Hash :=
  node (.proc #[] #[] (.seq #[]) "nop")

/-- Run the builder starting from Store.empty. Returns (result, store). -/
def run (m : StoreM α) : α × Store :=
  let (result, s) := StateT.run m { store := Store.empty, nextUid := 0 }
  (result, s.store)

/-- Run the builder starting from an existing store. Returns (result, store). -/
def runFrom (s : Store) (m : StoreM α) : α × Store :=
  let (result, s') := StateT.run m { store := s, nextUid := 0 }
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
