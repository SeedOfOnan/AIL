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
