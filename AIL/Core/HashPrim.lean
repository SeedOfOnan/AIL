-- AIL.Core.HashPrim
-- Content address primitive: the Hash type and raw byte hasher.
--
-- This module has no imports and is the root of the hash dependency chain:
--   HashPrim  ←  AST  ←  Hash (node serializer)  ←  Store / Types
--
-- BOOTSTRAP NOTE: Hash is UInt64 here for simplicity.
-- Before any real store is used in production, replace with SHA-256 (32 bytes).
-- The Hash type is opaque to all callers; the change is local to this file.

namespace AIL

/-- A content address. Uniquely identifies a node in the store by its content.
    Placeholder: UInt64. Production: SHA-256 (32 bytes). -/
abbrev Hash := UInt64

/-- FNV-1a over a ByteArray. Placeholder hash function.
    Replace with SHA-256 before production store use.
    TODO: prove collision-resistance properties when real hash is in place. -/
def hashBytes (bs : ByteArray) : Hash :=
  bs.foldl (fun acc b => acc * 1099511628211 + b.toUInt64) 14695981039346656037

end AIL
