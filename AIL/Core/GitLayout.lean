-- AIL.Core.GitLayout
-- VCS-friendly file layout for content-addressed stores (AIL#11).
--
-- STRATEGY:
--   Git is already content-addressed (SHA-addressed blobs). AIL nodes are
--   hash-addressed. The models are compatible; the friction is only at the
--   "files in directories" interface layer.
--
--   Conflicts can only happen at the named-root level. Node content is
--   immutable; adding a node is always conflict-free. The only mutable
--   state is the NameTable (name → hash). Two branches conflict only if
--   they both renamed the same entry point to a different hash.
--
-- LAYOUT:
--
--   <repo>/
--     store/
--       <XX>/           -- 2-char hex prefix (256 directories, like git objects)
--         <YYYYYYYYYYYYYY>  -- remaining 14 hex chars; payload = serializeNode(n)
--     roots             -- name→hash index; one line per root (mutable)
--
--   `git diff -- roots` shows semantic changes.
--   Node files are immutable; `git gc` handles unreachable-node cleanup.
--
-- ROOTS FILE FORMAT:
--   Lines: "<name> <decimal-hash>"
--   Lines starting with '#' or empty lines are ignored (comments / blanks).
--   The decimal encoding matches hashLabel (_n<decimal>) for cross-referencing.
--
-- LONG-TERM (SPECULATIVE / Tier 3):
--   A "commit" is itself a hash of (parent_commit_hash, roots_snapshot).
--   The entire history lives in the same content-addressed store. No external
--   VCS needed — the store IS the repository. The current git layout is a
--   stepping stone toward this model, not a dead end.
--
-- TIER: Core (tier-neutral). Uses only AIL.Core.Serialize.

import AIL.Core.Serialize

namespace AIL.GitLayout

open AIL

-- ---------------------------------------------------------------------------
-- Hash ↔ hex string  (public for testing)
-- ---------------------------------------------------------------------------

/-- Render a Hash as a 16-character lowercase hex string. -/
def hashToHex (h : Hash) : String :=
  let hexDigits := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let n := h.toNat
  String.ofList <| (List.range 16).map fun i =>
    hexDigits[(n >>> ((15 - i) * 4)) &&& 0xf]!

/-- Parse a 16-character lowercase hex string to a Hash.
    Returns none if the string is not exactly 16 valid hex digits. -/
def hexToHash (s : String) : Option Hash :=
  if s.length != 16 then none
  else
    s.toList.foldlM (fun (acc : UInt64) c =>
      let nibble : Option UInt64 := match c with
        | '0' => some 0  | '1' => some 1  | '2' => some 2  | '3' => some 3
        | '4' => some 4  | '5' => some 5  | '6' => some 6  | '7' => some 7
        | '8' => some 8  | '9' => some 9  | 'a' => some 10 | 'b' => some 11
        | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
        | _   => none
      nibble.map fun v => (acc <<< 4) ||| v) (0 : UInt64)

-- ---------------------------------------------------------------------------
-- Roots file format  (public for testing)
-- ---------------------------------------------------------------------------

/-- Render a NameTable as the text content of a roots file. -/
def renderRootsFile (nt : NameTable) : String :=
  let header := "# AIL roots (name decimal-hash)\n"
  nt.foldl (fun acc r => acc ++ r.name ++ " " ++ toString r.hash ++ "\n") header

/-- Parse the text content of a roots file into a NameTable. -/
def parseRootsFile (s : String) : Except String NameTable :=
  -- Normalise CRLF → LF before splitting.
  (s.replace "\r\n" "\n").splitOn "\n" |>.foldlM (fun nt line =>
    if line.isEmpty || line.startsWith "#" then .ok nt
    else
      match line.splitOn " " with
      | [name, hashStr] =>
          match hashStr.toNat? with
          | some n => .ok (NameTable.insert nt name n.toUInt64)
          | none   => .error s!"invalid hash in roots file: '{hashStr}'"
      | _ => .error s!"invalid roots file line: '{line}'"
  ) NameTable.empty

-- ---------------------------------------------------------------------------
-- File path helpers  (private)
-- ---------------------------------------------------------------------------

-- Split a 16-char hex string into (first-2, rest-14).
-- String.take/drop return Slice in this Lean 4 nightly; use toList/ofList.
private def hexSplit (s : String) : String × String :=
  let cs := s.toList
  (String.ofList (cs.take 2), String.ofList (cs.drop 2))

-- Node file: <base>/store/<hex2>/<hex14>
private def nodeFilePath (base : System.FilePath) (h : Hash) :
    System.FilePath × System.FilePath :=
  let hex          := hashToHex h
  let (pfx, rest)  := hexSplit hex
  let dir          := base / "store" / pfx
  let file         := dir / rest
  (dir, file)

-- ---------------------------------------------------------------------------
-- Write layout
-- ---------------------------------------------------------------------------

/-- Write a Store and NameTable to the git-friendly file layout.
    Creates store/<XX>/<YYYYYY...> node files and a roots file.
    Existing node files are silently overwritten (content is identical
    for a given hash, so this is always safe). -/
def writeLayout (base : System.FilePath) (s : Store) (nt : NameTable) : IO Unit := do
  IO.FS.createDirAll (base / "store")
  for (h, n) in (s : Array (Hash × Node)) do
    let (dir, file) := nodeFilePath base h
    IO.FS.createDirAll dir
    IO.FS.writeBinFile file (Store.serializeNode n)
  IO.FS.writeFile (base / "roots") (renderRootsFile nt)

-- ---------------------------------------------------------------------------
-- Read layout
-- ---------------------------------------------------------------------------

/-- Read a Store and NameTable back from the git-friendly file layout.
    Verifies hash consistency for every node file.
    Returns Except.error on any malformed or corrupted entry. -/
def readLayout (base : System.FilePath) : IO (Except String (Store × NameTable)) := do
  -- Walk store/<XX>/<YYYYYY...>
  let storeDir := base / "store"
  let prefixEntries ← storeDir.readDir
  let mut store := Store.empty
  for pfxEntry in prefixEntries do
    if pfxEntry.fileName.length != 2 then continue   -- skip non-prefix entries
    let nodeEntries ← pfxEntry.path.readDir
    for nodeEntry in nodeEntries do
      let hexStr := pfxEntry.fileName ++ nodeEntry.fileName
      match hexToHash hexStr with
      | none    => return .error s!"invalid hash in path: '{hexStr}'"
      | some h  =>
          let payload ← IO.FS.readBinFile nodeEntry.path
          match Store.deserializeNode payload with
          | .error msg => return .error s!"error reading node {hexStr}: {msg}"
          | .ok node   =>
              if hashNode node != h then
                return .error
                  s!"hash mismatch: path '{hexStr}', computed '{hashToHex (hashNode node)}'"
              store := Store.insert store h node
  -- Read roots file (optional — a store without a roots file has an empty NameTable)
  let rootsPath := base / "roots"
  let nt ← try
    let contents ← IO.FS.readFile rootsPath
    match parseRootsFile contents with
    | .ok nt     => pure nt
    | .error msg => return .error s!"error parsing roots file: {msg}"
  catch _ =>
    pure NameTable.empty
  return .ok (store, nt)

end AIL.GitLayout
