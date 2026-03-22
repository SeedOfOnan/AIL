-- AIL.Core.Serialize
-- Canonical binary serialization for Store and NameTable (AIL#10).
--
-- Requirements: round-trip, stable encoding, streamable.
--
-- FILE FORMAT:
--   magic:       4 bytes  (0x41 0x49 0x4C 0x01 = "AIL\x01")
--   node_count:  UInt32 BE
--   nodes:       node_count records, each:
--                  stored_hash:  8 bytes
--                  payload_len:  UInt32 BE (byte count of payload)
--                  payload:      full node encoding including label
--   roots_count: UInt32 BE
--   roots:       roots_count records, each:
--                  hash:  8 bytes
--                  name:  serStr (UInt32 char count + UTF-32 codepoints BE)
--
-- STABILITY:
--   The payload encodes the full node (identity fields + label).
--   Identity fields are encoded identically to nodeBytes in Hash.lean, so
--   hashNode(reconstructed_node) == stored_hash is verifiable on load.
--   The encoding of each node is uniquely determined by its content and never
--   changes — same bytes produce the same hash.
--
-- ENCODING PRIMITIVES (mirrors Hash.lean; private, same byte layout):
--   UInt8:  1 byte.  UInt32: 4 bytes BE.  UInt64/Hash: 8 bytes BE.
--   Bool:   0x00 false, 0x01 true.
--   String: UInt32 char count (BE) + each codepoint as UInt32 BE.
--   Array T: UInt32 count (BE) + each element serialized.

import AIL.Core.Store

namespace AIL

-- ============================================================================
-- Serialization primitives (identical to private helpers in Hash.lean)
-- ============================================================================

private def serU8S (v : UInt8) : ByteArray := ByteArray.mk #[v]

private def serU32S (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
                 UInt8.ofNat (n >>>  8), UInt8.ofNat  n]

private def serU64S (v : UInt64) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[UInt8.ofNat (n >>> 56), UInt8.ofNat (n >>> 48),
                 UInt8.ofNat (n >>> 40), UInt8.ofNat (n >>> 32),
                 UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
                 UInt8.ofNat (n >>>  8), UInt8.ofNat  n]

private def serHashS (h : Hash) : ByteArray := serU64S h
private def serBoolS (b : Bool) : ByteArray := serU8S (if b then 1 else 0)

private def serStrS (s : String) : ByteArray :=
  s.foldl (fun acc c => acc ++ serU32S c.val) (serU32S s.length.toUInt32)

private def serHashesS (hs : Array Hash) : ByteArray :=
  hs.foldl (fun acc h => acc ++ serHashS h) (serU32S hs.size.toUInt32)

private def serU8sS (bs : Array UInt8) : ByteArray :=
  bs.foldl (fun acc b => acc ++ serU8S b) (serU32S bs.size.toUInt32)

private def serStrsS (ss : Array String) : ByteArray :=
  ss.foldl (fun acc s => acc ++ serStrS s) (serU32S ss.size.toUInt32)

private def serAddrSpaceS : AddrSpace → ByteArray
  | .data    => serU8S 0
  | .program => serU8S 1
  | .sfr     => serU8S 2

private def serWidthS : Width → ByteArray
  | .w8  => serU8S 0
  | .w16 => serU8S 1
  | .w32 => serU8S 2

private def serAccessSemanticsS (a : AccessSemantics) : ByteArray :=
  serBoolS a.readable ++ serBoolS a.writable ++
  serBoolS a.sideEffectOnRead ++ serBoolS a.sideEffectOnWrite ++
  serWidthS a.accessWidth

private def serRegKindS : RegKind → ByteArray
  | .wreg => serU8S 0

private def serFormalKindS : FormalKind → ByteArray
  | .data space width => serU8S 0 ++ serAddrSpaceS space ++ serWidthS width
  | .bool             => serU8S 1
  | .unit             => serU8S 2
  | .reg r            => serU8S 3 ++ serRegKindS r

private def serAbstractOpS : AbstractOp → ByteArray
  | .add         => serU8S  0  | .sub         => serU8S  1  | .mul         => serU8S  2
  | .and         => serU8S  3  | .or          => serU8S  4  | .xor         => serU8S  5
  | .not         => serU8S  6  | .shiftL      => serU8S  7  | .shiftR      => serU8S  8
  | .testBit     => serU8S  9  | .load        => serU8S 10  | .store       => serU8S 11
  | .compare     => serU8S 12  | .setBit      => serU8S 13  | .clearBit    => serU8S 14
  | .loadDiscard => serU8S 15  | .indexLoad   => serU8S 16  | .indexStore  => serU8S 17
  | .xorImm k   => serU8S 18 ++ serU8S k
  | .addImm k   => serU8S 19 ++ serU8S k
  | .andImm k   => serU8S 20 ++ serU8S k
  | .movImm k   => serU8S 21 ++ serU8S k

private def serOpRefS : OpRef → ByteArray
  | .abstract op => serU8S 0 ++ serAbstractOpS op
  | .intrinsic h => serU8S 1 ++ serHashS h

-- ProcBody encoding: identical to serProcBody in Hash.lean (same tag bytes).
private def serProcBodyS : ProcBody → ByteArray
  | .atomic ref reads writes =>
      serU8S 0x01 ++ serOpRefS ref ++ serHashesS reads ++ serHashesS writes
  | .seq steps =>
      serU8S 0x02 ++ serHashesS steps
  | .cond test thenB elseB =>
      serU8S 0x03 ++ serHashS test ++ serHashS thenB ++ serHashS elseB
  | .loop body =>
      serU8S 0x04 ++ serHashS body
  | .forever body =>
      serU8S 0x08 ++ serHashS body
  | .whileLoop cond body =>
      serU8S 0x09 ++ serHashS cond ++ serHashS body
  | .call callee args retBinds callDepth =>
      serU8S 0x06 ++ serHashS callee ++ serHashesS args ++
      serHashesS retBinds ++ serU8S callDepth
  | .intrinsic instructions reads writes obligations fsrUse =>
      serU8S 0x07 ++ serStrsS instructions ++ serHashesS reads ++
      serHashesS writes ++ serStrsS obligations ++ serU8sS fsrUse

-- Full node encoding: identity fields (same order as nodeBytes) + label.
-- Tags match nodeBytes tags so decoders can cross-verify with the stored hash.
private def serNodeFull : Node → ByteArray
  | .data space w addr lbl =>
      serU8S 0x01 ++ serAddrSpaceS space ++ serWidthS w ++ serU32S addr ++ serStrS lbl
  | .peripheral space addr sem lbl =>
      serU8S 0x02 ++ serAddrSpaceS space ++ serU32S addr ++ serAccessSemanticsS sem ++ serStrS lbl
  | .formal uid kind =>
      serU8S 0x03 ++ serU64S uid ++ serFormalKindS kind
  | .proc params rets body lbl =>
      serU8S 0x04 ++ serHashesS params ++ serHashesS rets ++ serProcBodyS body ++ serStrS lbl
  | .bitField reg bitPos lbl =>
      serU8S 0x05 ++ serHashS reg ++ serU8S bitPos ++ serStrS lbl
  | .staticArray space w addr count lbl =>
      serU8S 0x06 ++ serAddrSpaceS space ++ serWidthS w ++ serU32S addr ++ serU32S count ++ serStrS lbl

-- ============================================================================
-- Public serializer
-- ============================================================================

private def magicBytes : ByteArray := ByteArray.mk #[0x41, 0x49, 0x4C, 0x01]

/-- Serialize a Store and NameTable to a self-describing byte stream.
    The result can be written to disk, sent over a channel, or stored in VCS.
    Deserialize with Store.ofByteArray. -/
def Store.toByteArray (s : Store) (roots : NameTable := .empty) : ByteArray :=
  let nodeRecords := (s : Array (Hash × Node)).foldl (fun acc (h, n) =>
    let payload := serNodeFull n
    acc ++ serHashS h ++ serU32S payload.size.toUInt32 ++ payload) ByteArray.empty
  let rootRecords := roots.foldl (fun acc r =>
    acc ++ serHashS r.hash ++ serStrS r.name) ByteArray.empty
  magicBytes ++ serU32S s.size.toUInt32 ++ nodeRecords ++
  serU32S roots.size.toUInt32 ++ rootRecords

-- ============================================================================
-- Deserialization
-- ============================================================================

-- Parser monad: state = (ByteArray being parsed, current position).
private abbrev PS    := ByteArray × Nat
private abbrev Parser α := StateT PS (Except String) α

private def readU8 : Parser UInt8 := do
  let (ba, i) ← get
  if i >= ba.size then throw "unexpected end of input"
  set (ba, i + 1)
  return ba[i]!

private def readU32 : Parser UInt32 := do
  let b0 ← readU8; let b1 ← readU8; let b2 ← readU8; let b3 ← readU8
  return (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

private def readU64 : Parser UInt64 := do
  let hi ← readU32; let lo ← readU32
  return (hi.toUInt64 <<< 32) ||| lo.toUInt64

private def readHash : Parser Hash := readU64

private def readStr : Parser String := do
  let len ← readU32
  let chars ← (List.range len.toNat).mapM fun _ => do
    return Char.ofNat (← readU32).toNat
  return String.ofList chars

private def readBool : Parser Bool := do
  return (← readU8) != 0

private def readHashes : Parser (Array Hash) := do
  let n ← readU32
  return (← (List.range n.toNat).mapM fun _ => readHash).toArray

private def readU8sP : Parser (Array UInt8) := do
  let n ← readU32
  return (← (List.range n.toNat).mapM fun _ => readU8).toArray

private def readStrsP : Parser (Array String) := do
  let n ← readU32
  return (← (List.range n.toNat).mapM fun _ => readStr).toArray

private def readAddrSpace : Parser AddrSpace := do
  match ← readU8 with
  | 0 => return .data
  | 1 => return .program
  | 2 => return .sfr
  | t => throw s!"unknown AddrSpace tag {t}"

private def readWidth : Parser Width := do
  match ← readU8 with
  | 0 => return .w8
  | 1 => return .w16
  | 2 => return .w32
  | t => throw s!"unknown Width tag {t}"

private def readAccessSemantics : Parser AccessSemantics := do
  let readable          ← readBool
  let writable          ← readBool
  let sideEffectOnRead  ← readBool
  let sideEffectOnWrite ← readBool
  let accessWidth       ← readWidth
  return { readable, writable, sideEffectOnRead, sideEffectOnWrite, accessWidth }

private def readRegKind : Parser RegKind := do
  match ← readU8 with
  | 0 => return .wreg
  | t => throw s!"unknown RegKind tag {t}"

private def readFormalKind : Parser FormalKind := do
  match ← readU8 with
  | 0 => return .data (← readAddrSpace) (← readWidth)
  | 1 => return .bool
  | 2 => return .unit
  | 3 => return .reg (← readRegKind)
  | t => throw s!"unknown FormalKind tag {t}"

private def readAbstractOp : Parser AbstractOp := do
  match ← readU8 with
  | 0  => return .add    | 1  => return .sub    | 2  => return .mul
  | 3  => return .and    | 4  => return .or     | 5  => return .xor
  | 6  => return .not    | 7  => return .shiftL | 8  => return .shiftR
  | 9  => return .testBit | 10 => return .load   | 11 => return .store
  | 12 => return .compare | 13 => return .setBit | 14 => return .clearBit
  | 15 => return .loadDiscard | 16 => return .indexLoad | 17 => return .indexStore
  | 18 => return .xorImm (← readU8)
  | 19 => return .addImm (← readU8)
  | 20 => return .andImm (← readU8)
  | 21 => return .movImm (← readU8)
  | t  => throw s!"unknown AbstractOp tag {t}"

private def readOpRef : Parser OpRef := do
  match ← readU8 with
  | 0 => return .abstract (← readAbstractOp)
  | 1 => return .intrinsic (← readHash)
  | t => throw s!"unknown OpRef tag {t}"

private def readProcBody : Parser ProcBody := do
  match ← readU8 with
  | 0x01 => return .atomic (← readOpRef) (← readHashes) (← readHashes)
  | 0x02 => return .seq (← readHashes)
  | 0x03 => return .cond (← readHash) (← readHash) (← readHash)
  | 0x04 => return .loop (← readHash)
  | 0x08 => return .forever (← readHash)
  | 0x09 => return .whileLoop (← readHash) (← readHash)
  | 0x06 => return .call (← readHash) (← readHashes) (← readHashes) (← readU8)
  | 0x07 => return .intrinsic (← readStrsP) (← readHashes) (← readHashes) (← readStrsP) (← readU8sP)
  | t    => throw s!"unknown ProcBody tag {t}"

private def readNodeFull : Parser Node := do
  match ← readU8 with
  | 0x01 => return .data (← readAddrSpace) (← readWidth) (← readU32) (← readStr)
  | 0x02 =>
      let space ← readAddrSpace; let addr ← readU32
      let sem ← readAccessSemantics; let lbl ← readStr
      return .peripheral space addr sem lbl
  | 0x03 => return .formal (← readU64) (← readFormalKind)
  | 0x04 =>
      let params ← readHashes; let rets ← readHashes
      let body ← readProcBody; let lbl ← readStr
      return .proc params rets body lbl
  | 0x05 => return .bitField (← readHash) (← readU8) (← readStr)
  | 0x06 =>
      let space ← readAddrSpace; let w ← readWidth
      let addr ← readU32; let count ← readU32; let lbl ← readStr
      return .staticArray space w addr count lbl
  | t   => throw s!"unknown Node tag {t}"

private def runParser (ba : ByteArray) (p : Parser α) : Except String α :=
  match StateT.run p (ba, 0) with
  | .ok (a, _) => .ok a
  | .error e   => .error e

/-- Deserialize a Store and NameTable from bytes produced by Store.toByteArray.
    Verifies magic bytes, payload lengths, and hash consistency.
    Returns Except.error on malformed or truncated input. -/
def Store.ofByteArray (ba : ByteArray) : Except String (Store × NameTable) :=
  runParser ba do
    -- Verify magic
    let m0 ← readU8; let m1 ← readU8; let m2 ← readU8; let m3 ← readU8
    if m0 != 0x41 || m1 != 0x49 || m2 != 0x4C || m3 != 0x01 then
      throw "invalid magic bytes (expected AIL\\x01)"
    -- Read nodes
    let nodeCount ← readU32
    let pairs ← (List.range nodeCount.toNat).mapM fun _ => do
      let storedHash  ← readHash
      let payloadLen  ← readU32
      let posBefore   := (← get).2
      let node        ← readNodeFull
      let consumed    := (← get).2 - posBefore
      if consumed != payloadLen.toNat then
        throw s!"payload length mismatch: expected {payloadLen}, consumed {consumed}"
      let computedHash := hashNode node
      if computedHash != storedHash then
        throw s!"hash mismatch: stored {storedHash}, computed {computedHash}"
      return (storedHash, node)
    let store := pairs.foldl (fun s (h, n) => Store.insert s h n) Store.empty
    -- Read roots
    let rootsCount ← readU32
    let rootList ← (List.range rootsCount.toNat).mapM fun _ => do
      let h    ← readHash
      let name ← readStr
      return NamedRoot.mk name h
    let nt := rootList.foldl (fun t r => NameTable.insert t r.name r.hash) NameTable.empty
    return (store, nt)

-- ---------------------------------------------------------------------------
-- Single-node serialization (for file-per-node storage, AIL#11)
-- ---------------------------------------------------------------------------

/-- Serialize a single Node to bytes.
    Used by the git layout to write one file per node.
    The encoding is the same payload format as in Store.toByteArray. -/
def Store.serializeNode (n : Node) : ByteArray := serNodeFull n

/-- Deserialize a single Node from bytes produced by Store.serializeNode.
    Does NOT verify the hash — the caller is responsible for checking
    hashNode(result) == expected_hash (typically encoded in the file path). -/
def Store.deserializeNode (ba : ByteArray) : Except String Node :=
  runParser ba readNodeFull

end AIL
