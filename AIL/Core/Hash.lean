-- AIL.Core.Hash
-- Node serializer: canonical byte encoding of Node values for content hashing.
--
-- Serialization discipline:
--   - Each node variant is prefixed with a unique tag byte.
--   - Each ProcBody variant is prefixed with a unique tag byte.
--   - Fields marked "excluded from identity" in AST.lean are omitted.
--   - UInt8: 1 byte. UInt32: 4 bytes BE. UInt64: 8 bytes BE. Hash (UInt64): 8 bytes BE.
--   - Array Hash: UInt32 count (BE) followed by each hash (8 bytes BE).
--   - Array String: UInt32 count (BE) followed by each serStr.
--   - String: UInt32 char count (BE) followed by each codepoint as UInt32 BE.
--   - Bool: 0x00 false, 0x01 true.

import AIL.Core.HashPrim
import AIL.Core.AST

namespace AIL

-- ---------------------------------------------------------------------------
-- Primitive serialization helpers
-- ---------------------------------------------------------------------------

private def serU8 (v : UInt8) : ByteArray := ByteArray.mk #[v]

private def serU32 (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
                 UInt8.ofNat (n >>>  8), UInt8.ofNat  n]

private def serU64 (v : UInt64) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[UInt8.ofNat (n >>> 56), UInt8.ofNat (n >>> 48),
                 UInt8.ofNat (n >>> 40), UInt8.ofNat (n >>> 32),
                 UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
                 UInt8.ofNat (n >>>  8), UInt8.ofNat  n]

private def serHash (h : Hash) : ByteArray := serU64 h
private def serBool (b : Bool) : ByteArray := serU8 (if b then 1 else 0)

private def serStr (s : String) : ByteArray :=
  s.foldl (fun acc c => acc ++ serU32 c.val) (serU32 s.length.toUInt32)

private def serHashes (hs : Array Hash) : ByteArray :=
  hs.foldl (fun acc h => acc ++ serHash h) (serU32 hs.size.toUInt32)

private def serU8s (bs : Array UInt8) : ByteArray :=
  bs.foldl (fun acc b => acc ++ serU8 b) (serU32 bs.size.toUInt32)

private def serStrs (ss : Array String) : ByteArray :=
  ss.foldl (fun acc s => acc ++ serStr s) (serU32 ss.size.toUInt32)

-- ---------------------------------------------------------------------------
-- Supporting-type serializers
-- ---------------------------------------------------------------------------

private def serAddrSpace : AddrSpace → ByteArray
  | .data    => serU8 0
  | .program => serU8 1
  | .sfr     => serU8 2

private def serWidth : Width → ByteArray
  | .w8  => serU8 0
  | .w16 => serU8 1
  | .w32 => serU8 2

private def serAccessSemantics (a : AccessSemantics) : ByteArray :=
  serBool a.readable ++ serBool a.writable ++
  serBool a.sideEffectOnRead ++ serBool a.sideEffectOnWrite ++
  serWidth a.accessWidth

private def serRegKind : RegKind → ByteArray
  | .wreg => serU8 0

private def serFlagKind : FlagKind → ByteArray
  | .C  => serU8 0
  | .DC => serU8 1
  | .Z  => serU8 2
  | .OV => serU8 3
  | .N  => serU8 4

private def serFormalKind : FormalKind → ByteArray
  | .data space width => serU8 0 ++ serAddrSpace space ++ serWidth width
  | .bool             => serU8 1
  | .unit             => serU8 2
  | .reg r            => serU8 3 ++ serRegKind r
  | .flag f           => serU8 4 ++ serFlagKind f

private def serAbstractOp : AbstractOp → ByteArray
  | .add         => serU8  0  | .sub         => serU8  1  | .mul         => serU8  2
  | .and         => serU8  3  | .or          => serU8  4  | .xor         => serU8  5
  | .not         => serU8  6  | .shiftL      => serU8  7  | .shiftR      => serU8  8
  | .testBit     => serU8  9  | .load        => serU8 10  | .store       => serU8 11
  | .compare     => serU8 12  | .setBit      => serU8 13  | .clearBit    => serU8 14
  | .loadDiscard => serU8 15  | .indexLoad   => serU8 16  | .indexStore  => serU8 17
  | .xorImm k    => serU8 18 ++ serU8 k
  | .addImm k    => serU8 19 ++ serU8 k
  | .andImm k    => serU8 20 ++ serU8 k
  | .movImm k    => serU8 21 ++ serU8 k
  | .compareImm k => serU8 22 ++ serU8 k

private def serOpRef : OpRef → ByteArray
  | .abstract op => serU8 0 ++ serAbstractOp op
  | .intrinsic h => serU8 1 ++ serHash h

-- ---------------------------------------------------------------------------
-- ProcBody serializer
-- ---------------------------------------------------------------------------

private def serProcBody : ProcBody → ByteArray
  | .atomic ref reads writes =>
      serU8 0x01 ++ serOpRef ref ++ serHashes reads ++ serHashes writes

  | .seq steps =>
      serU8 0x02 ++ serHashes steps

  | .cond test thenB elseB =>
      serU8 0x03 ++ serHash test ++ serHash thenB ++ serHash elseB

  | .loop body =>
      serU8 0x04 ++ serHash body

  | .forever body =>
      serU8 0x08 ++ serHash body

  | .whileLoop cond body =>
      serU8 0x09 ++ serHash cond ++ serHash body

  | .call callee args retBinds callDepth =>
      serU8 0x06 ++ serHash callee ++ serHashes args ++
      serHashes retBinds ++ serU8 callDepth

  | .intrinsic instructions reads writes obligations fsrUse =>
      serU8 0x07 ++ serStrs instructions ++ serHashes reads ++
      serHashes writes ++ serStrs obligations ++ serU8s fsrUse

-- ---------------------------------------------------------------------------
-- Node serializer
-- ---------------------------------------------------------------------------

/-- Canonical byte encoding of a Node value.
    Fields excluded from identity (labels) are omitted. -/
def nodeBytes : Node → ByteArray

  | .data addrSpace width address _label =>
      serU8 0x01 ++ serAddrSpace addrSpace ++ serWidth width ++ serU32 address

  | .peripheral addrSpace address semantics _label =>
      serU8 0x02 ++ serAddrSpace addrSpace ++ serU32 address ++
      serAccessSemantics semantics

  | .formal uid kind =>
      serU8 0x03 ++ serU64 uid ++ serFormalKind kind

  | .staticArray elemSpace elemWidth address count _label =>
      -- label excluded from identity
      serU8 0x06 ++ serAddrSpace elemSpace ++ serWidth elemWidth ++
      serU32 address ++ serU32 count

  | .bitField register bitPos _label =>
      -- label excluded from identity
      serU8 0x05 ++ serHash register ++ serU8 bitPos

  | .proc params rets body _label =>
      -- label excluded from identity; tag 0x04 unchanged (preserves existing hashes)
      serU8 0x04 ++ serHashes params ++ serHashes rets ++ serProcBody body

/-- Content hash of a Node. -/
def hashNode (n : Node) : Hash := hashBytes (nodeBytes n)

/-- Derive an XC8-safe assembly symbol from a node hash.
    Used in both the emitter (EQU declarations) and by node constructors
    that embed symbol references in intrinsic instruction strings. -/
def hashLabel (h : Hash) : String := s!"_n{h}"

end AIL
