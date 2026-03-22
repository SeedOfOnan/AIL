-- AIL.Analysis.FSRCheck
-- FSR resource conflict checker (AIL#13).
--
-- PIC18 has three FSR registers (FSR0, FSR1, FSR2) for indirect addressing.
-- Any ProcBody.intrinsic that uses an FSR declares it in its fsrUse field
-- (0 = FSR0, 1 = FSR1, 2 = FSR2). If an ISR-reachable intrinsic and a
-- main-reachable intrinsic share an FSR, the ISR can corrupt the main code's
-- indirect addressing mid-operation — a silent data-corruption bug.
--
-- This module:
--   1. Walks a Store DAG from a set of root hashes, collecting every
--      ProcBody.intrinsic node and its declared fsrUse.
--   2. Given separate ISR roots and main roots, computes the cross-product
--      of FSR usages and reports every (ISR node, main node, FSR) triple
--      where both sides claim the same FSR.
--
-- Usage (see TestRunner.lean Ex12):
--   let conflicts := FSRCheck.check store isrRoots mainRoots
--   if conflicts.isEmpty then IO.println "No FSR conflicts"
--   else for c in conflicts do IO.println (FSRCheck.renderConflict c)
--
-- Tier 1 (PIC18). The concept generalises to any ISA with shared pointer
-- registers, but the fsrUse annotation is PIC18-specific.

import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store

namespace AIL.FSRCheck

open AIL

-- ---------------------------------------------------------------------------
-- Result types
-- ---------------------------------------------------------------------------

/-- One intrinsic node's FSR annotation, paired with its store hash. -/
structure FSRUseEntry where
  nodeHash : Hash
  fsrUse   : Array UInt8

/-- A detected FSR conflict: ISR-reachable and main-reachable procs share an FSR. -/
structure FSRConflict where
  fsr      : UInt8    -- FSR index: 0 = FSR0, 1 = FSR1, 2 = FSR2
  isrNode  : Hash     -- intrinsic reachable from ISR that claims this FSR
  mainNode : Hash     -- intrinsic reachable from main that claims this FSR
deriving BEq

-- ---------------------------------------------------------------------------
-- DAG walk (mutually recursive: hash lookup ↔ body descent)
-- ---------------------------------------------------------------------------

-- collectFromHash  s h visited  — returns (entries, updated-visited)
-- collectFromBody  s h body visited  — same, where h is the containing proc's hash
--
-- visited tracks already-processed hashes to avoid revisiting shared nodes.
-- partial is required because Lean cannot prove DAG termination without a proof.

mutual

partial def collectFromHash
    (s       : Store)
    (h       : Hash)
    (visited : Array Hash)
    : Array FSRUseEntry × Array Hash :=
  if visited.any (· == h) then (#[], visited)
  else
    let visited' := visited.push h
    match Store.lookup s h with
    | none      => (#[], visited')
    | some node =>
      match node with
      | Node.proc _ _ body _ => collectFromBody s h body visited'
      | _                    => (#[], visited')

partial def collectFromBody
    (s       : Store)
    (h       : Hash)
    (body    : ProcBody)
    (visited : Array Hash)
    : Array FSRUseEntry × Array Hash :=
  match body with
  | ProcBody.intrinsic _ _ _ _ fsrUse =>
      (#[{ nodeHash := h, fsrUse }], visited)
  | ProcBody.seq steps =>
      steps.foldl (fun (acc, vis) step =>
        let (es, vis') := collectFromHash s step vis
        (acc ++ es, vis')) (#[], visited)
  | ProcBody.cond test thenB elseB =>
      let (e1, v1) := collectFromHash s test  visited
      let (e2, v2) := collectFromHash s thenB v1
      let (e3, v3) := collectFromHash s elseB v2
      (e1 ++ e2 ++ e3, v3)
  | ProcBody.forever body' =>
      collectFromHash s body' visited
  | ProcBody.loop body' =>
      collectFromHash s body' visited
  | ProcBody.whileLoop cond body' =>
      let (e1, v1) := collectFromHash s cond   visited
      let (e2, v2) := collectFromHash s body'  v1
      (e1 ++ e2, v2)
  | ProcBody.atomic _ _ _ =>
      (#[], visited)
  | ProcBody.call callee _ _ _ =>
      collectFromHash s callee visited

end

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

/-- Collect all FSRUseEntry reachable from a set of root hashes. -/
def collectFSRUse (s : Store) (roots : Array Hash) : Array FSRUseEntry :=
  roots.foldl (fun (acc, vis) h =>
    let (es, vis') := collectFromHash s h vis
    (acc ++ es, vis')) (#[], #[]) |>.1

/-- Given ISR roots and main roots, find all (isrNode, mainNode, fsr) triples
    where both sides claim the same FSR.  Each unique triple reported once. -/
def check
    (s         : Store)
    (isrRoots  : Array Hash)
    (mainRoots : Array Hash)
    : Array FSRConflict :=
  let isrEntries  := collectFSRUse s isrRoots
  let mainEntries := collectFSRUse s mainRoots
  isrEntries.foldl (fun acc isrE =>
    mainEntries.foldl (fun acc mainE =>
      isrE.fsrUse.foldl (fun acc fsr =>
        if mainE.fsrUse.any (· == fsr) then
          let c : FSRConflict := { fsr, isrNode := isrE.nodeHash, mainNode := mainE.nodeHash }
          if acc.any (· == c) then acc else acc.push c
        else acc) acc) acc) #[]

-- ---------------------------------------------------------------------------
-- Diagnostic rendering
-- ---------------------------------------------------------------------------

/-- Render one FSRConflict as a human-readable (and agent-parseable) string. -/
def renderConflict (c : FSRConflict) : String :=
  s!"FSR{c.fsr} conflict: ISR node {hashLabel c.isrNode} ↔ main node {hashLabel c.mainNode}"

end AIL.FSRCheck
