-- AIL: AI-native language for embedded systems
-- Bootstrapped in Lean 4
-- See CLAUDE.md for project context and design philosophy

-- Core modules
import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store
import AIL.Core.Diagnostic
import AIL.Core.Types
import AIL.Core.StaticAlloc
import AIL.Core.Capability

-- Analysis passes
import AIL.Analysis.FSRCheck

-- Standard library
import AIL.Lib.PIC18.RingBuf
import AIL.Lib.PIC18.INTCON

-- Targets (stubs — see docs/TIERS.md for tier discipline)
import AIL.Targets.PIC18.ISA
import AIL.Targets.PIC18.Emitter
import AIL.Targets.PIC18.Capabilities
