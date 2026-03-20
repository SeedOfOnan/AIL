-- AIL: AI-native language for embedded systems
-- Bootstrapped in Lean 4
-- See CLAUDE.md for project context and design philosophy

-- Core modules
import AIL.Core.Hash
import AIL.Core.AST
import AIL.Core.Store
import AIL.Core.Types

-- Standard library
import AIL.Lib.RingBuf

-- Targets (stubs — see docs/TIERS.md for tier discipline)
import AIL.Targets.PIC18.Emitter
