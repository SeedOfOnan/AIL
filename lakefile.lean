import Lake
open Lake DSL

package "AIL" where
  -- AIL: placeholder name for an AI-native language targeting embedded systems
  -- Bootstrapping vehicle: Lean 4 / Lake
  -- See CLAUDE.md for full project context before modifying anything

@[default_target]
lean_lib AIL

lean_exe ailc where
  root := `Main

lean_exe ailtest where
  root := `TestRunner
