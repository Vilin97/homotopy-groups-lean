/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

namespace EvalTools

set_option autoImplicit false

/-- Walk up from `dir` searching for the homotopy-groups-lean repository root, identified
by the presence of both `lakefile.toml` and the `manifests/problems/` directory. -/
partial def findRepoRoot? (dir : System.FilePath) : IO (Option System.FilePath) := do
  let hasLakefile ← (dir / "lakefile.toml").pathExists
  let hasManifest ← (dir / "manifests" / "problems").isDir
  if hasLakefile && hasManifest then
    return some dir
  match dir.parent with
  | none => return none
  | some parent =>
      if parent == dir then
        return none
      findRepoRoot? parent

/-- Return the homotopy-groups-lean repository root, or throw if not found. Looks at the
current working directory and walks upward. -/
def requireRepoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  let some root ← findRepoRoot? cwd
    | throw <| IO.userError
        "Could not find the repository root. Run from this repo or a subdirectory of it."
  pure root

end EvalTools
