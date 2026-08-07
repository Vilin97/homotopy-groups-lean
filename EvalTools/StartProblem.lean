/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

import Cli

open Cli

namespace EvalTools

set_option autoImplicit false

/-- Recursively copy a generated workspace to `dst`, following source symlinks
but excluding local build, package, cache, manifest, and VCS artifacts. File
permission bits are not preserved; committed generated contents contain no
executables. -/
private def isGeneratedRuntimeEntry (name : String) : Bool :=
  #[".lake", ".git", ".cache", "build", "lake-manifest.json", ".DS_Store"].contains name

partial def copyTree (src dst : System.FilePath) : IO Unit := do
  -- `FilePath.metadata` follows symlinks, so `.symlink` is unreachable here.
  let info ← src.metadata
  match info.type with
  | .dir =>
      IO.FS.createDirAll dst
      for entry in (← src.readDir) do
        unless isGeneratedRuntimeEntry entry.fileName do
          copyTree entry.path (dst / entry.fileName)
  | .file | .symlink | .other =>
      if let some parent := dst.parent then
        IO.FS.createDirAll parent
      let bytes ← IO.FS.readBinFile src
      IO.FS.writeBinFile dst bytes

/-- Implementation of `lake exe homotopy-groups-lean start-problem`: copy a generated
single-problem workspace to a destination directory so participants have a
clean local starting point.

Both `source` and `destination` accept separate effective and display
representations: the effective `FilePath` is what we read/write, while the
display `String` is what we print, so output text stays as compact as the
Python script's (relative-to-repo-root) output. -/
def runStartProblem
    (sourcePath : System.FilePath) (sourceDisplay : String)
    (destinationPath : System.FilePath) (destinationDisplay : String) :
    IO UInt32 := do
  if !(← sourcePath.isDir) then
    IO.eprintln s!"Problem workspace not found: {sourceDisplay}"
    return 1
  if ← destinationPath.pathExists then
    IO.eprintln s!"Destination already exists: {destinationDisplay}"
    return 1
  if let some parent := destinationPath.parent then
    IO.FS.createDirAll parent
  copyTree sourcePath destinationPath
  IO.println s!"Created workspace: {destinationDisplay}"
  IO.println "Next steps:"
  IO.println s!"  cd {destinationDisplay}"
  IO.println "  lake update"
  IO.println "  lake test"
  return 0

end EvalTools
