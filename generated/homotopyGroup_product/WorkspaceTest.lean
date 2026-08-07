/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

import Lean

open Lean

private def trustedPath (path : String) (workspace : System.FilePath) : String :=
  let root := workspace.toString
  String.intercalate ":" <| (path.splitOn ":").filter fun entry =>
    !entry.isEmpty && entry.startsWith "/" &&
      entry != root && !entry.startsWith (root ++ "/")

private def resolveTrustedExecutable
    (path : String) (workspace : System.FilePath) (name : String) : IO String := do
  let output ← IO.Process.output {
    cmd := "/usr/bin/which"
    args := #[name]
    env := #[("PATH", some path)]
  }
  let resolved := output.stdout.trimAscii.toString
  if output.exitCode != 0 || !resolved.startsWith "/" then
    throw <| IO.userError s!"Could not resolve trusted executable `{name}`."
  let root := workspace.toString
  if resolved == root || resolved.startsWith (root ++ "/") then
    throw <| IO.userError s!"Refusing workspace-owned executable `{resolved}`."
  unless ← (resolved : System.FilePath).pathExists do
    throw <| IO.userError s!"Resolved executable does not exist: {resolved}"
  return resolved

private def resolveLeanToolchain
    (path : String) (workspace : System.FilePath) : IO (String × String) := do
  -- Resolve elan before entering the syscall-filtered service, then invoke the
  -- real toolchain binaries there. The elan proxy may perform network probes.
  let leanLauncher ← resolveTrustedExecutable path workspace "lean"
  let output ← IO.Process.output {
    cmd := leanLauncher
    args := #["--print-prefix"]
    env := #[ ("PATH", some path) ]
  }
  let toolchainPrefix := output.stdout.trimAscii.toString
  if output.exitCode != 0 || !toolchainPrefix.startsWith "/" then
    throw <| IO.userError "Could not resolve the active Lean toolchain prefix."
  let leanBin := (toolchainPrefix : System.FilePath) / "bin" / "lean"
  let lakeBin := (toolchainPrefix : System.FilePath) / "bin" / "lake"
  let root := workspace.toString
  for executable in #[leanBin, lakeBin] do
    let resolved := executable.toString
    if resolved == root || resolved.startsWith (root ++ "/") then
      throw <| IO.userError s!"Refusing workspace-owned executable `{resolved}`."
    unless ← executable.pathExists do
      throw <| IO.userError s!"Resolved executable does not exist: {resolved}"
  return (leanBin.toString, lakeBin.toString)

/-- Prime only the benchmark-owned challenge before entering landrun. Lake
4.32 may create replay hashes beside cached dependency artifacts; doing this
trusted target first lets the comparator keep every dependency read-only while
candidate-controlled `Submission` remains completely unelaborated. -/
private def primeTrustedChallenge
    (lakeBin : String) (workspace : System.FilePath) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := lakeBin
    args := #["build", "Challenge"]
    cwd := workspace
    env := #[("UV_USE_IO_URING", some "0")]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"Trusted Challenge priming failed with exit code {exitCode}."

/-- Invoke comparator on this workspace, forcing the external nanoda kernel on.

nanoda is a global requirement of the eval, not a per-problem option: every
solution must be accepted by comparator **and** replayed through nanoda's
independent kernel. Rather than encode that in each workspace's `config.json`,
this harness reads the committed config, overrides `enable_nanoda := true`, and
hands the result to comparator — so nanoda runs regardless of what the file on
disk says. This mirrors the comparator-live "gold standard" setup, which forces
nanoda at the invocation site and leaves project configs untouched. -/
def main : IO UInt32 := do
  try
    let some path ← IO.getEnv "PATH"
      | throw <| IO.userError "PATH is unset; refusing to start comparator."
    let some home ← IO.getEnv "HOME"
      | throw <| IO.userError "HOME is unset; refusing to start comparator."
    let workspace ← IO.currentDir
    let path := trustedPath path workspace
    if path.isEmpty then
      throw <| IO.userError "No trusted executable directories remain on PATH."
    let comparatorBin ← resolveTrustedExecutable path workspace
      ((← IO.getEnv "COMPARATOR_BIN").getD "comparator")
    let landrunBin ← resolveTrustedExecutable path workspace "landrun"
    let lean4exportBin ← resolveTrustedExecutable path workspace "lean4export"
    let nanodaBin ← resolveTrustedExecutable path workspace "nanoda_bin"
    let (leanBin, lakeBin) ← resolveLeanToolchain path workspace
    let gitBin ← resolveTrustedExecutable path workspace "git"
    let systemdRunBin ← resolveTrustedExecutable path workspace "systemd-run"
    primeTrustedChallenge lakeBin workspace
    let configText ← IO.FS.readFile "config.json"
    let config ← IO.ofExcept (Json.parse configText)
    let config := config.setObjVal! "enable_nanoda" (Json.bool true)
    IO.FS.withTempFile fun handle enforcedPath => do
      handle.putStr config.pretty
      handle.flush
      -- `PrivateUsers=yes` remaps the service user. Make the random config
      -- readable in that namespace; it remains immutable to the service.
      IO.setAccessRights enforcedPath {
        user := { read := true }
        group := { read := true }
        other := { read := true }
      }
      IO.FS.withTempFile fun statusHandle statusPath => do
        statusHandle.putStr "starting"
        statusHandle.flush
        -- The remapped comparator must update this random, out-of-workspace
        -- marker. Candidate children cannot: landrun mounts `/` read-only and
        -- `COMPARATOR_STATUS_FILE` is deliberately absent from `envPass`.
        IO.setAccessRights statusPath {
          user := { read := true, write := true }
          group := { read := true, write := true }
          other := { read := true, write := true }
        }
        let child ← IO.Process.spawn {
          cmd := systemdRunBin
          args := #[
            "--user", "--pipe", "--wait", "--collect", "--quiet",
            "--property=RestrictAddressFamilies=~AF_UNIX",
            "--property=SystemCallArchitectures=native",
            "--property=SystemCallFilter=~@network-io @aio",
            "--property=PrivateUsers=yes", "--property=ProtectProc=invisible",
            "--property=ProcSubset=pid", "--property=NoNewPrivileges=yes",
            "--property=KillMode=control-group",
            "--property=MemoryMax=12G", "--property=TasksMax=512",
            "--property=LimitNOFILE=4096", "--property=LimitFSIZE=1G",
            "--property=RuntimeMaxSec=20min",
            s!"--working-directory={workspace}", "--", "/usr/bin/env", "-i",
            s!"PATH={path}", s!"HOME={home}", "LANG=C.UTF-8", "LC_ALL=C.UTF-8",
            "LEAN_ABORT_ON_PANIC=1", "UV_USE_IO_URING=0",
            s!"COMPARATOR_LANDRUN={landrunBin}",
            s!"COMPARATOR_LEAN4EXPORT={lean4exportBin}",
            s!"COMPARATOR_NANODA={nanodaBin}",
            s!"COMPARATOR_LAKE={lakeBin}",
            s!"COMPARATOR_LEAN={leanBin}",
            s!"COMPARATOR_GIT={gitBin}",
            s!"COMPARATOR_STATUS_FILE={statusPath}",
            lakeBin, "env", comparatorBin, enforcedPath.toString]
        }
        let exitCode ← child.wait
        let status := (← IO.FS.readFile statusPath).trimAscii.toString
        IO.eprintln s!"Comparator exited with code {exitCode} at stage `{status}`."
        if exitCode == 0 && status == "accepted" then return 0
        -- Only the patched comparator's explicit, normally returned verdict is
        -- a rejection. A stale progress marker, exception, signal, timeout,
        -- resource kill, or tool failure is an infrastructure error.
        if exitCode == 2 && status == "candidate_rejected" then return 2
        return 1
  catch err =>
    IO.eprintln "Failed to run the hardened comparator."
    IO.eprintln "Make sure `systemd-run`, `comparator`, and the `nanoda_bin` external kernel are installed and on your `PATH`, or set `COMPARATOR_BIN=/path/to/comparator`."
    IO.eprintln "See the root repository README for comparator setup details, including landrun, lean4export, and nanoda."
    IO.eprintln s!"Original error: {err}"
    pure 1
